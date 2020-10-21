package technology.tabula.detectors;

import java.awt.geom.Line2D;
import java.awt.geom.Point2D;
import java.awt.image.BufferedImage;
import java.awt.image.Raster;
import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;

import org.apache.pdfbox.contentstream.operator.Operator;
import org.apache.pdfbox.cos.COSName;
import org.apache.pdfbox.pdfparser.PDFStreamParser;
import org.apache.pdfbox.pdfwriter.ContentStreamWriter;
import org.apache.pdfbox.pdmodel.PDDocument;
import org.apache.pdfbox.pdmodel.PDPage;
import org.apache.pdfbox.pdmodel.common.PDStream;
import org.apache.pdfbox.rendering.ImageType;

import technology.tabula.Line;
import technology.tabula.Page;
import technology.tabula.Rectangle;
import technology.tabula.Ruling;
import technology.tabula.TextChunk;
import technology.tabula.TextElement;
import technology.tabula.Utils;
import technology.tabula.extractors.BasicExtractionAlgorithm;
import technology.tabula.extractors.SpreadsheetExtractionAlgorithm;

/**
 * Created by matt on 2015-12-17.
 * <p>
 * Attempt at an implementation of the table finding algorithm described by
 * Anssi Nurminen's master's thesis:
 * https://trepo.tuni.fi/handle/123456789/21520
 */
public class NurminenDetectionAlgorithm implements DetectionAlgorithm {

    private static final int GRAYSCALE_INTENSITY_THRESHOLD = 25;
    private static final int HORIZONTAL_EDGE_WIDTH_MINIMUM = 50;
    private static final int VERTICAL_EDGE_HEIGHT_MINIMUM = 10;
    private static final int CELL_CORNER_DISTANCE_MAXIMUM = 10;
    private static final float POINT_SNAP_DISTANCE_THRESHOLD = 8f;
    private static final float TABLE_PADDING_AMOUNT = 1.0f;
    private static final int REQUIRED_TEXT_LINES_FOR_EDGE = 4;
    private static final int REQUIRED_CELLS_FOR_TABLE = 4;
    private static final float IDENTICAL_TABLE_OVERLAP_RATIO = 0.9f;
    private static final float ROW_HEIGHT_THRESHOLD_MULT_BOTTOM = 1.5f;
    private static final float ROW_HEIGHT_THRESHOLD_MULT_TOP = 2f;
    public List<TextEdge> allLeftTextEdges = new ArrayList<>();
    public List<TextEdge> allMidTextEdges = new ArrayList<>();
    public List<TextEdge> allRightTextEdges = new ArrayList<>();
    private Rectangle textBoundingBox;
    private List<Line> allLines;
    private List<Ruling> horizontalRulings;
    private Page page;

    // create a set of our current tables that will eliminate duplicate tables
    private static final Comparator<Rectangle> TABLE_COMPARATOR = new Comparator<Rectangle>() {
        @Override
        public int compare(Rectangle o1, Rectangle o2) {
            if (o1.equals(o2)) {
                return 0;
            }

            // o1 is "equal" to o2 if o2 contains all of o1
            if (o2.contains(o1)) {
                return 0;
            }

            if (o1.contains(o2)) {
                return 0;
            }

            // otherwise see if these tables are "mostly" the same
            float overlap = o1.overlapRatio(o2);
            if (overlap >= IDENTICAL_TABLE_OVERLAP_RATIO) {
                return 0;
            } else {
                return 1;
            }
        }
    };

    /**
     * Helper class that encapsulates a text edge
     */
    public static final class TextEdge extends Line2D.Float {
        // types of text edges
        public static final int LEFT = 0;
        public static final int MID = 1;
        public static final int RIGHT = 2;
        public static final int SIDE_EDGE = 3;
        public static final int NUM_TYPES = 4;

        /**
         * Number of text element directly in touch with this edge
         */
        public int intersectingTextRowCount;

        public TextEdge(float x1, float y1, float x2, float y2) {
            super(x1, y1, x2, y2);
            this.intersectingTextRowCount = 0;
        }

        public float getYOverlapPercent(TextEdge textEdge) {
            float a = Math.max(y1, textEdge.y1);
            float b = Math.min(y2, textEdge.y2);

            if (a <= b) {
                return (b - a)/Math.max(textEdge.y2 - textEdge.y1, y2 - y1);
            } else {
                return 0.0f;
            }
        }

        public float getWidth() {
          return x2 - x1;
        }

        public float getHeight() {
          return y2 - y1;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            TextEdge textEdge = (TextEdge) o;
            return java.lang.Float.compare(textEdge.x1, x1) == 0 &&
              java.lang.Float.compare(textEdge.y1, y1) == 0 &&
              java.lang.Float.compare(textEdge.x2, x2) == 0 &&
              java.lang.Float.compare(textEdge.y2, y2) == 0 &&
              intersectingTextRowCount == textEdge.intersectingTextRowCount;
        }

        @Override
        public int hashCode() {
            return Objects.hash(x1, y1, x2, y2, intersectingTextRowCount);
        }
    }

    /**
     * Helper container for all text edges on a page
     */
    private static final class TextEdges extends ArrayList<List<TextEdge>> {
        public TextEdges(List<TextEdge> leftEdges, List<TextEdge> midEdges, List<TextEdge> rightEdges) {
            super(3);
            this.add(leftEdges);
            this.add(midEdges);
            this.add(rightEdges);
        }
    }

    /**
     * Helper container for relevant text edge info
     */
    private static final class RelevantEdges {
        public int edgeType;
        public int edgeCount;

        public RelevantEdges(int edgeType, int edgeCount) {
            this.edgeType = edgeType;
            this.edgeCount = edgeCount;
        }
    }

    @Override
    /**
     * 1. Convert to image
     * 3. Find rulings in image
     * 4. Using rulings in image, try to find full spreadsheet tables with cells.
     * 5. Search the rest of space for tables using Nurminen edges
     * 6. Using relevant edge count/type find rows that are relevant
     * 7. Expand the area into top and bottom using horizontal rulings.
     */
    public List<Rectangle> detect(Page page) {
        this.page = page;

        // get horizontal & vertical lines
        // we get these from an image of the PDF and not the PDF itself because sometimes there are invisible PDF
        // instructions that are interpreted incorrectly as visible elements - we really want to capture what a
        // person sees when they look at the PDF
        BufferedImage image;
        PDPage pdfPage = page.getPDPage();
        try {
            image = Utils.pageConvertToImage(page.getPDDoc(), pdfPage, 144, ImageType.GRAY);
        } catch (IOException e) {
            return new ArrayList<>();
        }

        //Utils.save(image, "/tmp/lool");

        horizontalRulings = this.getHorizontalRulings(image);

        // now check the page for vertical lines, but remove the text first to make things less confusing
        PDDocument removeTextDocument = null;
        try {
            removeTextDocument = this.removeText(pdfPage);
            pdfPage = removeTextDocument.getPage(0);
            image = Utils.pageConvertToImage(removeTextDocument, pdfPage, 144, ImageType.GRAY);
        } catch (Exception e) {
            return new ArrayList<>();
        } finally {
            if (removeTextDocument != null) {
                try {
                    removeTextDocument.close();
                } catch (IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }

        List<Ruling> verticalRulings = this.getVerticalRulings(image);

        List<Ruling> allEdges = new ArrayList<>(horizontalRulings);
        allEdges.addAll(verticalRulings);

        List<Rectangle> tableAreas = new ArrayList<>();

        // if we found some edges, try to find some tables based on them
        if (allEdges.size() > 0) {
            // now we need to snap edge endpoints to a grid
            Utils.snapPoints(allEdges, POINT_SNAP_DISTANCE_THRESHOLD, POINT_SNAP_DISTANCE_THRESHOLD);

            // normalize the rulings to make sure snapping didn't create any wacky non-horizontal/vertical rulings
            for (List<Ruling> rulings : Arrays.asList(horizontalRulings, verticalRulings)) {
                for (Iterator<Ruling> iterator = rulings.iterator(); iterator.hasNext(); ) {
                    Ruling ruling = iterator.next();

                    ruling.normalize();
                    if (ruling.oblique()) {
                        iterator.remove();
                    }
                }
            }

            // merge the edge lines into rulings - this makes finding edges between crossing points in the next step easier
            // we use a larger pixel expansion than the normal spreadsheet extraction method to cover gaps in the
            // edge detection/pixel snapping steps
            horizontalRulings = Ruling.collapseOrientedRulings(horizontalRulings, 5);
            verticalRulings = Ruling.collapseOrientedRulings(verticalRulings, 5);

            // use the rulings and points to find cells
            List<? extends Rectangle> cells = SpreadsheetExtractionAlgorithm.findCells(horizontalRulings, verticalRulings);

            // then use those cells to make table areas
            tableAreas = this.getTableAreasFromCells(cells);
        }

        // next find any vertical rulings that intersect tables - sometimes these won't have completely been captured as
        // cells if there are missing horizontal lines (which there often are)
        // let's assume though that these lines should be part of the table
        for (Line2D.Float verticalRuling : verticalRulings) {
            for (Rectangle tableArea : tableAreas) {
                if (verticalRuling.intersects(tableArea) &&
                        !(tableArea.contains(verticalRuling.getP1()) && tableArea.contains(verticalRuling.getP2()))) {

                    tableArea.setTop((float) Math.floor(Math.min(tableArea.getTop(), verticalRuling.getY1())));
                    tableArea.setBottom((float) Math.ceil(Math.max(tableArea.getBottom(), verticalRuling.getY2())));
                    break;
                }
            }
        }

        // the tabula Page coordinate space is half the size of the PDFBox image coordinate space
        // so halve the table area size before proceeding and add a bit of padding to make sure we capture everything
        for (Rectangle area : tableAreas) {
            area.x = area.x / 2 - TABLE_PADDING_AMOUNT;
            area.y = area.y / 2 - TABLE_PADDING_AMOUNT;
            area.width = area.width / 2 + TABLE_PADDING_AMOUNT;
            area.height = area.height / 2 + TABLE_PADDING_AMOUNT + 1;
        }

        // we're going to want halved horizontal lines later too
        for (Line2D.Float ruling : horizontalRulings) {
            ruling.x1 = ruling.x1 / 2;
            ruling.y1 = ruling.y1 / 2;
            ruling.x2 = ruling.x2 / 2;
            ruling.y2 = ruling.y2 / 2;
        }

        // now look at text rows to help us find more tables and flesh out existing ones
        List<TextChunk> textChunks = TextElement.mergeWords(page.getText());

        textBoundingBox = page.getTextBounds();

        // delete long lines of text. They are likely not a part of table.
        // This avoids detecting justified text as tables.
        textChunks.removeIf(textChunk -> textChunk.width > 0.38 * page.getWidth());

        List<Line> lines = TextChunk.groupByLines(textChunks);
        allLines = new ArrayList<>(lines);

        // first look for text rows that intersect an existing table - those lines should probably be part of the table
        for (Line textRow : lines) {
            for (Rectangle tableArea : tableAreas) {
                if (!tableArea.contains(textRow) && textRow.intersects(tableArea)) {
                    tableArea.setLeft((float) Math.floor(Math.min(textRow.getLeft(), tableArea.getLeft())));
                    tableArea.setRight((float) Math.ceil(Math.max(textRow.getRight(), tableArea.getRight())));
                }
            }
        }

        // get rid of tables that DO NOT intersect any text areas - these are likely graphs or some sort of graphic
        for (Iterator<Rectangle> iterator = tableAreas.iterator(); iterator.hasNext(); ) {
            Rectangle table = iterator.next();

            boolean intersectsText = false;
            for (Line textRow : lines) {
                if (table.intersects(textRow)) {
                    intersectsText = true;
                    break;
                }
            }

            if (!intersectsText) {
                iterator.remove();
            }
        }

        // lastly, there may be some tables that don't have any vertical rulings at all
        // we'll use text edges we've found to try and guess which text rows are part of a table

        // in his thesis nurminen goes through every row to try to assign a probability that the line is in a table
        // we're going to try a general heuristic instead, trying to find what type of edge (left/right/mid) intersects
        // the most text rows, and then use that magic number of "relevant" edges to decide what text rows should be
        // part of a table.


        boolean foundTable;
        boolean savedEdges = false;
        do {
            foundTable = false;

            // get rid of any text lines contained within existing tables, this allows us to find more tables
            for (Iterator<Line> iterator = lines.iterator(); iterator.hasNext(); ) {
                Line textRow = iterator.next();
                for (Rectangle table : tableAreas) {
                    if (table.contains(textRow)) {
                        iterator.remove();
                        break;
                    }
                }
            }

            // get text edges from remaining lines in the document
            TextEdges textEdges = this.getTextEdges(lines);
            List<TextEdge> leftTextEdges = textEdges.get(TextEdge.LEFT);
            List<TextEdge> midTextEdges = textEdges.get(TextEdge.MID);
            List<TextEdge> rightTextEdges = textEdges.get(TextEdge.RIGHT);

            if (!savedEdges) {
                allLeftTextEdges.addAll(leftTextEdges);
                allMidTextEdges.addAll(midTextEdges);
                allRightTextEdges.addAll(rightTextEdges);
                savedEdges = true;
            }

            List<TextEdge> sideTextEdges = new ArrayList<>(rightTextEdges);
            sideTextEdges.addAll(leftTextEdges);
            textEdges.add(sideTextEdges);

            // find the relevant text edges (the ones we think define where a table is)
            RelevantEdges relevantEdgeInfo = this.getRelevantEdges(textEdges, lines);

            // we found something relevant so let's look for rows that fit our criteria
            if (relevantEdgeInfo.edgeType != -1) {
                List<TextEdge> relevantEdges = null;
                switch (relevantEdgeInfo.edgeType) {
                    case TextEdge.SIDE_EDGE:
                        relevantEdges = sideTextEdges;
                        break;
                    case TextEdge.MID:
                        relevantEdges = midTextEdges;
                        break;
                }

                Rectangle table = this.getTableFromText(lines, relevantEdges, relevantEdgeInfo.edgeCount, horizontalRulings);

                if (table != null) {
                    foundTable = true;

                    Rectangle expandedTable = expand(page, table);
                    tableAreas.add(expandedTable);
                }
            }
        } while (foundTable);

        Set<Rectangle> tableSet = new TreeSet<>(TABLE_COMPARATOR);
        tableSet.addAll(tableAreas);

        return new ArrayList<>(tableSet);
    }

    /***
     * Finds biggest table on the page.
     *
     * Is prone to false detects on pages where there are no tables.
     * Also if there are more than one table, it will merge them.
     * However can find tables {@link NurminenDetectionAlgorithm#detect} fails to find.
     */
    public Rectangle bluntDetect() {
        if (allLines == null || textBoundingBox == null || horizontalRulings == null) {
            throw new RuntimeException("Please run detect first!");
        }

        // get text edges from remaining lines in the document
        TextEdges textEdges = this.getTextEdges(allLines);
        List<TextEdge> leftTextEdges = textEdges.get(TextEdge.LEFT);
        List<TextEdge> rightTextEdges = textEdges.get(TextEdge.RIGHT);

        List<TextEdge> sideTextEdges = new ArrayList<>(rightTextEdges);
        sideTextEdges.addAll(leftTextEdges);

        for (float tagetOverlap = 0.7f; tagetOverlap >= 0.1f; tagetOverlap -= 0.1f) {
            for (int edgeCount = 8; edgeCount >= 3; edgeCount--) {
                Rectangle table = this.getTableFromText(allLines, sideTextEdges, edgeCount, horizontalRulings);

                if (table != null && table.verticalOverlapPercent(textBoundingBox) > tagetOverlap) {
                    return expand(page, table);
                }
            }
        }
        return null;
    }

    /**
     * Expands the table to top and bottom, until new content intersects
     * table column lines (see {@link BasicExtractionAlgorithm#columnPositions(List)})
     */
    private Rectangle expand(Page page, Rectangle table) {
        Page tablePage = page.getArea(table);
        List<TextChunk> textChunks = TextElement.mergeWords(tablePage.getText());
        List<Line> relevantLines = TextChunk.groupByLines(textChunks);

        List<Float> columns = BasicExtractionAlgorithm.columnPositions(relevantLines);

        List<Ruling> verticalR = new ArrayList<>();
        for (Float column : columns) {
            float top = (page == null) ? table.getTop() : page.getTop();
            double height = (page == null) ? table.getHeight() : page.getHeight();
            // We add + 1 to column since if don't do it SpreadSheetExtractor can cut last letter.
            verticalR.add(new Ruling(top, column + 1, 0.1f, (float) height));
        }

        Page aboveTable = page.getArea(page.getTop(),
                                       table.getLeft(),
                                       table.getTop(),
                                       table.getRight());
        Page belowTable = page.getArea(table.getBottom(),
                                       table.getLeft(),
                                       page.getBottom(),
                                       table.getRight());

        Rectangle withBelow = expandIntoArea(table, verticalR, belowTable, false);
        Rectangle rectangle = expandIntoArea(withBelow, verticalR, aboveTable, true);

        return rectangle;
    }

    private Rectangle expandIntoArea(Rectangle initialTablePage, List<Ruling> verticalR,
                                     Page pageAreaToScan, boolean topPartOfTable) {
        List<TextChunk> expandedTextChunks = TextElement.mergeWords(pageAreaToScan.getText());
        List<Line> expandedLines = TextChunk.groupByLines(expandedTextChunks);

        if (topPartOfTable) {
            Collections.reverse(expandedLines);
        }

        Rectangle area = new Rectangle(initialTablePage.getTop(), initialTablePage.getLeft(), initialTablePage.width, initialTablePage.height);
        outerloop:
        for (Line line : expandedLines) {
            for (TextChunk textChunk : line.getTextElements()) {
                if (textChunk.isSameChar(Line.WHITE_SPACE_CHARS)) {
                    continue;
                }

                for (Ruling ruling : verticalR) {
                    TextChunk tc = textChunk;
                    if (textChunk.width > 5) { // give 5 pixel of room for error
                        tc = new TextChunk(textChunk.getTop(), textChunk.getLeft(),
                                           textChunk.width - 5, textChunk.height);
                    }

                    if (tc.intersectsLine(ruling)) {
                        break outerloop;
                    }
                }
            }
            area.merge(line);
        }

        if (topPartOfTable) {
            area.setTop(area.getTop() - 1); // otherwise text can get cut-off
        } else {
            area.setBottom(area.getBottom() + 1); // otherwise text can get cut-off
        }

        return area;
    }


    /**
     * Let's say we have a list which has bullet points (circles for example).
     * Every circles will have 3 edges: left, right and center.
     * Remove these excessive edges and leave only one.
     *
     * Otherwise we risk these areas being falsely detected as tables.
     */
    private void reduceBulletPointEdges(List<TextEdge> leftTextEdges, List<TextEdge> midTextEdges, List<TextEdge> rightTextEdges) {
        List<TextEdge> allTextEdges = new ArrayList<>();
        allTextEdges.addAll(leftTextEdges);
        allTextEdges.addAll(midTextEdges);
        allTextEdges.addAll(rightTextEdges);
        Collections.sort(allTextEdges, (t1, t2) -> Float.compare(t1.y2 - t1.y1, t2.y2 - t2.y1));


        Set<TextEdge> edgesToRemove = new HashSet<>();
        Float prevX = null;
        TextEdge prevEdge = null;
        for (Iterator<TextEdge> iterator = allTextEdges.iterator(); iterator.hasNext(); ) {
            TextEdge textEdge = iterator.next();

            Float x = textEdge.x1;
            if (prevX != null && Math.abs(x - prevX) < 5 && textEdge.getYOverlapPercent(prevEdge) > 0.9) {
                edgesToRemove.add(textEdge);
            }
            prevX = x;
            prevEdge = textEdge;
        }

        leftTextEdges.removeIf(edgesToRemove::contains);
        midTextEdges.removeIf(edgesToRemove::contains);
        rightTextEdges.removeIf(edgesToRemove::contains);
    }

    /**
     * 1. Find rows which intersect with at least "relevantEdgeCount" of edges of relevant type (relevantEdges)
     * to be considered part of table.
     * 2. Regions with relevant number of edges are united in case all rows between them are
     * closer than (totalRowSpacing / tableSpaceCount) * 2.5f
     * 3. Bounds of all the rows are bounds of the table (meaning everything in between them is also part of table)
     * 4. Expand the table to the top and to the bottom using horizontal rulings.
     */
    private Rectangle getTableFromText(List<Line> lines,
                                       List<TextEdge> relevantEdges,
                                       int relevantEdgeCount,
                                       List<Ruling> horizontalRulings) {

        Rectangle table = new Rectangle();

        Line prevRow = null;
        Line firstTableRow = null;
        Line lastTableRow = null;

        int tableSpaceCount = 0;
        float totalRowSpacing = 0;

        List<Rectangle> edgeRectangles = new ArrayList<>();
        for (TextEdge edge : relevantEdges) {
            edgeRectangles.add(new Rectangle((float) edge.getP1().getY(),
                                             (float) edge.getP1().getX(),
                                             edge.getWidth(),
                                             edge.getHeight()));
        }

        // go through the lines and find the ones that have the correct count of the relevant edges
        for (Line textRow : lines) {
            int numRelevantEdges = 0;
            int numRelevantEdgesToFullRow = 0;

            Rectangle fullTextRowRect = new Rectangle(textRow.getTop(), textRow.getLeft(), (float) textRow.getWidth(), (float) textRow.getHeight());
            fullTextRowRect.setRight(textBoundingBox.getRight());
            fullTextRowRect.setLeft(textBoundingBox.getLeft());

            for (Rectangle edgeRectangle : edgeRectangles) {
                if (textRow.intersects(edgeRectangle)) {
                    numRelevantEdges++;
                }
                if (fullTextRowRect.intersects(edgeRectangle)) {
                    numRelevantEdgesToFullRow++;
                }
            }

            if (firstTableRow != null && tableSpaceCount > 0) {
                // check to make sure this text row is within a line or so of the other lines already added
                // if it's not, we should stop the table here
                float tableLineThreshold = (totalRowSpacing / tableSpaceCount) * 2.5f;
                float lineDistance = textRow.getTop() - prevRow.getTop();

                if (lineDistance > tableLineThreshold || numRelevantEdgesToFullRow == 0) {
                    lastTableRow = prevRow;
                    break;
                }
            }

            // for larger tables, be a little lenient on the number of relevant rows the text intersects
            // for smaller tables, not so much - otherwise we'll end up treating paragraphs as tables too
            int relativeEdgeDifferenceThreshold = 1;
            if (relevantEdgeCount <= 3) {
                relativeEdgeDifferenceThreshold = 0;
            }



            // see if we have a candidate text row
            if (numRelevantEdges >= (relevantEdgeCount - relativeEdgeDifferenceThreshold)) {
                // keep track of table row spacing
                if (prevRow != null && firstTableRow != null) {
                    tableSpaceCount++;
                    totalRowSpacing += (textRow.getTop() - prevRow.getTop());
                }

                // row is part of a table
                if (table.getArea() == 0) {
                    firstTableRow = textRow;
                    table.setRect(textRow);
                } else {
                    table.setLeft(Math.min(table.getLeft(), textRow.getLeft()));
                    table.setBottom(Math.max(table.getBottom(), textRow.getBottom()));
                    table.setRight(Math.max(table.getRight(), textRow.getRight()));
                }
            } else {
                // no dice
                // if we're at the end of the table, save the last row
                if (firstTableRow != null && lastTableRow == null) {
                    lastTableRow = prevRow;
                }
            }

            prevRow = textRow;
        }

        // if we don't have a table now, we won't after the next step either
        if (table.getArea() == 0) {
            return null;
        }

        if (lastTableRow == null) {
            // takes care of one-row tables or tables that end at the bottom of a page
            lastTableRow = prevRow;
        }

        // use the average row height and nearby horizontal lines to extend the table area
        float avgRowHeight;
        if (tableSpaceCount > 0) {
            avgRowHeight = totalRowSpacing / tableSpaceCount;
        } else {
            avgRowHeight = lastTableRow.height;
        }

        float rowHeightThreshold = avgRowHeight * ROW_HEIGHT_THRESHOLD_MULT_BOTTOM;

        // check lines after the bottom of the table
        for (Line2D.Float ruling : horizontalRulings) {

            if (ruling.getY1() < table.getBottom()) {
                continue;
            }

            float distanceFromTable = (float) ruling.getY1() - table.getBottom();
            if (distanceFromTable <= rowHeightThreshold) {
                // use this ruling to help define the table
                table.setBottom((float) Math.max(table.getBottom(), ruling.getY1()));
                table.setLeft((float) Math.min(table.getLeft(), ruling.getX1()));
                table.setRight((float) Math.max(table.getRight(), ruling.getX2()));
            } else {
                // no use checking any further
                break;
            }
        }

        // do the same for lines at the top, but make the threshold greater since table headings tend to be
        // larger to fit up to three-ish rows of text (at least but we don't want to grab too much)
        rowHeightThreshold = avgRowHeight * ROW_HEIGHT_THRESHOLD_MULT_TOP;

        for (int i = horizontalRulings.size() - 1; i >= 0; i--) {
            Line2D.Float ruling = horizontalRulings.get(i);

            if (ruling.getY1() > table.getTop()) {
                continue;
            }

            float distanceFromTable = table.getTop() - (float) ruling.getY1();
            if (distanceFromTable <= rowHeightThreshold) {
                table.setTop((float) Math.min(table.getTop(), ruling.getY1()));
                table.setLeft((float) Math.min(table.getLeft(), ruling.getX1()));
                table.setRight((float) Math.max(table.getRight(), ruling.getX2()));
            } else {
                break;
            }
        }

        // add a bit of padding since the halved horizontal lines are a little fuzzy anyways
        table.setTop((float) Math.floor(table.getTop()) - TABLE_PADDING_AMOUNT);
        table.setBottom((float) Math.ceil(table.getBottom()) + TABLE_PADDING_AMOUNT);
        table.setLeft((float) Math.floor(table.getLeft()) - TABLE_PADDING_AMOUNT);
        table.setRight((float) Math.ceil(table.getRight()) + TABLE_PADDING_AMOUNT);

        return table;
    }

    private RelevantEdges getRelevantEdges(TextEdges textEdges, List<Line> lines) {
        List<TextEdge> midTextEdges = textEdges.get(TextEdge.MID);
        List<TextEdge> sideTextEdges = textEdges.get(TextEdge.SIDE_EDGE);

        // first we'll find the number of lines each type of edge crosses
        List<TextEdge>[][] edgeCountsPerLine = new List[lines.size()][TextEdge.NUM_TYPES];


        for (TextEdge edge : sideTextEdges) {
            if (edgeCountsPerLine[edge.intersectingTextRowCount - 1][TextEdge.SIDE_EDGE] == null) {
                edgeCountsPerLine[edge.intersectingTextRowCount - 1][TextEdge.SIDE_EDGE] = new ArrayList();
            }
            edgeCountsPerLine[edge.intersectingTextRowCount - 1][TextEdge.SIDE_EDGE].add(edge);
        }

        for (TextEdge edge : midTextEdges) {
            if (edgeCountsPerLine[edge.intersectingTextRowCount - 1][TextEdge.MID] == null) {
                edgeCountsPerLine[edge.intersectingTextRowCount - 1][TextEdge.MID] = new ArrayList<>();
            }
            edgeCountsPerLine[edge.intersectingTextRowCount - 1][TextEdge.MID].add(edge);
        }

        // now let's find the relevant edge type and the number of those edges we should look for
        // we'll only take a minimum of two edges to look for tables
        int relevantEdgeType = -1;
        int relevantEdgeCount = 0;
        for (int i = edgeCountsPerLine.length - 1; i > 2; i--) {
            // if more than two left edges cross exactly i rows
            // relevantEdgeCount = number of left edges
            List<TextEdge> sideEdges = edgeCountsPerLine[i][TextEdge.SIDE_EDGE];
            List<TextEdge> midEdges = edgeCountsPerLine[i][TextEdge.MID];
            sideEdges = (sideEdges == null) ? new ArrayList<>() : new ArrayList<>(sideEdges);
            midEdges = (midEdges == null) ? new ArrayList<>() : new ArrayList<>(midEdges);

            // add edges which have +-1 number of lines
            // Not mid edges since they are more false-detect prone anyways
            if (i > 3) {
                listAddAll(sideEdges, edgeCountsPerLine[i - 1][TextEdge.SIDE_EDGE]);

                if (i < edgeCountsPerLine.length - 1) {
                    listAddAll(sideEdges, edgeCountsPerLine[i + 1][TextEdge.SIDE_EDGE]);
                }
            }

            // merge adjacent edges together and get edges count of only the biggest group
            List<LinesGroup> sideGroups = getAdjacentGroups(sideEdges);
            List<LinesGroup> midGroups = getAdjacentGroups(midEdges);

            int sideEdgesCount = sideEdges.size();
            int midEdgesCount = midEdges.size();

            if (sideGroups.size() > 1) sideEdgesCount = Collections.max(sideGroups).count;
            if (midEdges.size() > 1) midEdgesCount = Collections.max(midGroups).count;


            if (midEdgesCount > 1) {
                relevantEdgeCount = midEdgesCount;
                relevantEdgeType = TextEdge.MID;
                break;
            }
            if (sideEdgesCount > 2) {
                relevantEdgeCount = sideEdgesCount;
                relevantEdgeType = TextEdge.SIDE_EDGE;
                break;
            }
        }

        return new RelevantEdges(relevantEdgeType, relevantEdgeCount);
    }

    class LinesGroup extends Line2D.Float implements Comparable<LinesGroup> {
        int count;

        LinesGroup(Line2D.Float groupLine) {
            super(groupLine.getP1(), groupLine.getP2());
            x1 = 0; // X coords doesn't matter
            x2 = 0;
            this.count = 1;
        }

        private boolean mergeByY(LinesGroup group) {
            if (this.intersectsLine(group)) {
                count += group.count;
                y1 = Math.min(group.y1, y1);
                y2 = Math.max(group.y2, y2);
                return true;
            }
            return false;
        }

        @Override
        public int compareTo(LinesGroup group) {
            return Integer.compare(count, group.count);
        }
    }

    private List<LinesGroup> getAdjacentGroups(List<TextEdge> textEdges) {
        List<LinesGroup> groups = new ArrayList<>();
        if (textEdges != null) {
            for (TextEdge textEdge : textEdges) {
                groups.add(new LinesGroup(textEdge));
            }

            Iterator<LinesGroup> it = groups.iterator();
            while (it.hasNext()) {
                LinesGroup groupI = it.next();
                for (LinesGroup groupJ : groups) {
                    if (groupI == groupJ) {
                        continue;
                    }
                    if (groupJ.mergeByY(groupI)) {
                        it.remove();
                        break;
                    }
                }
            }
        }
        return groups;
    }

    private static void listAddAll(List a, List b) {
        if (b != null) {
            a.addAll(b);
        }
    }

    private static class Range {
        private static final float HALF_RANGE_SIZE = 2.0f;
        private static final float MID_HALF_RANGE_SIZE = 1.5f;

        private final Type type;
        float numbersSum;
        float avg;
        List<Float> numbers = new ArrayList<>();
        List<TextChunk> edgeChunks = new ArrayList<>();

        enum Type {
            LEFT,
            MID,
            RIGHT;
        }

        Range(float firstNumber, TextChunk edgeChunk, Type type) {
            numbersSum = firstNumber;
            numbers.add(firstNumber);
            edgeChunks.add(edgeChunk);
            avg = firstNumber;
            this.type = type;
        }

        float getHalfRangeSize(float number, TextChunk text) {
            float maxRangeSize = getHalfRangeSizeConst();
            // give less room for error for far rows
            if (edgeChunks.size() > 0 && type != Type.MID) {
                double distance = Math.abs(text.getMinY() - edgeChunks.get(edgeChunks.size() - 1).getMaxY());
                // multiply by log to make f=maxRangeSize(distance) grow faster than linear
                double k = 60.0f / (distance * Math.log(Math.max(distance, 10)));
                maxRangeSize = (float) k * maxRangeSize;
            }

            return maxRangeSize;
        }

        boolean add(float number, TextChunk text) {
            if (Math.abs(number - avg) < getHalfRangeSize(number, text)) {
                numbersSum += number;
                numbers.add(number);
                edgeChunks.add(text);
                avg = numbersSum / numbers.size();
                return true;
            }
            return false;
        }

        boolean addToBeginning(float number, TextChunk text) {
          if (add(number, text)) {
            numbers.add(0, number);
            edgeChunks.add(0, text);
            numbers.remove(numbers.size() - 1);
            edgeChunks.remove(edgeChunks.size() - 1);

            return true;
          }
          return false;
        }

        boolean isBlownOut(TextChunk text, float left, float mid, float right) {
            float edge; float halfRangeSize;
            if (type == Type.MID) {
                edge = mid;
                halfRangeSize = getHalfRangeSizeConst();
            } else {
                edge = (type == Type.LEFT) ? left : right;
                halfRangeSize = getHalfRangeSize(edge, text) / 2;
            }

            return avg > left && avg < right &&
                Math.abs(edge - avg) >= halfRangeSize;
        }

        TextEdge getTextEdge(int linesSize) {
            TextChunk first = edgeChunks.get(0);
            TextChunk last = edgeChunks.get(edgeChunks.size() - 1);

            TextEdge edge = new TextEdge(avg - getHalfRangeSizeConst(), first.getTop(), avg + getHalfRangeSizeConst(), last.getBottom());
            edge.intersectingTextRowCount = Math.min(edgeChunks.size(), linesSize);

            return edge;
        }

        private float getHalfRangeSizeConst() {
            return (type == Type.MID) ? MID_HALF_RANGE_SIZE : HALF_RANGE_SIZE;
        }
    }

    private TextEdges getTextEdges(List<Line> lines) {
        List<Range> rangesLeft = new ArrayList<>(); List<Range> rangesMid = new ArrayList<>(); List<Range> rangesRight = new ArrayList<>();
        List<Range> rangesActiveLeft = new ArrayList<>(); List<Range> rangesActiveMid = new ArrayList<>(); List<Range> rangesActiveRight = new ArrayList<>();
        List<Range>[] rangesArr = new List[]{rangesLeft, rangesMid, rangesRight};
        List<Range>[] rangesActiveArr = new List[]{rangesActiveLeft, rangesActiveMid, rangesActiveRight};

        for (Line textRow : lines) {
            for (TextChunk text : textRow.getTextElements()) {
                float left = text.getLeft();
                float right = text.getRight();
                float mid = left + ((right - left) / 2);

                for (int i = Range.Type.LEFT.ordinal() ; i <= Range.Type.RIGHT.ordinal(); i++) {
                    List<Range> ranges = rangesArr[i];
                    List<Range> rangesActive = rangesActiveArr[i];
                    Range.Type rangeType = Range.Type.values()[i];

                    float number = (rangeType == Range.Type.LEFT) ? left :
                      (rangeType == Range.Type.MID) ? mid : right;

                    boolean added = false;
                    Float closestNumber = null;
                    Range closestRange = null;
                    for (Range range : rangesActive) {
                        added = range.add(number, text);

                        Float lastNumber = range.numbers.get(range.numbers.size() - 1);
                        if (closestNumber == null || (number > lastNumber &&
                          Math.abs(number - lastNumber) < Math.abs(number - closestNumber))) {
                            closestNumber = lastNumber;
                            closestRange = range;
                        }

                        if (added) {
                            break;
                        }
                    }
                    if (!added) {
                        Range newRange = new Range(number, text, rangeType);

                        // backtrack and add close edges from previous lines.
                        if (closestRange != null) {
                            for (int j = closestRange.edgeChunks.size() - 1; j >= 0; j--) {
                                closestNumber = closestRange.numbers.get(j);

                                if (Math.abs(number - closestNumber) > closestRange.getHalfRangeSizeConst()) {
                                    break;
                                }

                                if (!newRange.addToBeginning(closestNumber, closestRange.edgeChunks.get(j))) {
                                    break;
                                }
                            }
                        }
                        rangesActive.add(newRange);
                    }

                    rangesActive.removeIf(range -> {
                        if (range.isBlownOut(text, left, mid, right)) {
                            if (range.numbers.size() >= REQUIRED_TEXT_LINES_FOR_EDGE) {
                                ranges.add(range);
                            }
                            return true;
                        }
                        return false;
                    });
                }
            }
        }

        for (int i = Range.Type.LEFT.ordinal() ; i <= Range.Type.RIGHT.ordinal(); i++) {
            for (Range range : rangesActiveArr[i]) {
                if (range.numbers.size() >= REQUIRED_TEXT_LINES_FOR_EDGE) {
                    rangesArr[i].add(range);
                }
            }
        }

        List<TextEdge>[] textEdges = new List[]{new ArrayList<>(), new ArrayList<>(), new ArrayList<>()};
        for (int i = Range.Type.LEFT.ordinal() ; i <= Range.Type.RIGHT.ordinal(); i++) {
            for (Range range : rangesArr[i]) {
                textEdges[i].add(range.getTextEdge(lines.size()));
            }
        }

        // remove left edges which are too close to beginning of the page
        // they don't really indicate a table.
        for (Iterator<TextEdge> iterator = textEdges[0].iterator(); iterator.hasNext();) {
            TextEdge textEdge = iterator.next();

            if (textEdge.x1 < textBoundingBox.getLeft() + 8) {
                iterator.remove();
            }
        }

        reduceBulletPointEdges(textEdges[0], textEdges[1], textEdges[2]);

        return new TextEdges(textEdges[0], textEdges[1], textEdges[2]);
    }

    private List<Rectangle> getTableAreasFromCells(List<? extends Rectangle> cells) {
        List<List<Rectangle>> cellGroups = new ArrayList<>();
        for (Rectangle cell : cells) {
            boolean addedToGroup = false;

            cellCheck:
            for (List<Rectangle> cellGroup : cellGroups) {
                for (Rectangle groupCell : cellGroup) {
                    Point2D[] groupCellCorners = groupCell.getPoints();
                    Point2D[] candidateCorners = cell.getPoints();

                    for (int i = 0; i < candidateCorners.length; i++) {
                        for (int j = 0; j < groupCellCorners.length; j++) {
                            if (candidateCorners[i].distance(groupCellCorners[j]) < CELL_CORNER_DISTANCE_MAXIMUM) {
                                cellGroup.add(cell);
                                addedToGroup = true;
                                break cellCheck;
                            }
                        }
                    }
                }
            }

            if (!addedToGroup) {
                ArrayList<Rectangle> cellGroup = new ArrayList<>();
                cellGroup.add(cell);
                cellGroups.add(cellGroup);
            }
        }

        // create table areas based on cell group
        List<Rectangle> tableAreas = new ArrayList<>();
        for (List<Rectangle> cellGroup : cellGroups) {
            // less than four cells should not make a table
            if (cellGroup.size() < REQUIRED_CELLS_FOR_TABLE) {
                continue;
            }

            float top = Float.MAX_VALUE;
            float left = Float.MAX_VALUE;
            float bottom = Float.MIN_VALUE;
            float right = Float.MIN_VALUE;

            for (Rectangle cell : cellGroup) {
                if (cell.getTop() < top) top = cell.getTop();
                if (cell.getLeft() < left) left = cell.getLeft();
                if (cell.getBottom() > bottom) bottom = cell.getBottom();
                if (cell.getRight() > right) right = cell.getRight();
            }

            tableAreas.add(new Rectangle(top, left, right - left, bottom - top));
        }

        return tableAreas;
    }

    private List<Ruling> getHorizontalRulings(BufferedImage image) {

        // get all horizontal edges, which we'll define as a change in grayscale colour
        // along a straight line of a certain length
        ArrayList<Ruling> horizontalRulings = new ArrayList<>();

        Raster r = image.getRaster();
        int width = r.getWidth();
        int height = r.getHeight();

        for (int x = 0; x < width; x++) {

            int[] lastPixel = r.getPixel(x, 0, (int[]) null);

            for (int y = 1; y < height - 1; y++) {

                int[] currPixel = r.getPixel(x, y, (int[]) null);

                int diff = Math.abs(currPixel[0] - lastPixel[0]);
                if (diff > GRAYSCALE_INTENSITY_THRESHOLD) {
                    // we hit what could be a line
                    // don't bother scanning it if we've hit a pixel in the line before
                    boolean alreadyChecked = false;
                    for (Line2D.Float line : horizontalRulings) {
                        if (y == line.getY1() && x >= line.getX1() && x <= line.getX2()) {
                            alreadyChecked = true;
                            break;
                        }
                    }

                    if (alreadyChecked) {
                        lastPixel = currPixel;
                        continue;
                    }

                    int lineX = x + 1;

                    while (lineX < width) {
                        int[] linePixel = r.getPixel(lineX, y, (int[]) null);
                        int[] abovePixel = r.getPixel(lineX, y - 1, (int[]) null);

                        if (Math.abs(linePixel[0] - abovePixel[0]) <= GRAYSCALE_INTENSITY_THRESHOLD
                                || Math.abs(currPixel[0] - linePixel[0]) > GRAYSCALE_INTENSITY_THRESHOLD) {
                            break;
                        }

                        lineX++;
                    }

                    int endX = lineX - 1;
                    int lineWidth = endX - x;
                    if (lineWidth > HORIZONTAL_EDGE_WIDTH_MINIMUM) {
                        horizontalRulings.add(new Ruling(new Point2D.Float(x, y), new Point2D.Float(endX, y)));
                    }
                }

                lastPixel = currPixel;
            }
        }

        return horizontalRulings;
    }

    private List<Ruling> getVerticalRulings(BufferedImage image) {

        // get all vertical edges, which we'll define as a change in grayscale colour
        // along a straight line of a certain length
        ArrayList<Ruling> verticalRulings = new ArrayList<>();

        Raster r = image.getRaster();
        int width = r.getWidth();
        int height = r.getHeight();

        for (int y = 0; y < height; y++) {

            int[] lastPixel = r.getPixel(0, y, (int[]) null);

            for (int x = 1; x < width - 1; x++) {

                int[] currPixel = r.getPixel(x, y, (int[]) null);

                int diff = Math.abs(currPixel[0] - lastPixel[0]);
                if (diff > GRAYSCALE_INTENSITY_THRESHOLD) {
                    // we hit what could be a line
                    // don't bother scanning it if we've hit a pixel in the line before
                    boolean alreadyChecked = false;
                    for (Line2D.Float line : verticalRulings) {
                        if (x == line.getX1() && y >= line.getY1() && y <= line.getY2()) {
                            alreadyChecked = true;
                            break;
                        }
                    }

                    if (alreadyChecked) {
                        lastPixel = currPixel;
                        continue;
                    }

                    int lineY = y + 1;

                    while (lineY < height) {
                        int[] linePixel = r.getPixel(x, lineY, (int[]) null);
                        int[] leftPixel = r.getPixel(x - 1, lineY, (int[]) null);

                        if (Math.abs(linePixel[0] - leftPixel[0]) <= GRAYSCALE_INTENSITY_THRESHOLD
                                || Math.abs(currPixel[0] - linePixel[0]) > GRAYSCALE_INTENSITY_THRESHOLD) {
                            break;
                        }

                        lineY++;
                    }

                    int endY = lineY - 1;
                    int lineLength = endY - y;
                    if (lineLength > VERTICAL_EDGE_HEIGHT_MINIMUM) {
                        verticalRulings.add(new Ruling(new Point2D.Float(x, y), new Point2D.Float(x, endY)));
                    }
                }

                lastPixel = currPixel;
            }
        }

        return verticalRulings;
    }


    // taken from http://www.docjar.com/html/api/org/apache/pdfbox/examples/util/RemoveAllText.java.html
    private PDDocument removeText(PDPage page) throws IOException {

        PDFStreamParser parser = new PDFStreamParser(page);
        parser.parse();
        List<Object> tokens = parser.getTokens();
        List<Object> newTokens = new ArrayList<>();
        for (Object token : tokens) {
            if (token instanceof Operator) {
                Operator op = (Operator) token;
                if (op.getName().equals("TJ") || op.getName().equals("Tj")) {
                    //remove the one argument to this operator
                    newTokens.remove(newTokens.size() - 1);
                    continue;
                }
            }
            newTokens.add(token);
        }

        PDDocument document = new PDDocument();
        PDPage newPage = document.importPage(page);
        newPage.setResources(page.getResources());

        PDStream newContents = new PDStream(document);
        OutputStream out = newContents.createOutputStream(COSName.FLATE_DECODE);
        ContentStreamWriter writer = new ContentStreamWriter(out);
        writer.writeTokens(newTokens);
        out.close();
        newPage.setContents(newContents);
        return document;
    }
}
