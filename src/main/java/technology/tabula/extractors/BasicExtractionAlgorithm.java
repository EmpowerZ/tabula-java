package technology.tabula.extractors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Arrays;

import technology.tabula.Line;
import technology.tabula.Page;
import technology.tabula.Rectangle;
import technology.tabula.Ruling;
import technology.tabula.Table;
import technology.tabula.TextChunk;
import technology.tabula.TextElement;

/**
 * Extract a data Table, adding column lines in positions where there are no text on page.
 * and matching strings into rows using their position
 *
 * See {@link BasicExtractionAlgorithm#extract(Page, List)} for more info
 */
public class BasicExtractionAlgorithm implements ExtractionAlgorithm {
    private boolean mixedTableExtractionEnabled; // takes columns from basic extractor and row rulings (if present) from pdf.
    private List<Ruling> verticalRulings = null;
    public List<Ruling> mixedExtractionRulings = new ArrayList<>();

    public BasicExtractionAlgorithm() {
    }
    
    public BasicExtractionAlgorithm(List<Ruling> verticalRulings) {
        this.verticalRulings = verticalRulings;
    }
    
    public List<Table> extract(Page page, List<Float> verticalRulingPositions) {
        List<Ruling> verticalRulings = new ArrayList<>(verticalRulingPositions.size());
        for (Float p: verticalRulingPositions) {
            verticalRulings.add(new Ruling(page.getTop(), p, 0.0f, (float) page.getHeight()));
        }
        this.verticalRulings = verticalRulings;
        return this.extract(page);
    }

    private List<Ruling> getRelevantRulings(Page page, List<Ruling> horizontalR) {
        Iterator<Ruling> it = horizontalR.iterator();
        while (it.hasNext()) {
            Ruling hr = it.next();

            // if page not contains at least part of line
            if (!page.intersectsLine(hr)) {
                it.remove();
            }
        }
        return horizontalR;
    }

    /**
     * 1. Group strings by their Y coordinate into lines.
     * 2. Find column coordinates (vertical lines which do to intersect text).
     * 3. Extra columns using string lines and columns.
     */
    @Override
    public List<Table> extract(Page page) {
        List<TextElement> textElements = page.getText();
        
        if (textElements.size() == 0) {
            return Arrays.asList(new Table[] { Table.empty() });
        }
        
        List<TextChunk> textChunks = this.verticalRulings == null ? TextElement.mergeWords(page.getText()) : TextElement.mergeWords(page.getText(), this.verticalRulings);
        List<Line> lines = TextChunk.groupByLines(textChunks);
        List<Float> columns = null;
        
        if (this.verticalRulings != null) {
            Collections.sort(this.verticalRulings, new Comparator<Ruling>() {
                @Override
                public int compare(Ruling arg0, Ruling arg1) {
                    return Double.compare(arg0.getLeft(), arg1.getLeft());
                }
            });
            columns = new ArrayList<>(this.verticalRulings.size());
            for (Ruling vr: this.verticalRulings) {
                columns.add(vr.getLeft());
            }
        }
        else {
            columns = columnPositions(lines);
        }
        
        Table table = new Table(this);
        table.setRect(page.getLeft(), page.getTop(), page.getWidth(), page.getHeight());

        //ArrayList<Float> columnsNew = new ArrayList<>(columns);
        for (int i = 0; i < lines.size(); i++) {
            Line line = lines.get(i);
            List<TextChunk> elements = line.getTextElements();
            
            Collections.sort(elements, new Comparator<TextChunk>() {

				@Override
				public int compare(TextChunk o1, TextChunk o2) {
					return new java.lang.Float(o1.getLeft()).compareTo(o2.getLeft());
				}
			});
            
            for (TextChunk tc: elements) {
                if (tc.isSameChar(Line.WHITE_SPACE_CHARS)) {
                    continue;
                }

                int j = 0;
                boolean found = false;
                for(; j < columns.size(); j++) {
                    if (tc.getLeft() <= columns.get(j)) {
                        found = true;
                        //columnsNew.set(j, Math.max(columnsNew.get(j), tc.getRight()));
                        break;
                    } 
                }
                table.add(tc, i, found ? j : columns.size());
            }
        }


        // Mixed Extraction (Horizontal rulings are present, but vertical are not)
        List<Ruling> horizontalR = page.getHorizontalRulings();
        horizontalR = Ruling.collapseOrientedRulings(horizontalR);
        horizontalR = getRelevantRulings(page, horizontalR);

        if (mixedTableExtractionEnabled &&
          lines.size() != 0 && (float) horizontalR.size() / lines.size() > 0.3) {
            float minHRuling = Float.MAX_VALUE;
            float maxHRuling = Float.MIN_VALUE;
            for (Ruling hr : horizontalR) {
                minHRuling = Math.min(minHRuling, hr.y1);
                maxHRuling = Math.max(maxHRuling, hr.y1);

                hr.setLeft(page.getLeft());
                hr.setRight(page.getRight());
            }

            float contentTop = lines.get(0).getTop();
            float contentBottom = lines.get(lines.size() - 1).getBottom();

            // incase there are text above top ruling we need a line on top of the page
            if (contentTop < minHRuling) {
                horizontalR.add(new Ruling(page.getPoints()[0], page.getPoints()[1])); // top line
            }
            if (contentBottom > maxHRuling) {
                horizontalR.add(new Ruling(page.getPoints()[3], page.getPoints()[2])); // bottom line
            }

            List<Ruling> verticalR = new ArrayList<>();
            columns.add(page.x - 1);
            for (Float column : columns) {
                // We add + 1 to column since if don't do it SpreadSheetExtractor can cut last letter.
                verticalR.add(new Ruling(page.getTop(), column + 1, 0.1f, page.height));
            }
            // If horizontal mixedExtractionRulings start after table start. First column will not be seen. Hence make them a bit larger

            verticalR.addAll(horizontalR);
            mixedExtractionRulings = new ArrayList<>(verticalR);
            return new SpreadsheetExtractionAlgorithm().extract(page, verticalR);
        }
        
        return Arrays.asList(new Table[] { table } );
    }
    
    @Override
    public String toString() {
        return "stream";
    }
    
    
    /**
     * Merges rectangles from text lines which overlap horizontally into big rectangles.
     * Than makes right side of every big rectangle. These are our columns.
     *
     * @param lines must be an array of lines sorted by their +top+ attribute
     * @return a list of column boundaries (x axis)
     */
    public static List<java.lang.Float> columnPositions(List<Line> lines) {
        // ignore first row (might be a title header), not merge with them. See eu-001.pdf, Crawford_technologies.pdf for example.
        //int startIndex = (lines.size() > 5) ? 1 : 0;
        int startIndex = 0;

        List<Rectangle> regions = new ArrayList<>();
        for (TextChunk tc: lines.get(startIndex).getTextElements()) {
            if (tc.isSameChar(Line.WHITE_SPACE_CHARS)) { 
                continue; 
            }
            Rectangle r = new Rectangle();
            r.setRect(tc);
            regions.add(r);
        }
        
        for (Line l: lines.subList(startIndex + 1, lines.size())) {
            List<TextChunk> lineTextElements = new ArrayList<>();
            for (TextChunk tc: l.getTextElements()) {
                if (!tc.isSameChar(Line.WHITE_SPACE_CHARS)) { 
                    lineTextElements.add(tc);
                }
            }
            
            for (Rectangle cr: regions) {

                List<TextChunk> overlaps = new ArrayList<>();
                for (TextChunk te: lineTextElements) {
                    if (cr.horizontallyOverlaps(te)) {
                        overlaps.add(te);
                    }
                }
                
                for (TextChunk te: overlaps) {
                    cr.merge(te);
                }
                
                lineTextElements.removeAll(overlaps);
            }
            
            for (TextChunk te: lineTextElements) {
                Rectangle r = new Rectangle();
                r.setRect(te);
                regions.add(r);
            }
        }
        
        List<java.lang.Float> rv = new ArrayList<>();
        for (Rectangle r: regions) {
            rv.add(r.getRight());
        }
        
        Collections.sort(rv);
        
        return rv;
        
    }

    public void setMixedTableExtractionEnabled(boolean mixedTableExtractionEnabled) {
        this.mixedTableExtractionEnabled = mixedTableExtractionEnabled;
    }
}
