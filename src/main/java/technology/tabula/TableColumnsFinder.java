package technology.tabula;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TableColumnsFinder {
    private final List<Line> lines;
    List<Rectangle> regions = new ArrayList<>();

    /**
     * @param lines must be an array of lines sorted by their +top+ attribute
     */
    public TableColumnsFinder(List<Line> lines) {
        this.lines = lines;
    }

    /**
     * Merges rectangles from text lines which overlap horizontally into big rectangles.
     * Than makes right side of every big rectangle. These are our columns.
     *
     * @return a list of column boundaries (x axis)
     */
    public List<Float> generateColumns() {
        // ignore first rows (might be a title header something at the top or wrongly detected thing at top of table),
        // not merge with them. See eu-001.pdf, Crawford_technologies.pdf for example.
        int startIndex = (lines.size() > 4) ? 1 : 0;
        startIndex = (lines.size() > 5) ? 2 : startIndex;
        int skipEndElements = (lines.size() > 5) ? 1 : 0;
        skipEndElements = (lines.size() > 7) ? 2 : skipEndElements;

        for (TextChunk tc: lines.get(startIndex).getTextElements()) {
            if (tc.isSameChar(Line.WHITE_SPACE_CHARS)) {
                continue;
            }
            Rectangle r = new Rectangle();
            r.setRect(tc);
            regions.add(r);
        }

        for (Line l: lines.subList(startIndex + 1, lines.size() - skipEndElements)) {
            addLine(l, true);
        }

        for (Line l: lines.subList(0, startIndex + 1)) {
            addLine(l, false);
        }

        for (Line l: lines.subList(lines.size() - skipEndElements - 1, lines.size())) {
            addLine(l, false);
        }

        return columns();
    }

    public void addLine(Line line, boolean merge) {
        List<TextChunk> lineTextElements = new ArrayList<>();
        for (TextChunk tc: line.getTextElements()) {
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

            if (merge) {
                for (TextChunk te : overlaps) {
                    cr.merge(te);
                }
            }

            lineTextElements.removeAll(overlaps);
        }

        for (TextChunk te: lineTextElements) {
            Rectangle r = new Rectangle();
            r.setRect(te);
            regions.add(r);
        }
    }

    public List<Float> columns() {
        List<Float> rv = new ArrayList<>();
        for (Rectangle r: getRegions()) {
            rv.add(r.getRight());
        }

        Collections.sort(rv);
        return rv;
    }

    public Set<Rectangle> getRegions() {
        for (Rectangle ri : regions) {
            for (Rectangle rj : regions) {
                if (ri.horizontallyOverlaps(rj)) {
                    ri.merge(rj);
                    rj.merge(ri);
                }
            }
        }

        return new HashSet<>(regions);
    }
}
