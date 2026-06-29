# Waze Parallel Segments

A Tampermonkey/Greasemonkey userscript for the [Waze Map Editor](https://www.waze.com/editor) that splits two-way road segments into parallel one-way carriageways. Supports both **left-hand traffic (LHT)** and **right-hand traffic (RHT)** countries with automatic side detection.

## Features

- **Split two-way roads** — Converts a two-way segment into two parallel one-way segments.
- **Configurable gap distance** — Choose from 5 to 45 meters between the parallel carriageways.
- **Multi-segment chaining** — Select multiple connected segments to split an entire road in one operation. Segments are automatically ordered from end to end.
- **Traffic side auto-detection** — Automatically detects whether the country uses LHT or RHT via the WME SDK's segment → city → country chain (with viewport-based fallback). Carriageways are placed on the correct physical side of the road.
- **Lane count awareness** — Only splits segments with equal (or zero) defined lanes on both sides.
- **Pedestrian road exclusion** — Pedestrian road types are automatically skipped.
- **Script update monitoring** — Checks for new versions on GreasyFork.

## Installation

1. Install the [Tampermonkey](https://www.tampermonkey.net/) or [Greasemonkey](https://www.greasespot.net/) browser extension.
2. Install the script from [GreasyFork](https://greasyfork.org/en/scripts/491466-waze-parallel-segments).
3. The script will automatically load when you open the [Waze Map Editor](https://www.waze.com/editor).

## Usage

### Single Segment
1. Select a two-way road segment in the WME.
2. The **"Distance between the two parallel segments"** dropdown and **"Split the segments"** button appear in the segment edit panel.
3. Choose the desired gap distance and click **"Split the segments"**.

### Multiple Segments (Chain)
1. Select multiple connected two-way segments **sequentially** (from one end of the road to the other).
2. A confirmation dialog will remind you to verify the result after splitting.
3. Click **"Continue"** to proceed. The script will automatically order the segments, split each one, and connect the resulting parallel segments with junction nodes.

> ⚠️ **Always verify the results** after a multi-segment split — especially turn restrictions at the newly created junction nodes.

## How It Works

1. **Select a segment** — When you select a two-way road in the editor, the script shows a distance picker and a **"Split the segments"** button in the side panel.
2. **Detect driving side** — The script automatically figures out whether the country drives on the left (LHT) or right (RHT), so the new carriageways are placed on the correct side of the road.
3. **Split the road in half** — The selected segment is cut at its midpoint, creating two shorter segments.
4. **Offset each half** — Each half is shifted sideways (perpendicular to the road) to create two parallel lines. The direction of the shift depends on the driving side:
   - **LHT countries**: left half shifts left, right half shifts right.
   - **RHT countries**: the sides are swapped so carriageways are on the correct physical sides.
5. **Apply the new geometry** — The two new segments get their updated shapes.
6. **Set direction** — Both segments are set to **one-way** (A→B), so traffic flows in opposite directions on each carriageway.
7. **Enable turns** — Turns are activated at all junction nodes so traffic can enter and exit the new roads.
8. **Connect multiple segments** — If you selected more than one connected segment, the script also creates junction nodes between the parallel carriageways at each connection point.

## Technical Details

- **API**: Fully migrated to the [WME SDK](https://www.waze.com/editor/sdk) — no legacy `Waze/Action/*` actions except `AddNode` (which has no SDK replacement for multi-segment junctions).
- **Geometry**: All point-offset math uses [Turf.js](https://turfjs.org/) (WGS84 coordinate space). Line intersection helpers remain as plain JS functions.

## Changelog Highlights

| Version | Changes |
|---------|---------|
| 2026.06.29.01 | Fixed lane count detection; segments with equal defined lanes on both sides can now be split. |
| 2026.03.31.01 | Fixed broken country detection for segment-address-based lookup; uses `sdk.Countries.getTopCountry()` as primary method. |
| 2026.03.30.08 | Fixed RHT detection caching bug that caused RHT countries to be treated as LHT after editing in an LHT country. |
| 2026.03.30.07 | Added LHT/RHT traffic side detection; bearing offsets swapped for RHT countries. |
| 2026.03.30.01 | Full migration from legacy WME API + OpenLayers to WME SDK + Turf.js. |
| Earlier | Original implementation by J0N4S13 using legacy WME API and OpenLayers. |

## Author

- **kid4rm90s & Copilot** — WME SDK migration and ongoing development.
- **J0N4S13** ([jonathanserrario@gmail.com](mailto:jonathanserrario@gmail.com)) — Original author.

## License

[MIT License](LICENSE)
