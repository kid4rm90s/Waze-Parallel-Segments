// ==UserScript==
// @name         Waze Parallel Segments
// @version      2026.04.18.01
// @description  Splits two-way segments into parallel one-way carriageways. Supports both left-hand and right-hand traffic countries.
// @author       kid4rm90s & copilot (original author J0N4S13)
// @include 	 /^https:\/\/(www|beta)\.waze\.com\/(?!user\/)(.{2,6}\/)?editor.*$/
// @exclude      https://www.waze.com/user/*editor/*
// @exclude      https://www.waze.com/*/user/*editor/*
// @connect      greasyfork.org
// @grant        GM_xmlhttpRequest
// @grant        GM_setClipboard
// @grant        unsafeWindow
// @require 	 https://greasyfork.org/scripts/560385/code/WazeToastr.js
// @require      https://cdn.jsdelivr.net/npm/@turf/turf@7/turf.min.js
// @namespace    https://greasyfork.org/users/1087400
/* 
Original Author Thanks : J0N4S13 (jonathanserrario@gmail.com)
Migrated to WME SDK by kid4rm90s
*/
// @downloadURL https://update.greasyfork.org/scripts/491466/WAZEParallel%20Segments%20Mod%20for%20NP.user.js
// @updateURL   https://update.greasyfork.org/scripts/491466/WAZEParallel%20Segments%20Mod%20for%20NP.meta.js
// ==/UserScript==

(function () {
    'use strict';

    // ─── Script metadata ────────────────────────────────────────────────────────
    const updateMessage = `This script has been migrated to the <strong>WME SDK</strong>.<br>` +
        `Both left-hand and right-hand traffic countries are now supported.<br><br>` +
        `<em>Happy Mapping!</em>`;
    const scriptName = GM_info.script.name;
    const scriptVersion = GM_info.script.version;
    const downloadUrl = GM_info.script.downloadURL;
    const forumURL = 'https://greasyfork.org/en/scripts/491466-WAZEParallel-segments-mod-for-np/feedback';

    // ─── Road type IDs ──────────────────────────────────────────────────────────
    // Road types that are drivable (used in deactivated road-conversion code kept for reference)
    const drivableRoadIds = [3, 4, 6, 7, 2, 1, 22, 8, 20, 17, 15, 18, 19];
    // Road types considered pedestrian (excluded from split)
    const pedestrianRoadIds = [5, 10, 16];

    const language = {
        btnSplit: "Split the segments",
        strMeters: "m",
        strDistance: "Distance between the two parallel segments:",
        strSelMoreSeg: "Since you have more than 1 segment selected, to use this function make sure that you have selected segments sequentially (from one end to the other) and after executing the script, VERIFY the result obtained."
    };

    // ─── State tracking across multi-segment splits ──────────────────────────
    let last_node_A = null;
    let last_node_B = null;
    let last_coord_left_first = null;
    let last_coord_left_last = null;
    let last_coord_right_first = null;
    let last_coord_right_last = null;
    let baseDirection = null;

    // ─── SDK instance ────────────────────────────────────────────────────────
    let sdk = null;

    // ─── Traffic side ────────────────────────────────────────────────────────
    // Re-detected on every split so switching between LHT/RHT countries in the
    // same session always uses the correct setting. Defaults to true (LHT) as a
    // safe fallback if the country cannot be resolved yet.
    let isLeftHandTraffic = true;

    // Detects LHT/RHT for the current edit context.
    // Primary:  segment → primaryStreetId → cityId → countryId → isLeftHandTraffic.
    //           Tied to the segment's own data — reliable in cross-border areas.
    // Fallback: sdk.DataModel.Countries.getTopCountry() — viewport-based, used at
    //           init before any segment is available, or if the chain is incomplete.
    function detectTrafficSide(segmentId) {
        // Primary: walk segment → street → city → country.
        if (segmentId != null) {
            try {
                const seg = sdk.DataModel.Segments.getById({ segmentId });
                if (seg?.primaryStreetId) {
                    const street = sdk.DataModel.Streets.getById({ streetId: seg.primaryStreetId });
                    if (street?.cityId) {
                        const city = sdk.DataModel.Cities.getById({ cityId: street.cityId });
                        if (city?.countryId) {
                            const country = sdk.DataModel.Countries.getById({ countryId: city.countryId });
                            if (country != null) {
                                isLeftHandTraffic = country.isLeftHandTraffic ?? true;
                                console.debug('[WAZEParallel] Traffic side:', isLeftHandTraffic ? 'LHT' : 'RHT', '— country (from segment chain):', country.name);
                                return;
                            }
                        }
                    }
                }
            } catch (e) {
                console.warn('[WAZEParallel] Segment-chain country detection failed:', e);
            }
        }
        // Fallback: top country for the current map view.
        try {
            const topCountry = sdk.DataModel.Countries.getTopCountry();
            if (topCountry != null) {
                isLeftHandTraffic = topCountry.isLeftHandTraffic ?? true;
                console.debug('[WAZEParallel] Traffic side:', isLeftHandTraffic ? 'LHT' : 'RHT', '— country (from getTopCountry):', topCountry.name);
                return;
            }
        } catch (e) {
            console.warn('[WAZEParallel] getTopCountry() failed:', e);
        }
        console.warn('[WAZEParallel] Could not detect traffic side — keeping', isLeftHandTraffic ? 'LHT' : 'RHT');
    }

    // ─── Bootstrap ───────────────────────────────────────────────────────────
    function bootstrap() {
        // SDK pattern: use unsafeWindow because @grant directives are present
        unsafeWindow.SDK_INITIALIZED.then(initSdk);
    }

    function initSdk() {
        sdk = unsafeWindow.getWmeSdk({ scriptId: 'WAZEParallel-segments-mod-np', scriptName: scriptName });
        sdk.Events.once({ eventName: 'wme-ready' }).then(init);
    }

    function init() {
        // Best-effort early detection — no segment yet, falls back to getTopCountry().
        detectTrafficSide(null);
        // Register for selection change events (SDK equivalent of selectionManager.events.register)
        sdk.Events.on({ eventName: 'wme-selection-changed', eventHandler: onSelectionChanged });
        // Run once on startup in case something is already selected
        onSelectionChanged();
    }

    // ─── Selection handler ───────────────────────────────────────────────────
    function onSelectionChanged() {
        setTimeout(() => {
            const selection = sdk.Editing.getSelection();
            if (selection && selection.objectType === 'segment') {
                myTimer();
                insertButtons();
            }
        }, 300);
    }

    // ─── myTimer: inject A→B / B→A direction copy buttons ───────────────────
    function myTimer() {
        if (document.getElementById('signsroad')) return;

        const signsroad = document.createElement('div');
        signsroad.id = 'signsroad';

        const btnAB = document.createElement('button');
        btnAB.innerHTML = 'A->B';
        btnAB.id = 'btnAB';
        btnAB.style.cssText = 'height: 20px;font-size:11px';
        btnAB.onclick = function () {
            const selection = sdk.Editing.getSelection();
            if (!selection || selection.objectType !== 'segment') return;
            const segId = selection.ids[0];
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg || !seg.isAtoB) return;  // isAtoB = fwdDirection only
            const center = sdk.Map.getMapCenter();
            const text = center.lon.toFixed(6) + ',' + center.lat.toFixed(6) +
                '|' + segId + '|TRUE|' + seg.fromNodeId + '|' + seg.toNodeId;
            GM_setClipboard(text);
        };

        const btnBA = document.createElement('button');
        btnBA.innerHTML = 'B->A';
        btnBA.id = 'btnBA';
        btnBA.style.cssText = 'height: 20px;font-size:11px';
        btnBA.onclick = function () {
            const selection = sdk.Editing.getSelection();
            if (!selection || selection.objectType !== 'segment') return;
            const segId = selection.ids[0];
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg || !seg.isBtoA) return;  // isBtoA = revDirection only
            const center = sdk.Map.getMapCenter();
            const text = center.lon.toFixed(6) + ',' + center.lat.toFixed(6) +
                '|' + segId + '|FALSE|' + seg.toNodeId + '|' + seg.fromNodeId;
            GM_setClipboard(text);
        };

        const divDirectionBtns = document.createElement('div');
        divDirectionBtns.id = 'divDirectionBtns';
        divDirectionBtns.appendChild(btnAB);
        divDirectionBtns.appendChild(btnBA);

        const divLandmarkScript = document.createElement('div');
        divLandmarkScript.id = 'divLandmarkScript';
        divLandmarkScript.style.cssText = 'float:left;';
        divLandmarkScript.appendChild(signsroad);
        divLandmarkScript.appendChild(divDirectionBtns);

        const editGeneral = document.querySelector('div #segment-edit-general');
        if (editGeneral) {
            editGeneral.prepend(divLandmarkScript);
            divDirectionBtns.style.display = 'none';
        }
    }

    // ─── insertButtons: inject split segment UI ───────────────────────────────
    function insertButtons() {

        const selection = sdk.Editing.getSelection();
        if (!selection || selection.objectType !== 'segment' || selection.ids.length === 0) return;

        // Check exit conditions across all selected segments
        let exit = false;
        for (const segId of selection.ids) {
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg) continue;
            // fwdLaneCount / revLaneCount → fromLanesInfo / toLanesInfo lane counts
            const fwdLanes = seg.fromLanesInfo ? seg.fromLanesInfo.laneCount : 0;
            const revLanes = seg.toLanesInfo ? seg.toLanesInfo.laneCount : 0;
            if (fwdLanes !== 0 || revLanes !== 0) { exit = true; break; }
            // Must be strictly two-way — use SDK Segment.isTwoWay property
            if (!seg.isTwoWay) { exit = true; break; }
            if (pedestrianRoadIds.includes(seg.roadType)) { exit = true; break; }
        }

        if (exit) return;
        if (document.getElementById('split-segment') !== null) return;

        const strMeters = language.strMeters;

        const btn1 = document.createElement('wz-button');
        btn1.setAttribute('color', 'secondary');
        btn1.setAttribute('size', 'sm');
        btn1.style.cssText = 'float:right;margin-top: 5px;';
        btn1.textContent = language.btnSplit;
        btn1.addEventListener('click', mainSplitSegments);

        const selSegmentsDistance = document.createElement('wz-select');
        selSegmentsDistance.id = 'segmentsDistance';
        selSegmentsDistance.setAttribute('data-type', 'numeric');
        selSegmentsDistance.setAttribute('value', '5');
        selSegmentsDistance.style.cssText = 'width: 45%;float:left;';

        const distanceOptions = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 19, 21, 23, 25, 27, 30, 32, 35, 37, 40, 42, 45];
        for (const val of distanceOptions) {
            const opt = document.createElement('wz-option');
            opt.setAttribute('value', String(val));
            opt.textContent = `${val} ${strMeters}`;
            selSegmentsDistance.appendChild(opt);
        }

        const label = document.createElement('wz-label');
        label.textContent = language.strDistance;

        const divGroup1 = document.createElement('div');
        divGroup1.appendChild(label);
        divGroup1.appendChild(selSegmentsDistance);
        divGroup1.appendChild(btn1);

        const cnt = document.createElement('div');
        cnt.id = 'split-segment';
        cnt.className = 'form-group';
        cnt.style.cssText = 'display: flex;';
        cnt.appendChild(divGroup1);

        const attrForm = document.querySelector('#segment-edit-general .attributes-form');
        if (attrForm) attrForm.insertAdjacentElement('afterend', cnt);

        // Restore saved distance preference
        const savedDist = localStorage.getItem('metersSplitSegment');
        if (savedDist) selSegmentsDistance.setAttribute('value', savedDist);

        selSegmentsDistance.addEventListener('change', function () {
            localStorage.setItem('metersSplitSegment', selSegmentsDistance.value);
        });
    }

    // ─── orderSegments: sort selected segment IDs from one end to the other ───
    function orderSegments() {
        const selection = sdk.Editing.getSelection();
        if (!selection || selection.objectType !== 'segment') return [];
        const selectedIds = selection.ids;
        console.debug('[WAZEParallel] orderSegments: total selected =', selectedIds.length, 'ids =', selectedIds);

        const nodeOccurrences = [];
        for (const segId of selectedIds) {
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg) { console.warn('[WAZEParallel] orderSegments: segment not found in model:', segId); continue; }
            console.debug(`[WAZEParallel] orderSegments: seg ${segId} fromNode=${seg.fromNodeId} toNode=${seg.toNodeId}`);
            if (nodeOccurrences.length > 0) {
                let fromExists = false;
                let toExists = false;
                for (const entry of nodeOccurrences) {
                    if (entry[0] === seg.fromNodeId) { entry[1] = 2; fromExists = true; }
                    if (entry[0] === seg.toNodeId)   { entry[1] = 2; toExists = true; }
                }
                if (!fromExists) nodeOccurrences.push([seg.fromNodeId, 1]);
                if (!toExists)   nodeOccurrences.push([seg.toNodeId, 1]);
            } else {
                nodeOccurrences.push([seg.fromNodeId, 1]);
                nodeOccurrences.push([seg.toNodeId, 1]);
            }
        }
        console.debug('[WAZEParallel] orderSegments: node occurrence map =', nodeOccurrences);

        let nextNodeId = null;
        for (const entry of nodeOccurrences) {
            if (entry[1] === 1) { nextNodeId = entry[0]; break; }
        }
        console.debug('[WAZEParallel] orderSegments: start node =', nextNodeId);

        if (nextNodeId === null) {
            // Circular selection or disconnected — fall back to original order
            console.warn('[WAZEParallel] orderSegments: no endpoint node found (circular?), using original order');
            return [...selectedIds];
        }

        const orderedSegIds = [];
        const remaining = new Set(selectedIds);
        let loopGuard = 0;
        while (remaining.size > 0 && loopGuard < selectedIds.length * 2) {
            loopGuard++;
            let found = false;
            for (const segId of remaining) {
                const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
                if (!seg) { remaining.delete(segId); found = true; break; }
                if (seg.fromNodeId === nextNodeId) {
                    console.debug(`[WAZEParallel] orderSegments: placed seg ${segId} (fromNode match, next=${seg.toNodeId})`);
                    orderedSegIds.push(segId);
                    nextNodeId = seg.toNodeId;
                    remaining.delete(segId);
                    found = true;
                    break;
                } else if (seg.toNodeId === nextNodeId) {
                    console.debug(`[WAZEParallel] orderSegments: placed seg ${segId} (toNode match, next=${seg.fromNodeId})`);
                    orderedSegIds.push(segId);
                    nextNodeId = seg.fromNodeId;
                    remaining.delete(segId);
                    found = true;
                    break;
                }
            }
            if (!found) {
                console.warn('[WAZEParallel] orderSegments: chain broken at node', nextNodeId, '— remaining unplaced:', [...remaining]);
                break;
            }
        }
        console.debug('[WAZEParallel] orderSegments: result =', orderedSegIds);
        return orderedSegIds;
    }

    // ─── mainSplitSegments: entry point for split button ─────────────────────
    function mainSplitSegments() {
        const selection = sdk.Editing.getSelection();
        if (selection && selection.ids.length > 1) {
            WazeToastr.Alerts.confirm(
                scriptName,
                language.strSelMoreSeg,
                function () { executeSplit(); },
                function () { return; },
                "Continue",
                "Cancel"
            );
            return;
        }
        executeSplit();
    }

    // ─── executeSplit: core split logic ──────────────────────────────────────
    // For single segment: pure WME SDK.
    // For multiple connected segments: SDK for split+geometry+direction, but
    // legacy Waze/Action/AddNode (with deferred-dispatch wrapper) to create the
    // inter-segment junction nodes (no SDK splitSegment equivalent for
    // multi-seg junctions). Turn-allowance uses sdk.DataModel.Nodes.allowNodeTurns
    // for both single and multi-segment paths.
    //
    // CRITICAL: All AddNode actions MUST be collected and dispatched AFTER the
    // full createSegments loop. Dispatching AddNode inside the loop corrupts the
    // action-manager state before the next splitSegment call, causing segments
    // after the first to fail silently.
    function executeSplit() {
        const distance = parseFloat(document.getElementById('segmentsDistance').value);
        console.debug('[WAZEParallel] executeSplit start — distance:', distance);

        last_node_A = null;
        last_node_B = null;
        last_coord_left_first = null;
        last_coord_left_last = null;
        last_coord_right_first = null;
        last_coord_right_last = null;
        baseDirection = null;

        const orderedSegIds = orderSegments();
        console.debug('[WAZEParallel] executeSplit: ordered segment IDs =', orderedSegIds,
            '(', orderedSegIds.length, 'of', sdk.Editing.getSelection()?.ids?.length, 'selected)');

        if (orderedSegIds.length === 0) {
            console.warn('[WAZEParallel] executeSplit: nothing to split');
            return;
        }

        // Lazy traffic-side detection — use first segment for accurate per-segment chain lookup.
        detectTrafficSide(orderedSegIds[0]);
        console.debug('[WAZEParallel] executeSplit: isLeftHandTraffic =', isLeftHandTraffic);

        const isMultiSeg = orderedSegIds.length > 1;

        // AddNode has no SDK equivalent — must use legacy require.
        // ModifyAllConnections → sdk.DataModel.Nodes.allowNodeTurns.
        // UpdateObject(fwdTurnsLocked/revTurnsLocked) is NOT needed: those are UI-only
        // verification flags; allowNodeTurns already sets the final turn state correctly.
        let AddNodeLegacy = null;
        if (isMultiSeg) {
            console.debug('[WAZEParallel] Multi-segment mode: loading legacy AddNode');
            try {
                AddNodeLegacy = require('Waze/Action/AddNode');
                console.debug('[WAZEParallel] Legacy AddNode loaded OK');
            } catch (e) {
                console.error('[WAZEParallel] Failed to load legacy AddNode:', e);
            }
        }

        // AddNodeWrapper — mirrors the legacy version exactly.
        // Delays getAffectedUniqueIds until the node actually exists, preventing
        // the action manager from throwing when the node hasn't been created yet.
        function AddNodeWrapper(point, segments) {
            const base = new AddNodeLegacy(point, segments);
            const origGetAffected = base.getAffectedUniqueIds.bind(base);
            base.getAffectedUniqueIds = function (dataModel) {
                return this.node ? origGetAffected(dataModel) : [];
            };
            return base;
        }

        const leftSegIds = [];
        const rightSegIds = [];
        let connMode = null;

        // Collect all actions for post-split dispatch — mirroring actionsToAdd in legacy.
        // Dispatching these INSIDE the loop would corrupt the action manager before the
        // next splitSegment call.
        const actionsToAdd = [];

        for (let i = 0; i < orderedSegIds.length; i++) {
            const idsegment = orderedSegIds[i];
            const segment = sdk.DataModel.Segments.getById({ segmentId: idsegment });
            if (!segment) {
                console.warn('[WAZEParallel] executeSplit: segment not found in model (may already be split):', idsegment);
                continue;
            }

            // Determine how this segment connects to the previous one (by shared node ID)
            if (last_node_A !== null && last_node_B !== null) {
                if (last_node_A === segment.toNodeId)   connMode = 'AB';
                if (last_node_B === segment.fromNodeId) connMode = 'BA';
                if (last_node_A === segment.fromNodeId) connMode = 'AA';
                if (last_node_B === segment.toNodeId)   connMode = 'BB';
                if (i === 1) {
                    if (connMode === 'AB' || connMode === 'AA') baseDirection = 'BA';
                    if (connMode === 'BA' || connMode === 'BB') baseDirection = 'AB';
                    console.debug('[WAZEParallel] executeSplit: baseDirection set to', baseDirection);
                }
            }

            console.debug(`[WAZEParallel] Segment ${i}: id=${idsegment} connMode=${connMode}  fromNode=${segment.fromNodeId} toNode=${segment.toNodeId}  lastA=${last_node_A} lastB=${last_node_B}`);

            if (connMode === 'AA' || connMode === 'BB') {
                last_node_A = segment.toNodeId;
                last_node_B = segment.fromNodeId;
            } else {
                last_node_A = segment.fromNodeId;
                last_node_B = segment.toNodeId;
            }

            const segments = createSegments(segment, distance, connMode);
            if (!segments) {
                console.warn('[WAZEParallel] executeSplit: createSegments returned null for segment', idsegment);
                continue;
            }
            console.debug(`[WAZEParallel] Segment ${i} split → left=${segments[0]} right=${segments[1]}`);
            console.debug('[WAZEParallel] Coord cache after split:',
                'L[0]:', JSON.stringify(last_coord_left_first),
                'L[-1]:', JSON.stringify(last_coord_left_last),
                'R[0]:', JSON.stringify(last_coord_right_first),
                'R[-1]:', JSON.stringify(last_coord_right_last));

            if (i > 0 && isMultiSeg) {
                const prevLeftId  = leftSegIds[leftSegIds.length - 1];
                const prevRightId = rightSegIds[rightSegIds.length - 1];

                // SDK: read junction coordinates from updated geometry — GeoJSON-native,
                // no W.userscripts.toGeoJSONGeometry conversion needed.
                // For BA/BB: curr-left first point; curr-right last point.
                // For AB/AA: curr-left last point; curr-right first point.
                const currLeftSdk  = sdk.DataModel.Segments.getById({ segmentId: segments[0] });
                const currRightSdk = sdk.DataModel.Segments.getById({ segmentId: segments[1] });
                // Legacy WME objects still required as participants for the AddNode action.
                const prevLeftWme  = W.model.segments.getObjectById(prevLeftId);
                const currLeftWme  = W.model.segments.getObjectById(segments[0]);
                const prevRightWme = W.model.segments.getObjectById(prevRightId);
                const currRightWme = W.model.segments.getObjectById(segments[1]);

                let leftCoord  = null;
                let rightCoord = null;

                if (currLeftSdk && currRightSdk) {
                    const leftCoords  = currLeftSdk.geometry.coordinates;
                    const rightCoords = currRightSdk.geometry.coordinates;
                    if (connMode === 'BA' || connMode === 'BB') {
                        leftCoord  = { type: 'Point', coordinates: leftCoords[0] };
                        rightCoord = { type: 'Point', coordinates: rightCoords[rightCoords.length - 1] };
                    } else { // AB, AA
                        leftCoord  = { type: 'Point', coordinates: leftCoords[leftCoords.length - 1] };
                        rightCoord = { type: 'Point', coordinates: rightCoords[0] };
                    }
                } else {
                    // Fallback to cached coords if SDK can't find the segment yet
                    console.warn('[WAZEParallel] SDK segment not found for coord read, falling back to cache. left:', segments[0], 'right:', segments[1]);
                    if (connMode === 'BA' || connMode === 'BB') {
                        leftCoord  = { type: 'Point', coordinates: last_coord_left_first };
                        rightCoord = { type: 'Point', coordinates: last_coord_right_last };
                    } else {
                        leftCoord  = { type: 'Point', coordinates: last_coord_left_last };
                        rightCoord = { type: 'Point', coordinates: last_coord_right_first };
                    }
                }

                console.debug(`[WAZEParallel] AddNode LEFT  coord=${JSON.stringify(leftCoord)}  segs: prev=${prevLeftId} curr=${segments[0]}  wme: prev=${!!prevLeftWme} curr=${!!currLeftWme}`);
                console.debug(`[WAZEParallel] AddNode RIGHT coord=${JSON.stringify(rightCoord)} segs: prev=${prevRightId} curr=${segments[1]}  wme: prev=${!!prevRightWme} curr=${!!currRightWme}`);

                if (prevLeftWme && currLeftWme && leftCoord) {
                    actionsToAdd.push(AddNodeWrapper(leftCoord, [prevLeftWme, currLeftWme]));
                } else {
                    console.warn('[WAZEParallel] AddNode LEFT skipped — missing:', { prevLeftWme: !!prevLeftWme, currLeftWme: !!currLeftWme, leftCoord });
                }
                if (prevRightWme && currRightWme && rightCoord) {
                    actionsToAdd.push(AddNodeWrapper(rightCoord, [prevRightWme, currRightWme]));
                } else {
                    console.warn('[WAZEParallel] AddNode RIGHT skipped — missing:', { prevRightWme: !!prevRightWme, currRightWme: !!currRightWme, rightCoord });
                }
            }

            leftSegIds.push(segments[0]);
            rightSegIds.push(segments[1]);
        }

        // ── Phase 2: dispatch all AddNode actions now that all segments are split.
        if (isMultiSeg) {
            console.debug(`[WAZEParallel] Dispatching ${actionsToAdd.length} AddNode action(s)`);
            actionsToAdd.forEach(a => W.model.actionManager.add(a));

            // SDK: allowNodeTurns replaces legacy ModifyAllConnections.
            console.debug('[WAZEParallel] Allowing turns at all nodes of produced segments via SDK');
            for (const segId of [...leftSegIds, ...rightSegIds]) {
                const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
                if (!seg) { console.warn('[WAZEParallel] allowNodeTurns: SDK segment missing for seg', segId); continue; }
                if (seg.fromNodeId !== null) sdk.DataModel.Nodes.allowNodeTurns({ nodeId: seg.fromNodeId, allow: true });
                if (seg.toNodeId   !== null) sdk.DataModel.Nodes.allowNodeTurns({ nodeId: seg.toNodeId,   allow: true });
            }
        } else {
            // Single segment — pure SDK turn-allowance.
            for (const segId of [...leftSegIds, ...rightSegIds]) {
                const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
                if (!seg) continue;
                if (seg.fromNodeId !== null) sdk.DataModel.Nodes.allowNodeTurns({ nodeId: seg.fromNodeId, allow: true });
                if (seg.toNodeId   !== null) sdk.DataModel.Nodes.allowNodeTurns({ nodeId: seg.toNodeId,   allow: true });
            }
        }

        console.debug('[WAZEParallel] executeSplit done — left segs:', leftSegIds, '/ right segs:', rightSegIds);
        WazeToastr.Alerts.success(
            scriptName,
            `Successfully split ${leftSegIds.length} segment${leftSegIds.length > 1 ? 's' : ''} with ${distance}m gap!`
        );
    }

    // ─── createSegments: split one segment and compute offset geometries ──────
    // 
    // NOTE: OpenLayers geometry operations (rotate, resize, clone on OL.Geometry.Point)
    // are replaced here with turf.js equivalents.
    // turf works in WGS84 (lon/lat). WME SDK segment.geometry is a GeoJSON LineString
    // already in WGS84.
    //
    function createSegments(sel, displacement, connMode) {
        console.debug('[WAZEParallel] createSegments: segId=', sel.id, 'displacement=', displacement, 'connMode=', connMode);
        // SDK: segment.geometry is already a GeoJSON LineString { type:'LineString', coordinates:[[lon,lat],...] }
        const geomCoords = sel.geometry.coordinates;

        // Simplify geometry: for performance, keep only significant vertices.
        // turf.simplify works in WGS84 (lon/lat degrees).
        const lineFeature = turf.lineString(geomCoords);
        // tolerance in degrees ≈ 0.000001 is ~0.1m; 0.00001 is ~1m — use small value to preserve shape
        const simplified = turf.simplify(lineFeature, { tolerance: 0.000001, highQuality: true });
        const streetCoords = simplified.geometry.coordinates; // [[lon,lat], ...]

        let leftPoints = null;
        let rightPoints = null;
        let prevLeftEq = null;
        let prevRightEq = null;
        let leftPa, rightPa, leftPb, rightPb;

        // displacement is in meters; convert to displacement/2 for each side
        const halfD = displacement / 2;

        for (let i = 0; i < streetCoords.length - 1; i++) {
            const pa = streetCoords[i];   // [lon, lat]
            const pb = streetCoords[i + 1]; // [lon, lat]

            // Bearing from pa to pb
            const bearing = turf.bearing(turf.point(pa), turf.point(pb));

            // LHT (driving on left): left carriageway = bearing-90, right = bearing+90.
            // RHT (driving on right): sides are physically swapped — invert the offsets.
            const bearingLeft  = isLeftHandTraffic ? (bearing - 90 + 360) % 360 : (bearing + 90) % 360;
            const bearingRight = isLeftHandTraffic ? (bearing + 90) % 360 : (bearing - 90 + 360) % 360;

            // Distance along segment for offset endpoints
            const segLenKm = turf.distance(turf.point(pa), turf.point(pb)); // km
            const halfDKm = halfD / 1000;

            // Compute offset points at distance halfD from each vertex, perpendicular to bearing
            // "Extend" pa backward along bearing by halfD to get offset origin, then rotate
            const leftPaPoint  = turf.destination(turf.point(pa), halfDKm, bearingLeft,  { units: 'kilometers' });
            const rightPaPoint = turf.destination(turf.point(pa), halfDKm, bearingRight, { units: 'kilometers' });
            const leftPbPoint  = turf.destination(turf.point(pb), halfDKm, bearingLeft,  { units: 'kilometers' });
            const rightPbPoint = turf.destination(turf.point(pb), halfDKm, bearingRight, { units: 'kilometers' });

            leftPa  = leftPaPoint.geometry.coordinates;
            rightPa = rightPaPoint.geometry.coordinates;
            leftPb  = leftPbPoint.geometry.coordinates;
            rightPb = rightPbPoint.geometry.coordinates;

            // Line equations for intersection calculation (in geographic coords)
            const leftEq  = getEquation({ x1: leftPa[0],  y1: leftPa[1],  x2: leftPb[0],  y2: leftPb[1] });
            const rightEq = getEquation({ x1: rightPa[0], y1: rightPa[1], x2: rightPb[0], y2: rightPb[1] });

            if (leftPoints === null && rightPoints === null) {
                leftPoints  = [leftPa];
                rightPoints = [rightPa];
            } else {
                const li = intersectX(leftEq, prevLeftEq);
                const ri = intersectX(rightEq, prevRightEq);

                if (li && ri) {
                    leftPoints.unshift(li);
                    rightPoints.push(ri);
                    if (i === 0) {
                        leftPoints  = [li];
                        rightPoints = [ri];
                    }
                } else {
                    leftPoints.unshift([...leftPb]);
                    rightPoints.push([...rightPb]);
                    if (i === 0) {
                        leftPoints  = [[...leftPb]];
                        rightPoints = [[...rightPb]];
                    }
                }
            }

            prevLeftEq  = leftEq;
            prevRightEq = rightEq;
        }

        // Append final point
        leftPoints.push([...leftPb]);
        rightPoints.push([...rightPb]);

        // Rotate left array so first→last ordering is consistent
        leftPoints.unshift(leftPoints[leftPoints.length - 1]);
        leftPoints.pop();

        // Split the original segment at midpoint using SDK
        console.debug('[WAZEParallel] createSegments: calling SplitSegment, leftPoints=', leftPoints.length, 'rightPoints=', rightPoints.length);
        const splitIds = SplitSegment(sel);
        if (!splitIds) return null;

        // Reverse both so they flow A→B
        leftPoints  = leftPoints.reverse();
        rightPoints = rightPoints.reverse();

        // For AA/BB connection modes, swap left/right
        if (connMode === "AA" || connMode === "BB") {
            const aux  = leftPoints;
            leftPoints  = rightPoints;
            rightPoints = aux;
        }

        // Adjust endpoints to match previous iteration's cached connector coords
        if (last_coord_left_first !== null && last_coord_left_last !== null &&
            last_coord_right_first !== null && last_coord_right_last !== null) {

            if (connMode === "AB") {
                leftPoints[leftPoints.length - 1]  = last_coord_left_first;
                rightPoints[0]                     = last_coord_right_last;
            }
            if (connMode === "BA") {
                leftPoints[0]                      = last_coord_left_last;
                rightPoints[rightPoints.length - 1] = last_coord_right_first;
            }
            if (connMode === "AA") {
                leftPoints[leftPoints.length - 1]  = last_coord_left_first;
                rightPoints[0]                     = last_coord_right_last;
            }
            if (connMode === "BB") {
                leftPoints[0]                      = last_coord_left_last;
                rightPoints[rightPoints.length - 1] = last_coord_right_first;
            }
        }

        // Cache connector coords for next iteration
        last_coord_left_first  = leftPoints[0];
        last_coord_left_last   = leftPoints[leftPoints.length - 1];
        last_coord_right_first = rightPoints[0];
        last_coord_right_last  = rightPoints[rightPoints.length - 1];

        // Build GeoJSON LineString geometries for SDK updateSegment
        const newGeomLeft  = { type: 'LineString', coordinates: leftPoints };
        const newGeomRight = { type: 'LineString', coordinates: rightPoints };

        const leftSegId  = splitIds[0];
        const rightSegId = splitIds[1];

        console.debug('[WAZEParallel] createSegments: updateSegment geometry left=', leftSegId, 'right=', rightSegId);
        // SDK: updateSegment with new geometry — replaces UpdateSegmentGeometry action
        sdk.DataModel.Segments.updateSegment({ segmentId: leftSegId,  geometry: newGeomLeft });
        sdk.DataModel.Segments.updateSegment({ segmentId: rightSegId, geometry: newGeomRight });

        // Set direction: one-way A→B for both segments
        // SDK SegmentDirection values: 'A_TO_B' | 'B_TO_A' | 'TWO_WAY'
        const leftSeg  = sdk.DataModel.Segments.getById({ segmentId: leftSegId });
        const rightSeg = sdk.DataModel.Segments.getById({ segmentId: rightSegId });

        if (connMode === "AA" || connMode === "BB") {
            // Swap speed limits when direction is flipped
            if (leftSeg) {
                sdk.DataModel.Segments.updateSegment({
                    segmentId: leftSegId,
                    direction: 'A_TO_B',
                    fwdSpeedLimit: leftSeg.revSpeedLimit,
                    revSpeedLimit: leftSeg.fwdSpeedLimit
                });
            }
            if (rightSeg) {
                sdk.DataModel.Segments.updateSegment({
                    segmentId: rightSegId,
                    direction: 'A_TO_B',
                    fwdSpeedLimit: rightSeg.revSpeedLimit,
                    revSpeedLimit: rightSeg.fwdSpeedLimit
                });
            }
        } else {
            sdk.DataModel.Segments.updateSegment({ segmentId: leftSegId,  direction: 'A_TO_B' });
            sdk.DataModel.Segments.updateSegment({ segmentId: rightSegId, direction: 'A_TO_B' });
        }

        console.debug('[WAZEParallel] createSegments done — returning', splitIds);
        return splitIds;
    }
    // Replaces legacy Waze/Action/SplitSegments require() pattern.
    // SDK: DataModel.Segments.splitSegment({ segmentId, splitPoint: GeoJSON Point })
    //
    function SplitSegment(seg) {
        console.debug('[WAZEParallel] SplitSegment: segId=', seg.id, 'coords=', seg.geometry.coordinates.length);
        if (!sdk.DataModel.Segments.hasPermissions({ segmentId: seg.id })) {
            console.warn('[WAZEParallel] SplitSegment: no permissions for segment', seg.id);
            return undefined;
        }

        const coords = seg.geometry.coordinates;
        if (!coords || coords.length < 2) return undefined;

        // Ensure at least 3 points (insert midpoint if only 2 vertices)
        let workCoords = [...coords];
        if (workCoords.length === 2) {
            const mid = [
                (workCoords[0][0] + workCoords[1][0]) / 2,
                (workCoords[0][1] + workCoords[1][1]) / 2
            ];
            workCoords = [workCoords[0], mid, workCoords[1]];
            // Update geometry first so split point is valid
            sdk.DataModel.Segments.updateSegment({
                segmentId: seg.id,
                geometry: { type: 'LineString', coordinates: workCoords }
            });
        }

        // Split at the middle vertex
        const midIdx = Math.ceil(workCoords.length / 2 - 1);
        const splitPoint = { type: 'Point', coordinates: workCoords[midIdx] };

        const [id1, id2] = sdk.DataModel.Segments.splitSegment({ segmentId: seg.id, splitPoint });
        return [id1, id2];
    }

    // ─── Geometry helpers ────────────────────────────────────────────────────
    // These work in geographic (lon/lat) coordinate space.
    // NOTE: These are the same line-equation helpers as the legacy code —
    // they cannot be replaced by SDK methods as the SDK has no geometry math APIs.
    // Using turf for actual point-offset operations above is the migration path.

    function getEquation(segment) {
        if (segment.x2 === segment.x1) return { x: segment.x1 };
        const slope = (segment.y2 - segment.y1) / (segment.x2 - segment.x1);
        const offset = segment.y1 - slope * segment.x1;
        return { slope, offset };
    }

    function intersectX(eqa, eqb) {
        if (typeof eqa.slope === 'number' && typeof eqb.slope === 'number') {
            if (eqa.slope === eqb.slope) return null;
            const ix = (eqb.offset - eqa.offset) / (eqa.slope - eqb.slope);
            const iy = eqa.slope * ix + eqa.offset;
            return [ix, iy]; // [lon, lat]
        } else if (typeof eqa.x === 'number') {
            return [eqa.x, eqb.slope * eqa.x + eqb.offset];
        } else if (typeof eqb.x === 'number') {
            return [eqb.x, eqa.slope * eqb.x + eqa.offset];
        }
        return null;
    }

    // ─── Script update monitor ────────────────────────────────────────────────
    function scriptupdatemonitor() {
        if (WazeToastr?.Ready) {
            const updateMonitor = new WazeToastr.Alerts.ScriptUpdateMonitor(scriptName, scriptVersion, downloadUrl, GM_xmlhttpRequest);
            updateMonitor.start(2, true);
            WazeToastr.Interface.ShowScriptUpdate(scriptName, scriptVersion, updateMessage, downloadUrl, forumURL);
        } else {
            setTimeout(scriptupdatemonitor, 250);
        }
    }

    scriptupdatemonitor();
    bootstrap();

})();

/* Changelog 2026.03.31.01 - Replaced broken segment-address country detection with sdk.Countries.getTopCountry().
                 The SDK Segment interface has no .address property, so seg?.address?.country was
                 always undefined. detectTrafficSide() now calls sdk.Countries.getTopCountry()
                 directly and reads isLeftHandTraffic from the returned Country object.
                 Both LHT and RHT countries are now correctly detected and carriageways are
                 placed on the proper physical sides of the road.
 2026.03.30.08 - Fixed traffic-side detection caching bug: isTrafficSideDetected flag caused RHT
                 countries to be treated as LHT when the editor was previously used in an
                 LHT country in the same session. Removed the flag so detection always
                 re-runs per split. Segment address is now checked first (most accurate);
                 sdk.Countries.getTopCountry() is the fallback. Country name is now logged.
 2026.03.30.07 - Added left-hand vs right-hand traffic detection via sdk.Countries.getTopCountry().
                 Bearing offsets in createSegments() are now swapped for RHT countries so
                 carriageways are placed on the correct physical sides of the road.
 2026.03.30.06 - Removed getPermalink(): clipboard output is not consumed by any external tool,
                 so the permalink field is unnecessary. Removed sdk.Map.getPermalink() call,
                 async/await from direction-copy button handlers, and the helper function.
 2026.03.30.04 - Removed legacy require('Waze/Action/UpdateObject') and fwdTurnsLocked /
                 revTurnsLocked actions: these are UI-only verification flags that do not
                 affect functional correctness. sdk.DataModel.Nodes.allowNodeTurns already
                 sets the final turn state correctly. AddNode is now the only remaining
                 legacy action (no SDK splitSegment equivalent for multi-seg junctions). 2026.03.30.03 - Replaced legacy ModifyAllConnections with sdk.DataModel.Nodes.allowNodeTurns
                 for multi-segment mode (now consistent with single-segment path).
                 Replaced W.model.segments.getObjectById + .attributes.geometry.components +
                 W.userscripts.toGeoJSONGeometry for junction coord reading with
                 sdk.DataModel.Segments.getById + .geometry.coordinates (GeoJSON-native).
                 W.model.segments.getObjectById retained only where AddNode / UpdateObject
                 legacy actions require internal WME objects.
 2026.03.30.02 - Fixed multi-segment split: only the first segment was being split.
                 Fixes:
                   - orderSegments: loop now uses a Set + loop-guard to avoid breaking
                     the chain on disconnected or already-visited segments.
                   - executeSplit: added legacy require('Waze/Action/UpdateObject') to
                     lock turns (fwdTurnsLocked/revTurnsLocked) on each produced segment
                     before AddNode is dispatched — required for junction nodes to form.
                   - AddNode junction coordinates now read directly from the updated WME
                     segment geometry (.attributes.geometry.components) instead of
                     the cached coord variables, matching legacy behaviour exactly.
                   - All collected actions (AddNode + UpdateObject) dispatched together
                     after the split loop, before ModifyAllConnections.
                 Added verbose console.debug logs throughout for easier diagnosis.
 2026.03.30.01 - Migrated from legacy WME API to WME SDK.
                 Geometry math migrated from OpenLayers to turf.js.
                 clipboard copy migrated from execCommand to GM_setClipboard.
*/
