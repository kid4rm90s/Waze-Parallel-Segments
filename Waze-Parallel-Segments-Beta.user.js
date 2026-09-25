// ==UserScript==
// @name         Waze Parallel Segments Beta
// @version      2026.09.25.10
// @description  Splits two-way segments into parallel one-way carriageways, and adjusts existing one-way segments to be parallel to a user-drawn guide line. Supports both left-hand and right-hand traffic countries.
// @author       kid4rm90s & copilot (original author J0N4S13)
// @include 	 /^https:\/\/(www|beta)\.waze\.com\/(?!user\/)(.{2,6}\/)?editor.*$/
// @exclude      https://www.waze.com/user/*editor/*
// @exclude      https://www.waze.com/*/user/*editor/*
// @connect      greasyfork.org
// @connect      raw.githubusercontent.com
// @grant        GM_xmlhttpRequest
// @grant        GM_setClipboard
// @grant        unsafeWindow
// @require 	 https://greasyfork.org/scripts/560385/code/WazeToastr.js
// @require      https://cdn.jsdelivr.net/npm/@turf/turf@7/turf.min.js
// @require      https://cdn.jsdelivr.net/gh/TheEditorX/wme-sdk-plus@0b212bcaddf3e7983b28b220d120e0dd687a74d1/wme-sdk-plus.js
// @namespace    https://greasyfork.org/users/1087400
/* 
Original Author Thanks : J0N4S13 (jonathanserrario@gmail.com)
Migrated to WME SDK by kid4rm90s
*/
// @downloadURL https://raw.githubusercontent.com/kid4rm90s/Waze-Parallel-Segments/Beta/Waze-Parallel-Segments-Beta.user.js
// @updateURL https://raw.githubusercontent.com/kid4rm90s/Waze-Parallel-Segments/Beta/Waze-Parallel-Segments-Beta.user.js

// ==/UserScript== 
/**To Do */
// Select segment at one side and another same segment at the other side and it will select all the segments in between.
(function () {
    'use strict';

    // ─── Script metadata ────────────────────────────────────────────────────────
    const updateMessage = `<strong>Whats new?</strong>.<br>` +
        `Added "Make it parallel" feature: select one-way segments, draw a guide line between them without crossing, and they become parallel at the specified distance.<br><br>` +
        `<em>Enjoy Mapping!</em>`;
    const scriptName = GM_info.script.name;
    const scriptVersion = GM_info.script.version;
    const downloadUrl = 'https://raw.githubusercontent.com/kid4rm90s/Waze-Parallel-Segments/Beta/Waze-Parallel-Segments-Beta.user.js';
    const forumURL = 'https://github.com/kid4rm90s/Waze-Parallel-Segments/issues';

    // ─── Road type IDs ──────────────────────────────────────────────────────────
    // Road types considered pedestrian (excluded from split)
    const pedestrianRoadIds = [5, 10, 16];

    // Minimum clearance (metres) the drawn guide line must leave past the
    // furthest projection of the selected segments, at both ends.
    const GUIDE_CLEARANCE_M = 5;
    // Miter cap for the guide-line offset. Offsetting a vertex by halfD / cos(theta/2)
    // would push a sharp corner arbitrarily far out, so the factor is clamped here.
    // 2.0 covers deflections up to 120 degrees; past that the vertex under-offsets
    // slightly rather than spiking.
    const OFFSET_MITER_MAX = 2.0;
    // Rounded joins on the convex side of a bend: number of arc steps. Even, so the arc
    // has a well-defined middle point. The offset stays exact whatever this is, because
    // the arc radius is exactly halfD.
    const OFFSET_ARC_STEPS = 2;
    // A position within this fraction of an edge end counts as landing on the vertex
    // itself, so both neighbouring segments agree on where the shared node goes.
    const VERTEX_EPS = 1e-6;
    // The same tolerance in metres, for deciding whether a guide vertex lies strictly
    // inside a segment's span.
    const VERTEX_EPS_M = 0.01;
    // Sanity bounds for the "distance between segments" input. The dropdown only
    // offers 5–45 m; the upper bound exists purely to catch a bad value (e.g. a
    // typed 1000) before it flings segments off the road.
    const MAX_PARALLEL_GAP_M = 200;
    // A reconciled segment shorter than this is treated as collapsed — WME
    // rejects zero-length geometry, so the run is aborted before any mutation.
    const MIN_SEGMENT_SPAN_M = 0.1;
    // How far the point handed to AddNode may sit from a participating segment's end
    // before the placement is reported as wrong. WME accepts a point that misses and
    // silently drags the segment to meet the new node, so this is measured, not assumed.
    const ADD_NODE_TOLERANCE_M = 0.05;

    const language = {
        btnSplit: "Split the segments",
        btnMakeParallel: "Make it parallel",
        strMeters: "m",
        strDistance: "Distance between the two parallel segments:",
        strSelMoreSeg: "Since you have more than 1 segment selected, to use this function make sure that you have selected segments sequentially (from one end to the other) and after executing the script, VERIFY the result obtained.",
        strMakeParallelConfirm: "You are about to make {count} segments parallel. Continue?",
        strMakeParallelGuide: "Draw a guide line on the map — the selected segments will become parallel to it.",
        strMakeParallelSuccess: "Successfully made {count} segment{plural} parallel with {distance}m gap!",
        strMakeParallelBadDistance: "Choose a valid distance (a positive number of metres) before making segments parallel.",
        strGuideTooShort: "Guide line is too short. The drawn line must extend past both ends of the selected segments (minimum {margin}m clearance at each end).",
        strMakeParallelFailed: "Could not make the segments parallel — the changes were rolled back. See the console for details.",
        strSplitFailed: "Could not split the segments — the changes were rolled back. See the console for details.",
        strDrawingInProgress: "A drawing is already in progress — finish or cancel it first.",
        strWouldCollapse: "That distance collapses at least one selected segment to a point — nothing was changed. Try a smaller gap."
    };

    // ─── State tracking across multi-segment splits ──────────────────────────
    let last_node_A = null;
    let last_node_B = null;
    let last_coord_left_first = null;
    let last_coord_left_last = null;
    let last_coord_right_first = null;
    let last_coord_right_last = null;

    // ─── SDK instance ────────────────────────────────────────────────────────
    let sdk = null;

    // ─── Transactions (WME SDK+ · Editing.Transactions) ──────────────────────
    // The native SDK has no action-grouping API — sdk.Editing only exposes
    // undo / redo / undoAll — so a multi-step edit produces one undo entry per
    // mutation. sdk.Editing.doActions(), supplied by the wme-sdk-plus library
    // @require'd above, dispatches every action raised inside a callback as a
    // single MultiAction instead: ONE undo entry, and a throw discards the lot.
    // See https://github.com/TheEditorX/wme-sdk-plus/wiki
    //
    // Deliberately drives begin/commit/cancel rather than doActions() itself, so a
    // validation path can abort via `return false` instead of leaving an empty
    // entry in the WME change log. (It also sidesteps doActions()'s refusal to
    // accept async callbacks.)
    const hasTransactions = () => typeof sdk?.Editing?.beginTransaction === 'function';

    // Runs fn as a single transaction and returns its result. If fn returns false
    // the transaction is cancelled rather than committed. When transaction support
    // is unavailable the callback runs unwrapped — each mutation is then its own
    // undo entry and there is no atomic rollback.
    function withTransaction(description, fn) {
        if (!hasTransactions()) {
            return fn();
        }
        sdk.Editing.beginTransaction();
        let result;
        try {
            result = fn();
        } catch (ex) {
            // Discards every action captured so far — this is the rollback.
            try {
                sdk.Editing.cancelTransaction();
            } catch (cancelEx) {
                console.error(`${scriptName} cancelTransaction failed:`, cancelEx);
            }
            throw ex;
        }
        if (result === false) {
            sdk.Editing.cancelTransaction();
            return result;
        }
        sdk.Editing.commitTransaction(description);
        return result;
    }

    // Undoes our own mutations back to a previously recorded unsaved-change count.
    // After a transaction cancel this is a no-op (the count is already restored), so
    // it only does real work on the no-transaction-support fallback path.
    function rollbackToUnsavedCount(unsavedBefore) {
        // Re-read the live count every pass: WME may coalesce several of our
        // mutations into one undo entry, so a pre-computed step count would
        // over-revert and delete edits the user made before this run. Stop as
        // soon as the count stops falling, and cap the loop defensively.
        for (let guard = 0; guard < 500 && sdk.Editing.getUnsavedChangesCount() > unsavedBefore; guard++) {
            const before = sdk.Editing.getUnsavedChangesCount();
            try {
                sdk.Editing.undo();
            } catch (undoEx) {
                console.error(`${scriptName} rollback undo failed:`, undoEx);
                break;
            }
            if (sdk.Editing.getUnsavedChangesCount() >= before) break; // no progress
        }
    }

    // ─── Debug tracing ───────────────────────────────────────────────────────
    // Flip to true when diagnosing geometry problems. Keeps normal runs free of
    // per-vertex coordinate dumps, which are expensive on large selections.
    const DEBUG = false;
    const log = (...args) => { if (DEBUG) console.log(...args); };

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
                                console.log(`${scriptName} Traffic side:`, isLeftHandTraffic ? 'LHT' : 'RHT', '— country (from segment chain):', country.name);
                                return;
                            }
                        }
                    }
                }
            } catch (e) {
                console.log(`${scriptName} Segment-chain country detection failed:`, e);
            }
        }
        // Fallback: top country for the current map view.
        try {
            const topCountry = sdk.DataModel.Countries.getTopCountry();
            if (topCountry != null) {
                isLeftHandTraffic = topCountry.isLeftHandTraffic ?? true;
                console.log(`${scriptName} Traffic side:`, isLeftHandTraffic ? 'LHT' : 'RHT', '— country (from getTopCountry):', topCountry.name);
                return;
            }
        } catch (e) {
            console.log(`${scriptName} getTopCountry() failed:`, e);
        }
        console.log(`${scriptName} Could not detect traffic side — keeping`, isLeftHandTraffic ? 'LHT' : 'RHT');
    }

    // ─── Bootstrap ───────────────────────────────────────────────────────────
    function bootstrap() {
        // SDK pattern: use unsafeWindow because @grant directives are present
        unsafeWindow.SDK_INITIALIZED.then(initSdk);
    }

    function initSdk() {
        sdk = unsafeWindow.getWmeSdk({ scriptId: 'Waze-Parallel-Segments', scriptName: scriptName });
        sdk.Events.once({ eventName: 'wme-ready' }).then(init);
    }

    async function init() {
        // wme-sdk-plus has to be initialised before any transaction is started, and
        // only once the SDK itself is ready — hence here rather than in initSdk().
        // Only the module we actually use is requested, so the library does not also
        // install its middleware, XHR and event patches.
        try {
            if (typeof initWmeSdkPlus === 'function') {
                await initWmeSdkPlus(sdk, { hooks: ['Editing.Transactions'] });
                console.log(`${scriptName} wme-sdk-plus ready (Editing.Transactions)`);
            } else {
                console.warn(`${scriptName} wme-sdk-plus not loaded — splits and parallel runs will use one undo entry per change.`);
            }
        } catch (ex) {
            console.error(`${scriptName} wme-sdk-plus init failed — continuing without transactions:`, ex);
        }

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

    // ─── insertButtons: inject split segment and make-parallel UI ────────────
    function insertButtons() {

        const selection = sdk.Editing.getSelection();
        if (!selection || selection.objectType !== 'segment' || selection.ids.length === 0) return;

        // ── Check 1: split-segment conditions (all two-way, symmetrical lanes) ──
        let canSplit = true;
        for (const segId of selection.ids) {
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg) continue;
            const fwdLanes = seg.fromLanesInfo?.numberOfLanes ?? 0;
            const revLanes = seg.toLanesInfo?.numberOfLanes ?? 0;
            if (fwdLanes !== revLanes) { canSplit = false; }
            if (!seg.isTwoWay) { canSplit = false; }
            if (pedestrianRoadIds.includes(seg.roadType)) { canSplit = false; }
        }

        // ── Check 2: make-parallel conditions (all one-way, ≥2 segments) ────
        let canMakeParallel = selection.ids.length >= 2;
        for (const segId of selection.ids) {
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg) continue;
            if (seg.isTwoWay) { canMakeParallel = false; break; }
            if (pedestrianRoadIds.includes(seg.roadType)) { canMakeParallel = false; break; }
        }

        if (!canSplit && !canMakeParallel) return;

        // ── Create shared container (once) ──────────────────────────────────
        if (document.getElementById('split-segment') === null) {
            const strMeters = language.strMeters;

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

            // Split button
            const btnSplit = document.createElement('wz-button');
            btnSplit.setAttribute('color', 'secondary');
            btnSplit.setAttribute('size', 'sm');
            btnSplit.id = 'btnSplitSegments';
            btnSplit.style.cssText = 'float:right;margin-top: 5px;';
            btnSplit.textContent = language.btnSplit;
            btnSplit.addEventListener('click', mainSplitSegments);

            // Make-parallel button
            const btnParallel = document.createElement('wz-button');
            btnParallel.setAttribute('color', 'secondary');
            btnParallel.setAttribute('size', 'sm');
            btnParallel.id = 'btnMakeParallel';
            btnParallel.style.cssText = 'float:right;margin-top: 5px;margin-left: 4px;';
            btnParallel.textContent = language.btnMakeParallel;
            btnParallel.addEventListener('click', onMakeParallelClick);

            const divGroup1 = document.createElement('div');
            divGroup1.appendChild(label);
            divGroup1.appendChild(selSegmentsDistance);
            divGroup1.appendChild(btnSplit);
            divGroup1.appendChild(btnParallel);

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

        // ── Toggle button visibility ────────────────────────────────────────
        const splitBtn = document.getElementById('btnSplitSegments');
        const parallelBtn = document.getElementById('btnMakeParallel');
        if (splitBtn) splitBtn.style.display = canSplit ? '' : 'none';
        if (parallelBtn) parallelBtn.style.display = canMakeParallel ? '' : 'none';
    }

    // ─── orderSegments: sort selected segment IDs from one end to the other ───
    function orderSegments() {
        const selection = sdk.Editing.getSelection();
        if (!selection || selection.objectType !== 'segment') return [];
        const selectedIds = selection.ids;
        console.log(`${scriptName} orderSegments: total selected =`, selectedIds.length, 'ids =', selectedIds);

        const nodeOccurrences = [];
        for (const segId of selectedIds) {
            const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
            if (!seg) { console.log(`${scriptName} orderSegments: segment not found in model:`, segId); continue; }
            console.log(`${scriptName} orderSegments: seg ${segId} fromNode=${seg.fromNodeId} toNode=${seg.toNodeId}`);
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
        console.log(`${scriptName} orderSegments: node occurrence map =`, nodeOccurrences);

        let nextNodeId = null;
        for (const entry of nodeOccurrences) {
            if (entry[1] === 1) { nextNodeId = entry[0]; break; }
        }
        console.log(`${scriptName} orderSegments: start node =`, nextNodeId);

        if (nextNodeId === null) {
            // Circular selection or disconnected — fall back to original order
            console.log(`${scriptName} orderSegments: no endpoint node found (circular?), using original order`);
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
                    console.log(`${scriptName} orderSegments: placed seg ${segId} (fromNode match, next=${seg.toNodeId})`);
                    orderedSegIds.push(segId);
                    nextNodeId = seg.toNodeId;
                    remaining.delete(segId);
                    found = true;
                    break;
                } else if (seg.toNodeId === nextNodeId) {
                    console.log(`${scriptName} orderSegments: placed seg ${segId} (toNode match, next=${seg.fromNodeId})`);
                    orderedSegIds.push(segId);
                    nextNodeId = seg.fromNodeId;
                    remaining.delete(segId);
                    found = true;
                    break;
                }
            }
            if (!found) {
                console.log(`${scriptName} orderSegments: chain broken at node`, nextNodeId, '— remaining unplaced:', [...remaining]);
                break;
            }
        }
        console.log(`${scriptName} orderSegments: result =`, orderedSegIds);
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
        console.log(`${scriptName} executeSplit start — distance:`, distance);

        last_node_A = null;
        last_node_B = null;
        last_coord_left_first = null;
        last_coord_left_last = null;
        last_coord_right_first = null;
        last_coord_right_last = null;

        const orderedSegIds = orderSegments();
        console.log(`${scriptName} executeSplit: ordered segment IDs =`, orderedSegIds,
            '(', orderedSegIds.length, 'of', sdk.Editing.getSelection()?.ids?.length, 'selected)');

        if (orderedSegIds.length === 0) {
            console.log(`${scriptName} executeSplit: nothing to split`);
            return;
        }

        // Lazy traffic-side detection — use first segment for accurate per-segment chain lookup.
        detectTrafficSide(orderedSegIds[0]);
        console.log(`${scriptName} executeSplit: isLeftHandTraffic =`, isLeftHandTraffic);

        const isMultiSeg = orderedSegIds.length > 1;

        // AddNode has no SDK equivalent — must use legacy require.
        // ModifyAllConnections → sdk.DataModel.Nodes.allowNodeTurns.
        // UpdateObject(fwdTurnsLocked/revTurnsLocked) is NOT needed: those are UI-only
        // verification flags; allowNodeTurns already sets the final turn state correctly.
        let AddNodeLegacy = null;
        if (isMultiSeg) {
            console.log(`${scriptName} Multi-segment mode: loading legacy AddNode`);
            try {
                AddNodeLegacy = require('Waze/Action/AddNode');
                console.log(`${scriptName} Legacy AddNode loaded OK`);
            } catch (e) {
                console.error(`${scriptName} Failed to load legacy AddNode:`, e);
            }
        }

        // The whole mutation phase runs as ONE transaction: the split becomes a
        // single undo entry, and a throw anywhere inside it discards every change
        // instead of leaving a half-split road behind on the map.
        let produced;
        try {
            produced = withTransaction(
                `Split ${orderedSegIds.length} segment(s)`,
                () => executeSplitMutations(orderedSegIds, distance, isMultiSeg, AddNodeLegacy)
            );
        } catch (ex) {
            console.error(`${scriptName} executeSplit failed — changes rolled back:`, ex);
            WazeToastr.Alerts.error(scriptName, language.strSplitFailed);
            return;
        }

        const { leftSegIds: splitLeft, rightSegIds: splitRight } = produced;
        console.log(`${scriptName} executeSplit done — left segs:`, splitLeft, '/ right segs:', splitRight);
        WazeToastr.Alerts.success(
            scriptName,
            `Successfully split ${splitLeft.length} segment${splitLeft.length > 1 ? 's' : ''} with ${distance}m gap!`
        );
    }

    // ─── executeSplitMutations: the mutation phase of executeSplit ───────────
    // Split out so it can be handed to withTransaction() as one synchronous
    // callback without re-indenting it. Mutates the map and returns the produced
    // segment IDs; it shares the module-level split state (last_node_A/B and the
    // coord caches) with its caller.
    function executeSplitMutations(orderedSegIds, distance, isMultiSeg, AddNodeLegacy) {
        // AddNodeWrapper — mirrors the legacy version exactly.
        // Delays getAffectedUniqueIds until the node actually exists, preventing
        // the action manager from throwing when the node hasn't been created yet.
        function AddNodeWrapper(point, segments) {
            const base = new AddNodeLegacy(point, segments);
            const origGetAffected = base.getAffectedUniqueIds.bind(base);
            base.getAffectedUniqueIds = function (dataModel) {
                return this.node ? origGetAffected(dataModel) : [];
            };
            // Remember what we asked for, so verifyAddNodes() can compare it against what
            // the SDK reports once the action has run.
            base.intendedPoint = point?.coordinates ? [...point.coordinates] : null;
            base.intendedSegmentIds = segments
                .map(s => (typeof s?.getID === 'function' ? s.getID() : s?.attributes?.id))
                .filter(id => id != null);
            return base;
        }

        // Move a carriageway's junction-side endpoint onto the computed junction point.
        // Without this the previous carriageway keeps its own natural offset endpoint,
        // which is a DIFFERENT point whenever the road bends at the junction — leaving the
        // node, the previous carriageway and the new segment disagreeing about where the
        // junction is.
        function pullCarriagewayEnd(segmentId, sdkSeg, point, nodeCoord, label) {
            if (!sdkSeg || !point || !nodeCoord) return;
            const coords = sdkSeg.geometry.coordinates.map(c => [...c]);
            const idx = nearestEndIndex(coords, nodeCoord).index;
            if (distanceMetres(coords[idx], point) < 0.001) return;
            coords[idx] = [...point];
            sdk.DataModel.Segments.updateSegment({
                segmentId,
                geometry: { type: 'LineString', coordinates: coords }
            });
            console.log(`${scriptName} junction ${label}: pulled prev carriageway ${segmentId} end #${idx} onto the junction point`);
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
                console.log(`${scriptName} executeSplit: segment not found in model (may already be split):`, idsegment);
                continue;
            }

            // Determine how this segment connects to the previous one (by shared node ID)
            if (last_node_A !== null && last_node_B !== null) {
                if (last_node_A === segment.toNodeId)   connMode = 'AB';
                if (last_node_B === segment.fromNodeId) connMode = 'BA';
                if (last_node_A === segment.fromNodeId) connMode = 'AA';
                if (last_node_B === segment.toNodeId)   connMode = 'BB';
                // connMode is only ever assigned, never cleared, so a pair that matches
                // none of the four silently reuses the PREVIOUS iteration's mode. That
                // would aim the endpoint adjustment (and the AddNode point) at the wrong
                // end. Make it visible before deciding to skip the join instead.
                if (!['AB', 'BA', 'AA', 'BB'].includes(connMode)) {
                    console.warn(`${scriptName} connMode UNRESOLVED at i=${i} (seg ${idsegment}) — no node matches lastA=${last_node_A} lastB=${last_node_B} against from=${segment.fromNodeId} to=${segment.toNodeId}; reusing "${connMode}"`);
                }
            }

            console.log(`${scriptName} executeSplit: Segment ${i}: id=${idsegment} connMode=${connMode}  fromNode=${segment.fromNodeId} toNode=${segment.toNodeId}  lastA=${last_node_A} lastB=${last_node_B}`);

            if (connMode === 'AA' || connMode === 'BB') {
                last_node_A = segment.toNodeId;
                last_node_B = segment.fromNodeId;
            } else {
                last_node_A = segment.fromNodeId;
                last_node_B = segment.toNodeId;
            }

            // Where this segment's carriageways must meet the previous ones: the
            // intersection of the two offset lines, so both stay parallel and the node sits
            // on the shared junction node's perpendicular. Must be computed BEFORE the
            // split, because it needs this segment's ORIGINAL geometry, which
            // createSegments overwrites.
            let junctionSnap = null;
            if (i > 0 && isMultiSeg) {
                junctionSnap = parallelJunctionSnap(
                    leftSegIds[leftSegIds.length - 1],
                    rightSegIds[rightSegIds.length - 1],
                    segment,
                    distance / 2
                );
            }

            const segments = createSegments(segment, distance, connMode, junctionSnap);
            if (!segments) {
                console.log(`${scriptName} executeSplit: createSegments returned null for segment`, idsegment);
                continue;
            }
            console.log(`${scriptName} executeSplit: Segment ${i} split → left=${segments[0]} right=${segments[1]}`);
            console.log(`${scriptName} executeSplit: Coord cache after split:`,
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
                const prevLeftSdk  = sdk.DataModel.Segments.getById({ segmentId: prevLeftId });
                const currLeftSdk  = sdk.DataModel.Segments.getById({ segmentId: segments[0] });
                const currRightSdk = sdk.DataModel.Segments.getById({ segmentId: segments[1] });
                const prevRightSdk = sdk.DataModel.Segments.getById({ segmentId: prevRightId });
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
                    leftCoord  = { type: 'Point', coordinates: leftCoords[junctionIndex(leftCoords, connMode, true)] };
                    rightCoord = { type: 'Point', coordinates: rightCoords[junctionIndex(rightCoords, connMode, false)] };
                } else {
                    // Fallback to cached coords if SDK can't find the segment yet.
                    // These MUST be the previous segment's cached junction ends — the same
                    // values createSegments() copied into this geometry — so the selection
                    // has to follow junctionAtEnd() exactly. It previously took the OPPOSITE
                    // end of both carriageways, which put the node a whole segment length
                    // away and left WME to drag a segment across to meet it.
                    console.log(`${scriptName} SDK segment not found for coord read, falling back to cache. left:`, segments[0], 'right:', segments[1]);
                    const atEnd = junctionAtEnd(connMode);
                    leftCoord  = { type: 'Point', coordinates: atEnd ? last_coord_left_first  : last_coord_left_last };
                    rightCoord = { type: 'Point', coordinates: atEnd ? last_coord_right_last : last_coord_right_first };
                }

                console.log(`${scriptName} AddNode LEFT  coord=${JSON.stringify(leftCoord)}  segs: prev=${prevLeftId} curr=${segments[0]}  wme: prev=${!!prevLeftWme} curr=${!!currLeftWme}`);
                console.log(`${scriptName} AddNode RIGHT coord=${JSON.stringify(rightCoord)} segs: prev=${prevRightId} curr=${segments[1]}  wme: prev=${!!prevRightWme} curr=${!!currRightWme}`);

                // Both carriageways must END on the junction point, not just the new one:
                // the previous carriageway still sits on its own natural offset endpoint,
                // which is a different point whenever the road bends here. createSegments
                // has already written the new segment's end from junctionSnap, so only the
                // previous carriageway needs pulling.
                pullCarriagewayEnd(prevLeftId,  prevLeftSdk,  junctionSnap?.left,  junctionSnap?.node, 'LEFT');
                pullCarriagewayEnd(prevRightId, prevRightSdk, junctionSnap?.right, junctionSnap?.node, 'RIGHT');

                // Measure the placement before dispatching, AFTER the pull so the check sees
                // the geometry that will actually be used. The point is only correct if it
                // sits on the facing end of BOTH segments being joined.
                logAddNodeCheck('LEFT',  leftCoord,
                    sdk.DataModel.Segments.getById({ segmentId: prevLeftId }),
                    sdk.DataModel.Segments.getById({ segmentId: segments[0] }));
                logAddNodeCheck('RIGHT', rightCoord,
                    sdk.DataModel.Segments.getById({ segmentId: prevRightId }),
                    sdk.DataModel.Segments.getById({ segmentId: segments[1] }));

                // Where the node sits relative to the SHARED point, in the terms the map
                // shows: straight junctions must be perpendicular to it.
                logJunctionOffset('LEFT',  leftCoord,  junctionSnap?.node,
                    sdk.DataModel.Segments.getById({ segmentId: prevLeftId }),
                    sdk.DataModel.Segments.getById({ segmentId: segments[0] }), distance / 2);
                logJunctionOffset('RIGHT', rightCoord, junctionSnap?.node,
                    sdk.DataModel.Segments.getById({ segmentId: prevRightId }),
                    sdk.DataModel.Segments.getById({ segmentId: segments[1] }), distance / 2);

                if (prevLeftWme && currLeftWme && leftCoord) {
                    actionsToAdd.push(AddNodeWrapper(leftCoord, [prevLeftWme, currLeftWme]));
                } else {
                    console.log(`${scriptName} AddNode LEFT skipped — missing:`, { prevLeftWme: !!prevLeftWme, currLeftWme: !!currLeftWme, leftCoord });
                }
                if (prevRightWme && currRightWme && rightCoord) {
                    actionsToAdd.push(AddNodeWrapper(rightCoord, [prevRightWme, currRightWme]));
                } else {
                    console.log(`${scriptName} AddNode RIGHT skipped — missing:`, { prevRightWme: !!prevRightWme, currRightWme: !!currRightWme, rightCoord });
                }
            }

            leftSegIds.push(segments[0]);
            rightSegIds.push(segments[1]);
        }

        // ── Phase 2: dispatch all AddNode actions now that all segments are split.
        if (isMultiSeg) {
            console.log(`${scriptName} Dispatching ${actionsToAdd.length} AddNode action(s)`);
            actionsToAdd.forEach(a => W.model.actionManager.add(a));

            // Ask the SDK what those actions actually produced.
            verifyAddNodes(actionsToAdd);

            // SDK: allowNodeTurns replaces legacy ModifyAllConnections.
            console.log(`${scriptName} Allowing turns at all nodes of produced segments via SDK`);
            let nodeIdsSeen = 0;
            for (const segId of [...leftSegIds, ...rightSegIds]) {
                const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
                if (!seg) { console.log(`${scriptName} allowNodeTurns: SDK segment missing for seg`, segId); continue; }
                // != null, not !== null: an unsaved segment can report these as undefined.
                if (seg.fromNodeId != null) { nodeIdsSeen++; sdk.DataModel.Nodes.allowNodeTurns({ nodeId: seg.fromNodeId, allow: true }); }
                if (seg.toNodeId   != null) { nodeIdsSeen++; sdk.DataModel.Nodes.allowNodeTurns({ nodeId: seg.toNodeId,   allow: true }); }
            }
            // A freshly split, unsaved segment reported no usable from/to node ids on a real
            // run. In that case there is nothing here to enable turns on, and the run would
            // otherwise look like it had done so — which is why the README asks you to verify
            // turn restrictions at the new junctions.
            if (nodeIdsSeen === 0) {
                console.warn(`${scriptName} allowNodeTurns: none of the ${leftSegIds.length + rightSegIds.length} produced segments exposed from/to node ids — turns were NOT touched`);
            } else {
                console.log(`${scriptName} allowNodeTurns: ${nodeIdsSeen} node id(s) across ${leftSegIds.length + rightSegIds.length} produced segments`);
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

        return { leftSegIds, rightSegIds };
    }

    // ═══════════════════════════════════════════════════════════════════════
    //  "Make it parallel" feature
    // ═══════════════════════════════════════════════════════════════════════

    // ─── onMakeParallelClick: entry point — draw a guide line ────────────
    function onMakeParallelClick() {
        const selection = sdk.Editing.getSelection();
        if (!selection || selection.objectType !== 'segment' || selection.ids.length < 2) return;

        const distance = parseFloat(document.getElementById('segmentsDistance').value);
        if (!Number.isFinite(distance) || distance <= 0 || distance > MAX_PARALLEL_GAP_M) {
            WazeToastr.Alerts.error(scriptName, language.strMakeParallelBadDistance);
            return;
        }

        if (sdk.Editing.isDrawingInProgress()) {
            WazeToastr.Alerts.error(scriptName, language.strDrawingInProgress);
            return;
        }

        const segmentIds = [...selection.ids];

        // Show brief guidance toastr before drawing
        WazeToastr.Alerts.info(scriptName, language.strMakeParallelGuide, false, false, 3000);

        sdk.Map.drawLine()
            .then((line) => onDrawLineFinished(line, segmentIds, distance))
            .catch((ex) => {
                if (ex instanceof sdk.Errors.InvalidStateError) {
                    // User cancelled drawing — ignore silently
                    console.log(`${scriptName} Make parallel drawing cancelled`);
                } else {
                    console.error(`${scriptName} Make parallel error:`, ex);
                }
            });
    }

    // ─── onDrawLineFinished: handle the drawn guide line ────────────────
    // Always confirm — even 2 segments is a destructive edit that is hard to
    // review afterwards, so a single code path always asks first.
    function onDrawLineFinished(line, segmentIds, distance) {
        WazeToastr.Alerts.confirm(
            scriptName,
            language.strMakeParallelConfirm.replace('{count}', segmentIds.length),
            function () { applyMakeParallel(line, segmentIds, distance); },
            function () { return; },
            "Continue",
            "Cancel"
        );
    }

    // ─── applyMakeParallel: validated wrapper, runs as one transaction ────
    // Every SDK mutation (moveNode / updateSegment / updateTurn) creates its own
    // undo entry, so a failure half-way through would leave a partially reshaped
    // junction and the user would need one undo per mutation to clean it up. The
    // reshape therefore runs inside a single transaction: success commits it as
    // ONE undo entry, while any throw (or a validation abort returning false)
    // discards the whole run. The delta-based rollback is kept only for the
    // no-transaction-support fallback — after a cancel it is a no-op.
    function applyMakeParallel(line, segmentIds, distance) {
        if (!Number.isFinite(distance) || distance <= 0 || distance > MAX_PARALLEL_GAP_M) {
            WazeToastr.Alerts.error(scriptName, language.strMakeParallelBadDistance);
            return;
        }
        if (!line?.coordinates || line.coordinates.length < 2) {
            WazeToastr.Alerts.error(scriptName, language.strMakeParallelFailed);
            return;
        }

        const unsavedBefore = sdk.Editing.getUnsavedChangesCount();
        try {
            const applied = withTransaction(
                'Make segments parallel',
                () => applyMakeParallelCore(line, segmentIds, distance)
            );
            // false = a pre-mutation validation path aborted; core already showed
            // the reason and the transaction was discarded.
            if (applied === false) return;

            const msg = language.strMakeParallelSuccess
                .replace('{count}', segmentIds.length)
                .replace('{plural}', segmentIds.length > 1 ? 's' : '')
                .replace('{distance}', distance);
            WazeToastr.Alerts.success(scriptName, msg);
        } catch (ex) {
            console.error(`${scriptName} applyMakeParallel failed — rolling back:`, ex);
            rollbackToUnsavedCount(unsavedBefore);
            WazeToastr.Alerts.error(scriptName, language.strMakeParallelFailed);
        }
    }

    // ─── applyMakeParallelCore: core logic — offset segments to be parallel ───
    // Strategy: compute segment geometries first (by slicing the offset guide
    // line), then derive node positions from the slice endpoints. This ensures
    // node and geometry are always in sync, preventing kinking on curves while
    // fully reshaping segments to follow the guide line's curvature.
    //   1. Validate the drawn guide line is longer than the segment span
    //   2. Determine which geometric side each segment is on
    //   3. Detect independent chains. If exactly 2 chains, assign opposite
    //      sides (one left, one right) so they spread outward from the guide
    //      line as a parallel pair.
    //   4. Make each chain internally consistent (force mixed-side segments
    //      within a chain to the chain's majority side). This prevents
    //      cross-side nodes inside a chain from collapsing both chains.
    //   5. Detect cross-side shared nodes. If any exist, force all segments
    //      to the majority side to prevent V-shaped kinks.
    //   6. Group by side, slice guide line → offset → per-segment slices,
    //      record node positions from slice endpoints.
    //   7. Place cross-side shared nodes on the guide line.
    //   8. Reconcile every geometry endpoint with its node position — WME
    //      treats node coordinates as authoritative, so the geometry written
    //      for a segment must end exactly on its nodes.
    //   9. Snapshot the full turn state at every affected node.
    //  10. Move all nodes, then update all segment geometries.
    //  11. Re-apply the snapshotted turn state.
    function applyMakeParallelCore(line, segmentIds, distance) {
        const halfD = distance / 2;
        log(`========== ${scriptName} applyMakeParallel START ==========`);
        log(`${scriptName} Params: segmentIds=${JSON.stringify(segmentIds)}, distance=${distance}, halfD=${halfD}`);
        log(`${scriptName} Guide line coords: ${line.coordinates.length}`);

        // Read-only segment cache for the pre-mutation phase — replaces the
        // repeated getById calls (and the O(n²) scan in chain detection).
        // Cached objects may go stale once mutations run, so anything read
        // AFTER the mutation phase calls getById directly.
        const segCache = new Map();
        const getSeg = (id) => {
            if (!segCache.has(id)) segCache.set(id, sdk.DataModel.Segments.getById({ segmentId: id }));
            return segCache.get(id);
        };
        // ── Node connectivity map ──────────────────────────────────────────
        const nodeSegments = new Map(); // nodeId → Set<segId>
        for (const segId of segmentIds) {
            const seg = getSeg(segId);
            if (!seg) {
                log(`${scriptName}   seg ${segId}: NOT FOUND in model`);
                continue;
            }
            log(`${scriptName}   seg ${segId}: fromNode=${seg.fromNodeId}, toNode=${seg.toNodeId}, coords=${JSON.stringify(seg.geometry.coordinates)}`);
            for (const nodeId of [seg.fromNodeId, seg.toNodeId]) {
                if (nodeId === null) continue;
                if (!nodeSegments.has(nodeId)) nodeSegments.set(nodeId, new Set());
                nodeSegments.get(nodeId).add(segId);
            }
        }
        log(`${scriptName} Node connectivity:`, JSON.stringify([...nodeSegments].map(([n, s]) => [n, [...s]])));

        // Drop repeated coordinates first: a zero-length edge leaves the offset's
        // bisector undefined and makes turf.bearing() return 0 for the pair, which
        // would corrupt both the offset and the side detection below.
        const lineCoords = dedupeCoords(line.coordinates);

        // Simplify the drawn line to reduce vertex count
        const guideCoords = turf.simplify(turf.lineString(lineCoords), {
            tolerance: 0.000001,
            highQuality: true
        }).geometry.coordinates;

        log(`${scriptName} After simplify: coords count=${guideCoords.length}`);
        log(`${scriptName} Guide coords (simplified):`, JSON.stringify(guideCoords));

        if (guideCoords.length < 2) {
            console.error(`${scriptName} guide line has too few coordinates`);
            WazeToastr.Alerts.error(scriptName, language.strMakeParallelFailed);
            return false;
        }

        const guideLine = turf.lineString(guideCoords);
        const guideLengthM = turf.length(guideLine, { units: 'meters' });
        log(`${scriptName} Guide line length: ${guideLengthM.toFixed(2)}m`);

        // ── Validate: guide line must be longer than the selected segments ──
        // Project each segment's first and last coordinate onto the guide line
        // and verify they clear the guide line's interior (not its tips).
        // nearestPointOnLine already returns the distance along the line as
        // properties.location (in KILOMETRES, independent of the units option),
        // so no lineSlice + length round-trip is needed per endpoint.
        const marginMeters = GUIDE_CLEARANCE_M;
        let minDistM = Infinity;
        let maxDistM = -Infinity;

        log(`${scriptName} Validation: projecting segment endpoints onto guide line...`);
        for (const segId of segmentIds) {
            const seg = getSeg(segId);
            if (!seg) continue;
            const coords = seg.geometry.coordinates;
            for (const coord of [coords[0], coords[coords.length - 1]]) {
                const nearest = turf.nearestPointOnLine(guideLine, turf.point(coord));
                const d = nearest.properties.location * 1000; // km → m
                log(`${scriptName}   seg ${segId} endpoint [${coord[0].toFixed(6)},${coord[1].toFixed(6)}] → projected [${nearest.geometry.coordinates[0].toFixed(6)},${nearest.geometry.coordinates[1].toFixed(6)}] (index=${nearest.properties.index}) → ${d.toFixed(2)}m from guide start`);
                if (d < minDistM) minDistM = d;
                if (d > maxDistM) maxDistM = d;
            }
        }
        log(`${scriptName} Validation: minDistM=${minDistM === Infinity ? 'N/A' : minDistM.toFixed(2)}m, maxDistM=${maxDistM === -Infinity ? 'N/A' : maxDistM.toFixed(2)}m, guideLengthM=${guideLengthM.toFixed(2)}m`);

        if (minDistM !== Infinity &&
            (minDistM < marginMeters || guideLengthM - maxDistM < marginMeters)) {
            console.error(`${scriptName} VALIDATION FAILED: earliest projection ${minDistM.toFixed(1)}m from start, ${(guideLengthM - maxDistM).toFixed(1)}m from end, margin ${marginMeters}m`);
            WazeToastr.Alerts.error(scriptName, language.strGuideTooShort.replace('{margin}', marginMeters));
            return false;
        }
        log(`${scriptName} Validation PASSED`);

        // Detect traffic side for log context
        detectTrafficSide(segmentIds[0]);

        // ── Step 1: Determine which geometric side each segment is on ──────
        log(`${scriptName} Step 1: determining segment sides...`);
        const segmentSides = {};
        for (const segId of segmentIds) {
            const seg = getSeg(segId);
            if (!seg) continue;
            segmentSides[segId] = determineSideOfLine(seg.geometry.coordinates, guideCoords);
        }
        log(`${scriptName}   Sides: ${segmentIds.map(id => `${id}=${segmentSides[id]}`).join(', ')}`);

        // ── Step 2: Detect independent chains, assign opposite sides ──────
        // When there are exactly 2 independent chains (segments that don't share
        // nodes), force one to the left side and the other to the right side.
        // This creates a parallel pair offset outward from the guide line — each
        // chain spreads away from the center instead of both crowding one side.
        // this overrides the detected sides, so two chains that really
        // do sit on the same side get split apart. Ceiling: a heuristic cannot
        // read intent — upgrade path is a UI toggle for "keep detected sides".
        log(`${scriptName} Step 2: detecting independent chains...`);

        // Chain adjacency built from the node → segments map in one pass,
        // instead of the previous per-segment × per-node × per-segment scan.
        const segNeighbours = new Map(segmentIds.map(id => [id, new Set()]));
        for (const segsAtNode of nodeSegments.values()) {
            for (const a of segsAtNode) {
                for (const b of segsAtNode) {
                    if (a !== b) segNeighbours.get(a).add(b);
                }
            }
        }

        const visited = new Set();
        const chains = [];
        for (const segId of segmentIds) {
            if (visited.has(segId)) continue;
            const chain = [segId];
            visited.add(segId);
            const queue = [segId];
            while (queue.length > 0) {
                const cur = queue.shift();
                for (const n of segNeighbours.get(cur) ?? []) {
                    if (!visited.has(n)) { visited.add(n); queue.push(n); chain.push(n); }
                }
            }
            chains.push(chain);
        }
        log(`${scriptName}   Found ${chains.length} independent chain(s)`);
        for (let ci = 0; ci < chains.length; ci++) {
            log(`${scriptName}     Chain ${ci}: ${chains[ci].length} seg(s), sides: ${chains[ci].map(sid => segmentSides[sid]).join(', ')}`);
        }
        // If exactly 2 chains on the same side, spread outward by assigning
        // opposite sides. The chain FURTHER from the guide line (larger perp
        // distance) stays on its detected side; the CLOSER chain flips. This
        // ensures the physically outermost chain stays outward on its natural
        // side, matching the user's spatial expectation.
        if (chains.length === 2) {
            const c0Side = segmentSides[chains[0][0]];
            const c1Side = segmentSides[chains[1][0]];
            if (c0Side === c1Side) {
                // Compute average center and perpendicular distance for each chain
                const chainDist = [0, 0];
                for (let ci = 0; ci < 2; ci++) {
                    let sumLon = 0, sumLat = 0, count = 0;
                    for (const segId of chains[ci]) {
                        const seg = getSeg(segId);
                        if (!seg) continue;
                        for (const c of seg.geometry.coordinates) { sumLon += c[0]; sumLat += c[1]; count++; }
                    }
                    if (count === 0) continue;
                    const center = [sumLon / count, sumLat / count];
                    const nearest = turf.nearestPointOnLine(guideLine, turf.point(center));
                    chainDist[ci] = turf.distance(turf.point(center), turf.point(nearest.geometry.coordinates), { units: 'meters' });
                    log(`${scriptName}     Chain ${ci} center distance from guide: ${chainDist[ci].toFixed(2)}m`);
                }
                // Flip the closer chain; keep the further chain on its detected side
                const flipIdx = chainDist[0] < chainDist[1] ? 0 : 1;
                const keepIdx = 1 - flipIdx;
                const flipTo = c0Side === 'left' ? 'right' : 'left';
                log(`${scriptName}   Both chains on "${c0Side}" — keeping chain ${keepIdx} (${chainDist[keepIdx].toFixed(2)}m), flipping chain ${flipIdx} (${chainDist[flipIdx].toFixed(2)}m) to "${flipTo}"`);
                for (const segId of chains[flipIdx]) segmentSides[segId] = flipTo;
            }
        }

        // ── Step 3: Make each chain internally consistent ─────────────────
        // Within a chain, segments may detect on different sides, creating
        // cross-side shared nodes inside the chain. This triggers a global
        // majority vote that collapses BOTH chains to one side. Fix by
        // forcing each chain to its own majority side first.
        log(`${scriptName} Step 3: making chains internally consistent...`);
        for (let ci = 0; ci < chains.length; ci++) {
            let left = 0, right = 0;
            for (const segId of chains[ci]) {
                if (segmentSides[segId] === 'left') left++;
                else if (segmentSides[segId] === 'right') right++;
            }
            if (left > 0 && right > 0) {
                const majoritySide = left >= right ? 'left' : 'right';
                log(`${scriptName}     Chain ${ci}: mixed (L:${left}, R:${right}) → forcing to "${majoritySide}"`);
                for (const segId of chains[ci]) segmentSides[segId] = majoritySide;
            } else {
                log(`${scriptName}     Chain ${ci}: consistent (${left > 0 ? 'left' : 'right'})`);
            }
        }

        // ── Step 4: Detect cross-side shared nodes ─────────────────────────
        log(`${scriptName} Step 4: detecting cross-side shared nodes...`);
        const neutralNodeIds = new Set();
        for (const [nodeId, segsAtNode] of nodeSegments) {
            let hasLeft = false, hasRight = false;
            for (const segId of segsAtNode) {
                if (segmentSides[segId] === 'left') hasLeft = true;
                else if (segmentSides[segId] === 'right') hasRight = true;
            }
            if (hasLeft && hasRight) {
                neutralNodeIds.add(nodeId);
                log(`${scriptName}   node ${nodeId}: connected to BOTH left and right — will stay on guide line`);
            }
        }

        // ── Step 5: If cross-side nodes exist, force all to majority side ──
        // a single cross-side node moves ALL selected segments onto
        // one side via a global majority vote, which can defeat the drawn
        // intent. Ceiling: O(n) vote instead of per-node resolution — upgrade
        // path is resolving each cross-side node individually.
        if (neutralNodeIds.size > 0) {
            let left = 0, right = 0;
            for (const side of Object.values(segmentSides)) {
                if (side === 'left') left++;
                else if (side === 'right') right++;
            }
            const majoritySide = left >= right ? 'left' : 'right';
            log(`${scriptName}   Cross-side nodes found — forcing all ${segmentIds.length} segments to "${majoritySide}"`);
            for (const segId of segmentIds) {
                segmentSides[segId] = majoritySide;
            }
            neutralNodeIds.clear();
        }

        // ── Step 6: Compute node positions & segment geometries together ──
        // Strategy: create the offset guide line, slice portions for each segment,
        // then derive node positions from the slice endpoints. This ensures node
        // positions and segment endpoints are in sync. Cross-side shared nodes
        // are the exception (placed on the guide line in the next step).
        log(`${scriptName} Step 6: grouping segments by side and computing offset slices...`);

        const nodeNewPositions = new Map(); // nodeId → [lon, lat]
        const segmentNewGeometries = new Map(); // segId → [[lon,lat], ...]

        // Group segments by side with projection info
        const sideGroups = {}; // side → [{segId, fromNodeId, toNodeId, projStart, projEnd, startLoc, endLoc}]
        for (const segId of segmentIds) {
            const seg = getSeg(segId);
            if (!seg) continue;
            const side = segmentSides[segId];
            if (side !== 'left' && side !== 'right') continue;
            const firstCoord = seg.geometry.coordinates[0];
            const lastCoord = seg.geometry.coordinates[seg.geometry.coordinates.length - 1];
            const projStart = turf.nearestPointOnLine(guideLine, turf.point(firstCoord));
            const projEnd = turf.nearestPointOnLine(guideLine, turf.point(lastCoord));

            if (!sideGroups[side]) sideGroups[side] = [];
            sideGroups[side].push({
                segId,
                fromNodeId: seg.fromNodeId,
                toNodeId: seg.toNodeId,
                projStartCoord: projStart.geometry.coordinates,
                projEndCoord: projEnd.geometry.coordinates,
                // properties.location is KILOMETRES — only ratios are used below,
                // so the unit cancels out.
                startLoc: projStart.properties.location,
                endLoc: projEnd.properties.location
            });
        }

        // Process each side group independently
        for (const [side, segs] of Object.entries(sideGroups)) {
            log(`${scriptName}   Processing ${side} side: ${segs.length} segments`);

            // Sort by projection start location along the guide line
            segs.sort((a, b) => Math.min(a.startLoc, a.endLoc) - Math.min(b.startLoc, b.endLoc));

            // Find the true extremes (handling reversed projections)
            let trueMinCoord = null, trueMinLoc = Infinity;
            let trueMaxCoord = null, trueMaxLoc = -Infinity;
            for (const s of segs) {
                const sLoc = Math.min(s.startLoc, s.endLoc);
                const eLoc = Math.max(s.startLoc, s.endLoc);
                const sCoord = s.startLoc <= s.endLoc ? s.projStartCoord : s.projEndCoord;
                const eCoord = s.endLoc >= s.startLoc ? s.projEndCoord : s.projStartCoord;
                if (sLoc < trueMinLoc) { trueMinLoc = sLoc; trueMinCoord = sCoord; }
                if (eLoc > trueMaxLoc) { trueMaxLoc = eLoc; trueMaxCoord = eCoord; }
            }
            if (!trueMinCoord || !trueMaxCoord) continue;

            // Slice the guide line from min to max.
            // trueMinLoc ≤ trueMaxLoc always holds (the minimum of the per-segment
            // minima can never exceed the maximum of the per-segment maxima), so
            // one slice direction covers every case.
            let sliceCoords = turf.lineSlice(
                turf.point(trueMinCoord),
                turf.point(trueMaxCoord),
                guideLine
            ).geometry.coordinates;
            if (sliceCoords.length < 2) {
                sliceCoords = [trueMinCoord, trueMaxCoord];
            }

            // ── Place every node by ARC LENGTH along the guide ────────────────
            // Each node is found by walking the guide to its arc length and stepping
            // halfD along the LOCAL edge normal there, so it lands opposite the point
            // it was projected from. The previous approach mapped a guide fraction
            // onto a fraction of the offset line's own length, which assumed the
            // offset stretches the guide proportionally — it cannot, because each
            // guide leg shortens by a constant halfD·tan(theta/2) at a bend. On a
            // corner with uneven legs that slid nodes along the curve by up to 15.8m
            // (measured). Arc-length placement carries no such assumption.
            const sliceCum = cumulativeLengthsM(sliceCoords);
            const sliceTotalM = sliceCum[sliceCum.length - 1];
            const vertexGroups = offsetVertexCoords(sliceCoords, halfD, side);

            // properties.location is kilometres along the guide, so the segment's span
            // converts to metres from the slice start; clamp it into the slice.
            const toSliceMetres = (loc) =>
                Math.max(0, Math.min(sliceTotalM, (loc - trueMinLoc) * 1000));

            log(`${scriptName}     ${side} side: slice has ${sliceCoords.length} coords / ${sliceTotalM.toFixed(1)}m`);

            // Cut each segment's portion of the offset and record positions
            for (const s of segs) {
                const dStart = toSliceMetres(Math.min(s.startLoc, s.endLoc));
                const dEnd = toSliceMetres(Math.max(s.startLoc, s.endLoc));

                const segCoords = offsetSliceSegment(
                    sliceCoords, vertexGroups, sliceCum, dStart, dEnd, halfD, side
                );

                // Reverse if the segment's original orientation was reversed
                if (s.startLoc > s.endLoc) {
                    segCoords.reverse();
                }

                // Record the node position from the first endpoint seen.
                // Step 8 then snaps every segment endpoint onto these positions,
                // so ordering here cannot leave geometry and nodes disagreeing.
                if (!neutralNodeIds.has(s.fromNodeId) && !nodeNewPositions.has(s.fromNodeId)) {
                    nodeNewPositions.set(s.fromNodeId, segCoords[0]);
                }
                if (!neutralNodeIds.has(s.toNodeId) && !nodeNewPositions.has(s.toNodeId)) {
                    nodeNewPositions.set(s.toNodeId, segCoords[segCoords.length - 1]);
                }

                segmentNewGeometries.set(s.segId, segCoords);
                log(`${scriptName}     seg ${s.segId} (${side}): span=[${dStart.toFixed(1)}m,${dEnd.toFixed(1)}m], geometry has ${segCoords.length} coords`);
            }
        }

        // ── Step 7: Set cross-side shared node positions (on guide line) ──
        // A node touching both a left and a right segment sits on the guide line
        // itself; Step 8 then pulls both sides' endpoints onto it.
        // this: one position per node, so the side that claimed it first wins
        // and the other side's segment bends up to halfD at that junction. That is
        // deliberate (a bend beats a gap) but it does mean a shared node is not
        // truly "between" both offsets.
        log(`${scriptName} Step 7: setting ${neutralNodeIds.size} cross-side shared node(s) on guide line...`);
        for (const nodeId of neutralNodeIds) {
            const node = sdk.DataModel.Nodes.getById({ nodeId });
            if (!node) continue;
            const nearest = turf.nearestPointOnLine(guideLine, turf.point(node.geometry.coordinates));
            nodeNewPositions.set(nodeId, nearest.geometry.coordinates);
            log(`${scriptName}   neutral node ${nodeId} → guide line [${nearest.geometry.coordinates[0].toFixed(6)},${nearest.geometry.coordinates[1].toFixed(6)}]`);
        }
        log(`${scriptName} Step 7: ${nodeNewPositions.size} unique node positions computed`);

        // ── Step 8: Reconcile segment endpoints with node positions ───────
        // WME treats node coordinates as authoritative: a segment whose stored
        // endpoint differs from its node is silently corrected or drawn with a
        // gap. Force every endpoint onto the position its node is about to be
        // moved to, so Step 10 writes geometry that already agrees. This covers
        // the cross-side nodes placed in Step 7 as well as ordinary shared nodes.
        let snappedEndpoints = 0;
        for (const [segId, coords] of segmentNewGeometries) {
            const seg = getSeg(segId);
            if (!seg || coords.length < 2) continue;
            const fromPos = nodeNewPositions.get(seg.fromNodeId);
            const toPos = nodeNewPositions.get(seg.toNodeId);
            if (fromPos && coords[0] !== fromPos) { coords[0] = fromPos; snappedEndpoints++; }
            if (toPos && coords[coords.length - 1] !== toPos) {
                coords[coords.length - 1] = toPos;
                snappedEndpoints++;
            }
        }
        log(`${scriptName} Step 8: reconciled ${snappedEndpoints} endpoint(s) with node positions`);

        // Guard: reconciliation can collapse a very short segment whose two ends
        // both landed on the same spot, and WME rejects zero-length geometry.
        // Detect it here — before any mutation — so the run aborts cleanly with
        // nothing to roll back.
        for (const [segId, coords] of segmentNewGeometries) {
            if (coords.length < 2) continue;
            const spanM = turf.distance(turf.point(coords[0]), turf.point(coords[coords.length - 1]), { units: 'meters' });
            if (spanM < MIN_SEGMENT_SPAN_M) {
                console.error(`${scriptName} aborting: seg ${segId} would collapse to ${spanM.toFixed(3)}m`);
                WazeToastr.Alerts.error(scriptName, language.strWouldCollapse);
                return false;
            }
        }

        // ── Step 9: Snapshot the turn state at every affected node ────────
        // Reshaping a node's geometry can drop or flip its turns. Record the full
        // allowed/forbidden state BEFORE mutating so Step 11 can re-apply it.
        // allowNodeTurns({allow:true}) was previously used here, but it also
        // un-forbids restrictions the editor set deliberately at those nodes.
        // The key includes the direction flags because one segment pair can have
        // separate forward/reverse turns at the same node.
        const turnKey = (t) => `${t.fromSegmentId}|${t.fromSegmentFwd}|${t.toSegmentId}|${t.toSegmentFwd}`;
        const turnStateBefore = new Map(); // nodeId → Map<turnKey, isAllowed>
        for (const nodeId of nodeNewPositions.keys()) {
            let turns;
            try {
                if (!sdk.DataModel.Turns.canEditTurnsThroughNode({ nodeId })) continue;
                turns = sdk.DataModel.Turns.getTurnsThroughNode({ nodeId });
            } catch (ex) {
                console.error(`${scriptName}   turn snapshot failed for node ${nodeId}:`, ex);
                continue;
            }
            turnStateBefore.set(nodeId, new Map(turns.map(t => [turnKey(t), t.isAllowed])));
        }

        // ── Step 10: Move all nodes, then update segment geometries ────────
        log(`${scriptName} Step 10: moving ${nodeNewPositions.size} unique nodes...`);
        for (const [nodeId, newPos] of nodeNewPositions) {
            log(`${scriptName}   moveNode id=${nodeId} → [${newPos[0].toFixed(6)},${newPos[1].toFixed(6)}]`);
            sdk.DataModel.Nodes.moveNode({
                id: nodeId,
                geometry: { type: 'Point', coordinates: newPos }
            });
        }

        log(`${scriptName} Step 10: updating ${segmentNewGeometries.size} segment geometries (offset-sliced, follows guide line shape)...`);
        for (const [segId, coords] of segmentNewGeometries) {
            if (coords.length >= 2) {
                sdk.DataModel.Segments.updateSegment({
                    segmentId: segId,
                    geometry: { type: 'LineString', coordinates: coords }
                });
            }
        }

        // ── Step 11: Re-apply the snapshotted turn state ──────────────────
        // Restores BOTH directions: a turn that was forbidden before the move
        // must stay forbidden, otherwise geometry re-evaluation silently
        // un-forbids restrictions the editor set on the same nodes.
        log(`${scriptName} Step 11: restoring turns at ${turnStateBefore.size} node(s)...`);
        for (const [nodeId, stateBefore] of turnStateBefore) {
            let turnsNow;
            try {
                turnsNow = sdk.DataModel.Turns.getTurnsThroughNode({ nodeId });
            } catch (ex) {
                console.error(`${scriptName}   turn restore failed for node ${nodeId}:`, ex);
                continue;
            }

            let restored = 0, failed = 0;
            const nowKeys = new Set();
            for (const turn of turnsNow) {
                const key = turnKey(turn);
                nowKeys.add(key);
                // A turn with no prior state is one WME created during the move —
                // leave its default alone rather than guessing.
                if (!stateBefore.has(key)) continue;
                const want = stateBefore.get(key);
                if (turn.isAllowed === want) continue;
                try {
                    sdk.DataModel.Turns.updateTurn({ turnId: turn.id, isAllowed: want });
                    restored++;
                } catch (ex) {
                    // Per-turn isolation: one rejected turn must not abandon the rest.
                    failed++;
                    console.error(`${scriptName}   could not set turn ${turn.id} (node ${nodeId}) to ${want}:`, ex);
                }
            }
            // A turn that existed before but is gone now was dropped by the move
            // and cannot be re-created from here.
            for (const key of stateBefore.keys()) {
                if (!nowKeys.has(key)) console.warn(`${scriptName}   turn ${key} at node ${nodeId} no longer exists after the move`);
            }
            if (restored > 0 || failed > 0) log(`${scriptName}   node ${nodeId}: restored ${restored}, failed ${failed}`);
        }

        log(`========== ${scriptName} applyMakeParallel END ==========`);

        // ── AFTER snapshot (debug only) ────────────────────────────────────
        if (DEBUG) {
            for (const segId of segmentIds) {
                const seg = sdk.DataModel.Segments.getById({ segmentId: segId });
                log(`${scriptName}   seg ${segId}: fromNode=${seg?.fromNodeId}, toNode=${seg?.toNodeId}, coords=${JSON.stringify(seg?.geometry.coordinates)}`);
            }
        }

        return true;
    }

    // ─── determineSideOfLine: which geometric side of a guide line a segment is on ──
    function determineSideOfLine(segmentCoords, guideCoords) {
        // Compute the midpoint of the segment geometry
        let sumLon = 0;
        let sumLat = 0;
        for (const coord of segmentCoords) {
            sumLon += coord[0];
            sumLat += coord[1];
        }
        const midLon = sumLon / segmentCoords.length;
        const midLat = sumLat / segmentCoords.length;

        // Build a turf line from the guide coords
        const guideLine = turf.lineString(guideCoords);
        const nearest = turf.nearestPointOnLine(guideLine, turf.point([midLon, midLat]));

        const nearestLon = nearest.geometry.coordinates[0];
        const nearestLat = nearest.geometry.coordinates[1];

        // The segment (index) of the guide line containing the nearest point
        const idx = nearest.properties.index;
        const p1 = guideCoords[idx];
        const p2 = guideCoords[Math.min(idx + 1, guideCoords.length - 1)];

        // Bearing of the guide line at the nearest point
        const bearing = turf.bearing(turf.point(p1), turf.point(p2));

        // Bearing from the nearest point to the segment midpoint
        const toSegment = turf.bearing(
            turf.point([nearestLon, nearestLat]),
            turf.point([midLon, midLat])
        );

        // Cross product (z-component) between guide direction and segment direction.
        // IMPORTANT: turf.bearing uses 0° = North, but Math.cos/sin use 0° = East.
        // Swap sin/cos to convert from bearing convention to vector components.
        const bearingRad = bearing * Math.PI / 180;
        const toSegmentRad = toSegment * Math.PI / 180;
        const dx = Math.sin(bearingRad);   // sin, not cos — bearing 0°=North → x=0
        const dy = Math.cos(bearingRad);   // cos, not sin — bearing 0°=North → y=1
        const sx = Math.sin(toSegmentRad);
        const sy = Math.cos(toSegmentRad);
        const cross = dx * sy - dy * sx;

        return cross > 0 ? 'left' : 'right';
    }

    // ─── dedupeCoords: drop consecutive repeated coordinates ────────────────
    // A repeated point creates a zero-length edge, which leaves the offset's angle
    // bisector undefined and makes turf.bearing() return 0 for that pair — both of
    // which silently corrupt the offset and the side detection. The draw tool can
    // emit the same position twice. (Idiom borrowed from WazePT Segments.)
    function dedupeCoords(coords) {
        const out = [];
        for (const coord of coords) {
            const prev = out[out.length - 1];
            if (!prev || prev[0] !== coord[0] || prev[1] !== coord[1]) out.push(coord);
        }
        return out;
    }

    // ─── unitVectorMetres: unit vector from coord a to coord b ─────────────
    // Only the direction is used, so an equirectangular scaling at the reference
    // latitude is exact for our purposes — and unlike turf.bearing it stays
    // well-defined however short the edge is.
    function unitVectorMetres(a, b) {
        const kx = Math.cos(a[1] * Math.PI / 180);
        const dx = (b[0] - a[0]) * kx;
        const dy = b[1] - a[1];
        const len = Math.hypot(dx, dy);
        return len > 0 ? { x: dx / len, y: dy / len } : { x: 0, y: 0 };
    }

    // ─── bearingFromXY: compass bearing of an (east, north) vector ─────────
    // Bearing 0° = north (y) and 90° = east (x), hence atan2(x, y).
    function bearingFromXY(x, y) {
        return (Math.atan2(x, y) * 180 / Math.PI + 360) % 360;
    }

    // ─── offsetAlongNormal: step `halfD` from a point along a side normal ──
    // (nx, ny) is the direction whose perpendicular is the offset direction, and
    // `scale` is the miter factor (1 for a plain normal).
    function offsetAlongNormal(coord, nx, ny, sideSign, halfD, scale = 1) {
        const offsetBearing = bearingFromXY(sideSign * ny, -sideSign * nx);
        return turf.destination(
            turf.point(coord),
            (halfD * scale) / 1000,
            offsetBearing,
            { units: 'kilometers' }
        ).geometry.coordinates;
    }

    // ─── offsetArcPoints: rounded join on the convex side of a bend ────────
    // A miter on the OUTSIDE of a corner ends up halfD/cos(theta/2) from the vertex
    // (measured: 24.75m where 17.5m was asked for, at a 90° corner on a 35m gap),
    // because the perpendicular feet fall beyond both edges. The exact parallel curve
    // there is an arc of radius halfD centred on the vertex, swept between the two
    // edge normals.
    function offsetArcPoints(vertex, incoming, outgoing, sideSign, halfD) {
        const b1 = bearingFromXY(sideSign * incoming.y, -sideSign * incoming.x);
        const b2 = bearingFromXY(sideSign * outgoing.y, -sideSign * outgoing.x);

        // Shortest sweep between the two normals, in (-180, 180].
        const delta = ((b2 - b1 + 540) % 360) - 180;
        const steps = Math.abs(delta) < 1e-9 ? 1 : OFFSET_ARC_STEPS;

        const points = [];
        for (let k = 0; k <= steps; k++) {
            const bearing = (b1 + delta * (k / steps) + 360) % 360;
            points.push(
                turf.destination(turf.point(vertex), halfD / 1000, bearing, { units: 'kilometers' })
                    .geometry.coordinates
            );
        }
        return points;
    }

    // ─── offsetVertexCoords: per-vertex offset for a guide polyline ─────────
    // Returns ONE ENTRY PER INPUT VERTEX. An entry is normally a single coordinate —
    // the miter point, exactly halfD from both adjacent edges — except on the convex
    // side of a bend, where it is the arc from offsetArcPoints(). Endpoints have a
    // single edge, where the bisector degenerates to that edge's normal.
    function offsetVertexCoords(guideCoords, halfD, side) {
        const out = [];
        const last = guideCoords.length - 1;
        const sideSign = side === 'left' ? -1 : 1;

        for (let i = 0; i <= last; i++) {
            if (i === 0 || i === last) {
                const u = i === 0
                    ? unitVectorMetres(guideCoords[0], guideCoords[1])
                    : unitVectorMetres(guideCoords[last - 1], guideCoords[last]);
                out.push([offsetAlongNormal(guideCoords[i], u.x, u.y, sideSign, halfD)]);
                continue;
            }

            const incoming = unitVectorMetres(guideCoords[i - 1], guideCoords[i]);
            const outgoing = unitVectorMetres(guideCoords[i], guideCoords[i + 1]);
            const bxRaw = incoming.x + outgoing.x;
            const byRaw = incoming.y + outgoing.y;
            const bisectorLen = Math.hypot(bxRaw, byRaw);

            if (bisectorLen < 1e-9) {
                // Exact reversal — no bisector exists. Follow the outgoing edge.
                out.push([offsetAlongNormal(guideCoords[i], outgoing.x, outgoing.y, sideSign, halfD)]);
                continue;
            }

            // cross > 0 means the path turns left at this vertex.
            const cross = incoming.x * outgoing.y - incoming.y * outgoing.x;
            // On the convex (outside) side of a bend a miter overshoots, so the true
            // parallel there is an arc instead.
            const convex = (cross > 0) !== (sideSign < 0);

            if (convex) {
                out.push(offsetArcPoints(guideCoords[i], incoming, outgoing, sideSign, halfD));
            } else {
                // |u + v| = 2·cos(theta/2) for deflection theta, so 2/|u + v| is exactly
                // the 1/cos(theta/2) miter factor. Done with vectors, so it is immune to
                // the 0°/360° wrap that averaging bearings would hit. Without the factor
                // the offset pinched by cos(theta/2) — measured 12.37m instead of 17.5m
                // at a 90° corner on a 35m gap.
                const miterFactor = Math.min(OFFSET_MITER_MAX, 2 / bisectorLen);
                out.push([
                    offsetAlongNormal(
                        guideCoords[i], bxRaw / bisectorLen, byRaw / bisectorLen, sideSign, halfD, miterFactor
                    )
                ]);
            }
        }

        return out;
    }

    // ─── canonicalOffsetVertex: the one position representing a vertex ─────
    // Used where a node lands exactly on a guide vertex, so both adjacent segments
    // agree on it. For a miter that is the miter point; for an arc it is the middle
    // point, i.e. the bisector direction at radius halfD.
    function canonicalOffsetVertex(group) {
        return group[Math.floor(group.length / 2)];
    }

    // ─── distanceMetres: local planar distance between two lon/lat coords ───
    // Equirectangular scaling at the mean latitude — far more accurate than the
    // lengths a drawn guide line has.
    function distanceMetres(a, b) {
        const kx = Math.cos(((a[1] + b[1]) / 2) * Math.PI / 180);
        const dx = (b[0] - a[0]) * kx;
        const dy = b[1] - a[1];
        return Math.hypot(dx, dy) * (Math.PI / 180) * 6371008.8;
    }

    // ─── cumulativeLengthsM: running length of a lon/lat polyline in metres ──
    function cumulativeLengthsM(coords) {
        const cum = [0];
        for (let i = 0; i + 1 < coords.length; i++) {
            cum.push(cum[i] + distanceMetres(coords[i], coords[i + 1]));
        }
        return cum;
    }

    // ─── offsetPositionAt: the point `dist` metres along the guide, offset halfD ──
    // Strictly inside an edge the offset uses THAT edge's normal, which keeps the
    // point directly opposite the guide position it came from — no along-track drift.
    // On a vertex the vertex's canonical offset is used instead, so a corner is not
    // pinched and both neighbouring segments pick the same point.
    function offsetPositionAt(sliceCoords, vertexGroups, cum, dist, halfD, side) {
        const last = sliceCoords.length - 1;
        let k = 0;
        while (k < last - 1 && cum[k + 1] < dist) k++;

        const edgeLen = cum[k + 1] - cum[k];
        const t = edgeLen > 0 ? (dist - cum[k]) / edgeLen : 0;

        if (t <= VERTEX_EPS) return canonicalOffsetVertex(vertexGroups[k]);
        if (t >= 1 - VERTEX_EPS) return canonicalOffsetVertex(vertexGroups[k + 1]);

        const a = sliceCoords[k];
        const b = sliceCoords[k + 1];
        const u = unitVectorMetres(a, b);
        const point = [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t];
        return offsetAlongNormal(point, u.x, u.y, side === 'left' ? -1 : 1, halfD);
    }

    // ─── offsetSliceSegment: the offset geometry for one segment's span ────
    // Walks from dStart to dEnd: the two interpolated endpoints plus every guide
    // vertex strictly between them (contributing its miter or arc points).
    function offsetSliceSegment(sliceCoords, vertexGroups, cum, dStart, dEnd, halfD, side) {
        const out = [offsetPositionAt(sliceCoords, vertexGroups, cum, dStart, halfD, side)];
        for (let j = 1; j < sliceCoords.length - 1; j++) {
            if (cum[j] > dStart + VERTEX_EPS_M && cum[j] < dEnd - VERTEX_EPS_M) {
                out.push(...vertexGroups[j]);
            }
        }
        out.push(offsetPositionAt(sliceCoords, vertexGroups, cum, dEnd, halfD, side));

        // A span shorter than the vertex tolerance can land both endpoints on the same
        // vertex. WME rejects single-point geometry, and Step 8's collapse guard needs
        // two points to measure, so close it with a near-zero stub; the guard then
        // aborts the run cleanly instead of writing bad geometry.
        if (out.length < 2) out.push([out[0][0] + 1e-9, out[0][1] + 1e-9]);
        return out;
    }

    // ─── junctionAtEnd / junctionIndex: where a split's junction node goes ────
    // The junction with the PREVIOUS segment sits at the END of the produced geometry
    // for AB/AA and at the START for BA/BB. This rule used to be duplicated — once as
    // the endpoint adjustment in createSegments() and once as the endpoint read in
    // executeSplitMutations() — and the two copies have to agree or the point handed to
    // AddNode is not the coordinate the geometry was written with. It lives here once.
    const junctionAtEnd = (connMode) => connMode === 'AB' || connMode === 'AA';

    // Index of that endpoint inside a carriageway's coordinates. The two carriageways
    // are produced in OPPOSITE directions, so the junction is at the end of the LEFT
    // geometry and the start of the RIGHT one (mirrored for BA/BB).
    function junctionIndex(coords, connMode, isLeft) {
        const atEnd = junctionAtEnd(connMode);
        return (isLeft ? atEnd : !atEnd) ? coords.length - 1 : 0;
    }

    // ─── parallelJunctionPoint: where two carriageways' offset lines cross ────
    // At an INTERIOR junction of a multi-segment split the node has to sit where the two
    // carriageways actually meet while BOTH stay parallel to their own segment — the
    // intersection of the two offset lines. Placing it on the previous carriageway's own
    // endpoint (the earlier behaviour) puts it on only ONE of the two offset lines, so the
    // following carriageway gets dragged off its line: it kinks at the junction, stops
    // being parallel, and at a bend the node slides away from the perpendicular of the
    // shared junction node.
    //
    // prevSide  – the previous carriageway's junction-side endpoint (it lies on its line)
    // prevInner – the adjacent vertex of that carriageway, fixing its direction
    // currOrigEdge – [junctionEnd, innerVertex] of the CURRENT segment's ORIGINAL geometry
    // node      – the shared junction node's coordinate
    // halfD     – the carriageway offset
    // Returns the junction coordinate, or null when the two lines are collinear (a
    // straight-through junction), where the previous endpoint already IS the junction.
    function parallelJunctionPoint(prevSide, prevInner, currOrigEdge, node, halfD) {
        if (!prevSide || !prevInner || !currOrigEdge || !node) return null;
        const [currAtNode, currAway] = currOrigEdge;

        // Local metric frame centred on the shared node: lon/lat degrees are not
        // isotropic, so every direction and intersection below is computed in metres.
        const MPERDEG = Math.PI / 180 * 6371008.8;
        const kx = Math.cos(node[1] * Math.PI / 180);
        const toXY = (c) => ({ x: (c[0] - node[0]) * kx * MPERDEG, y: (c[1] - node[1]) * MPERDEG });
        const toLonLat = (p) => [node[0] + p.x / (kx * MPERDEG), node[1] + p.y / MPERDEG];

        const A = toXY(prevSide);
        const dIn = unitVectorMetres(prevInner, prevSide);   // chain direction INTO the junction
        const dOut = unitVectorMetres(currAtNode, currAway); // chain direction OUT of the junction
        const e = unitVectorMetres(node, prevSide);          // which side the previous carriageway is on

        // The current carriageway is the current segment's own offset, on the SAME side of
        // the chain as the previous carriageway. "Same side" is measured against the CHAIN
        // direction — not against the segment's own A→B sense, which can point either way
        // depending on how the segment happens to be stored — and that is what keeps this
        // free of the from/to convention.
        const sPrev = Math.sign(dIn.x * e.y - dIn.y * e.x) || 1;
        const left = { x: -dOut.y, y: dOut.x };
        const B = { x: sPrev * left.x * halfD, y: sPrev * left.y * halfD }; // offset point, relative to the node

        const denom = dIn.x * dOut.y - dIn.y * dOut.x;
        // Straight-through junction: the two offset lines are parallel, so their
        // intersection cannot be evaluated — only approached as a limit, and that limit is
        // the PERPENDICULAR FOOT of the shared node, which is exactly where prevSide already
        // sits. This case used to return null and fall back to the cached coordinate, and
        // THAT is the path a straight junction takes: the cache is a different carriageway's
        // earlier endpoint rather than a point derived from this node, and unlike every bent
        // junction it also skipped pullCarriagewayEnd, so the previous carriageway kept its
        // own endpoint and the node never ended up on the shared point's perpendicular.
        if (Math.abs(denom) < 1e-9) {
            const footDist = Math.hypot(A.x, A.y);
            // Self-check: prevSide must BE that foot, i.e. halfD from the node. If the end
            // nearest the node is not the node's own offset point, this shortcut would be
            // wrong too — decline instead of placing a node on trust.
            if (Math.abs(footDist - halfD) > ADD_NODE_TOLERANCE_M) {
                console.warn(`${scriptName} parallelJunctionPoint: the previous carriageway's junction end is ` +
                    `${footDist.toFixed(3)}m from the shared node (expected ${halfD.toFixed(3)}m) — not using the collinear shortcut`);
                return null;
            }
            return toLonLat(A);
        }

        // Intersect prev's offset line (through A, direction dIn) with curr's (through B,
        // direction dOut): A + t·dIn = B + u·dOut.
        let t = ((B.x - A.x) * dOut.y - (B.y - A.y) * dOut.x) / denom;

        // Bound the miter so a very sharp bend cannot throw the node far from the junction.
        // The clamp slides along PREV's line, so that carriageway still ends exactly where
        // its own offset line runs; beyond ~120° of bend no single point is on both lines,
        // and this keeps the compromise on the side that has already been written.
        const maxM = halfD * OFFSET_MITER_MAX;
        const aDotD = A.x * dIn.x + A.y * dIn.y;
        const tMax = -aDotD + Math.sqrt(Math.max(0, aDotD * aDotD - (A.x * A.x + A.y * A.y - maxM * maxM)));
        // A sharp bend puts the intersection BEHIND the node (t negative), so the bound is
        // on |t|, not t. Getting this wrong let a 150° junction place the node twice as far
        // out as the cap allows.
        if (Math.abs(t) > tMax) t = Math.sign(t) * tMax;

        const M = { x: A.x + dIn.x * t, y: A.y + dIn.y * t };
        return toLonLat(M);
    }

    // ─── junctionEndOfOriginal: which end of the current segment meets the previous ones ──
    // Compared by COORDINATE, not by node id. A freshly split, unsaved segment does not
    // report usable from/to node ids — observed on a real run, where intersecting the
    // carriageways' node-id sets with the current segment's came back EMPTY and the whole
    // junction snap silently fell back — but its original geometry's two endpoints ARE the
    // two nodes. Returns the end and inner indices into currCoords, or null when the two
    // ends are comparably close (a short segment between junctions) and guessing an end
    // would be worse than falling back to the cached coordinate.
    function junctionEndOfOriginal(currCoords, prevEnds) {
        if (!currCoords || currCoords.length < 2 || !prevEnds || prevEnds.length === 0) return null;
        const last = currCoords.length - 1;
        const nearestPrev = (c) => Math.min(...prevEnds.map((p) => distanceMetres(c, p)));
        const dStart = nearestPrev(currCoords[0]);
        const dEnd = nearestPrev(currCoords[last]);

        const nearD = Math.min(dStart, dEnd);
        const farD = Math.max(dStart, dEnd);
        if (farD < Math.max(2 * nearD, 1)) return null;

        return dStart <= dEnd ? { end: 0, inner: 1 } : { end: last, inner: last - 1 };
    }

    // ─── parallelJunctionSnap: the junction point for one interior junction ──
    // Gathers what parallelJunctionPoint() needs for the left and the right carriageway.
    // The shared node is located geometrically, from the current segment's ORIGINAL
    // endpoints, because the previous carriageways are freshly split and unsaved and so
    // cannot be relied on to report node ids (see junctionEndOfOriginal).
    function parallelJunctionSnap(prevLeftId, prevRightId, currSeg, halfD) {
        const prevLeftSdk  = sdk.DataModel.Segments.getById({ segmentId: prevLeftId });
        const prevRightSdk = sdk.DataModel.Segments.getById({ segmentId: prevRightId });
        if (!prevLeftSdk || !prevRightSdk || !currSeg) return null;

        const prevEnds = [];
        for (const seg of [prevLeftSdk, prevRightSdk]) {
            const coords = seg.geometry?.coordinates;
            if (coords && coords.length >= 2) prevEnds.push(coords[0], coords[coords.length - 1]);
        }
        if (prevEnds.length === 0) {
            console.log(`${scriptName} parallelJunctionSnap: no usable previous carriageway geometry`);
            return null;
        }

        const origCoords = currSeg.geometry.coordinates;
        const ends = junctionEndOfOriginal(origCoords, prevEnds);
        if (!ends) {
            console.log(`${scriptName} parallelJunctionSnap: could not tell which end of seg ${currSeg.id} meets the previous carriageways — using the cached coordinate`);
            return null;
        }

        // The shared junction node IS this original endpoint. createSegments is about to
        // overwrite the geometry, so the edge is captured now: after the split the junction
        // vertex already carries the previous carriageway's coordinate and the edge through
        // it lies on neither offset line.
        const nodeCoord = origCoords[ends.end];
        const currEdge = [origCoords[ends.end], origCoords[ends.inner]];

        const pointFor = (prevSeg) => {
            const coords = prevSeg.geometry.coordinates;
            const idx = nearestEndIndex(coords, nodeCoord).index;
            const inner = idx === 0 ? 1 : idx - 1;
            if (inner < 0 || inner >= coords.length) return null;
            return parallelJunctionPoint(coords[idx], coords[inner], currEdge, nodeCoord, halfD);
        };

        const snap = { left: pointFor(prevLeftSdk), right: pointFor(prevRightSdk), node: nodeCoord };
        console.log(`${scriptName} parallelJunctionSnap: seg ${currSeg.id} junction at its ` +
            `${ends.end === 0 ? 'start' : 'end'} [${nodeCoord[0].toFixed(6)},${nodeCoord[1].toFixed(6)}] —`,
            'left=', snap.left ? JSON.stringify(snap.left) : 'collinear (cached end used)',
            'right=', snap.right ? JSON.stringify(snap.right) : 'collinear (cached end used)');
        return snap;
    }

    // ─── nearestEndIndex: closest end of a geometry to a coordinate ──────────
    // Used by the AddNode check below, which must not assume anything about which end
    // a segment was written with — it measures instead.
    function nearestEndIndex(coords, coordinate) {
        const first = distanceMetres(coordinate, coords[0]);
        const last = distanceMetres(coordinate, coords[coords.length - 1]);
        return first <= last ? { index: 0, distance: first } : { index: coords.length - 1, distance: last };
    }

    // ─── logAddNodeCheck: measures the AddNode placement error ───────────────
    // The node is created from ONE point, read back out of the current segment's
    // geometry. Placement is only correct if that point also sits on the facing end of
    // the segment being joined to it; otherwise WME pulls that segment across to meet
    // the node and the junction silently moves. Both distances are reported against
    // whichever end is nearest, so no end convention is assumed here.
    // ─── junctionDeflectionDeg: how sharply a carriageway turns at its junction end ──
    // The angle between the edge that ends at the junction and the next edge inward.
    // 0° = the carriageway runs straight through, which is what a correct junction looks
    // like on a straight road. This is the measurement that shows a KINKED junction: a
    // point-coincidence check cannot, because a carriageway whose end has been written onto
    // the other carriageway's endpoint IS an endpoint of both segments (distance 0.000m)
    // while being visibly bent there. A junction between two different original segments
    // legitimately shows the road's own bend, so read the value against how straight the
    // road is at that node.
    function junctionDeflectionDeg(coords, nodeCoord) {
        const idx = nearestEndIndex(coords, nodeCoord).index;
        const step = idx === 0 ? 1 : -1;
        const a = coords[idx];
        const b = coords[idx + step];
        const c = coords[idx + 2 * step];
        if (!b || !c) return null;

        const u1 = unitVectorMetres(a, b);  // leaving the junction
        const u2 = unitVectorMetres(b, c);  // the next edge inward
        if ((u1.x === 0 && u1.y === 0) || (u2.x === 0 && u2.y === 0)) return null;

        const dot = Math.max(-1, Math.min(1, u1.x * u2.x + u1.y * u2.y));
        return Math.acos(dot) * 180 / Math.PI;
    }

    function logAddNodeCheck(label, point, prevSeg, currSeg) {
        const prevCoords = prevSeg?.geometry?.coordinates;
        const currCoords = currSeg?.geometry?.coordinates;
        if (!point || !prevCoords?.length || !currCoords?.length) return;

        const prev = nearestEndIndex(prevCoords, point.coordinates);
        const curr = nearestEndIndex(currCoords, point.coordinates);
        // The deflection is reported alongside the distances because the distance ALONE
        // cannot tell a good junction from a snapped one: writing the new carriageway's end
        // onto the previous carriageway's endpoint makes the point an endpoint of both
        // segments, so it reads 0.000m while the carriageway is kinked there.
        const prevTurn = junctionDeflectionDeg(prevCoords, point.coordinates);
        const currTurn = junctionDeflectionDeg(currCoords, point.coordinates);
        const asDeg = (t) => (t === null ? 'n/a' : `${t.toFixed(1)}°`);

        const detail = `${scriptName}   AddNode ${label}: point=[${point.coordinates[0].toFixed(6)},${point.coordinates[1].toFixed(6)}]` +
            `  to prev end #${prev.index} = ${prev.distance.toFixed(3)}m` +
            `  to curr end #${curr.index} = ${curr.distance.toFixed(3)}m` +
            `  deflection prev=${asDeg(prevTurn)} curr=${asDeg(currTurn)}`;

        if (Math.max(prev.distance, curr.distance) > ADD_NODE_TOLERANCE_M) {
            console.warn(`${detail}  ← MISMATCH (tolerance ${ADD_NODE_TOLERANCE_M}m; WME will move a segment to meet this node)`);
        } else {
            log(`${detail}  ok`);
        }
    }

    // ─── logJunctionOffset: is the node where the shared point says it should be? ──
    // Decomposes the node's displacement from the SHARED junction node into "along the road"
    // and "perpendicular". A straight junction (both carriageways' edges at the node nearly
    // parallel) must be almost purely perpendicular; an along-road component there means the
    // node did not land on the shared point's perpendicular and a carriageway has to kink to
    // reach it. A bend legitimately has both, since its node sits on the bisector.
    function logJunctionOffset(label, point, nodeCoord, prevSeg, currSeg, halfD) {
        if (!point || !nodeCoord) return;
        const prevCoords = prevSeg?.geometry?.coordinates;
        const currCoords = currSeg?.geometry?.coordinates;
        if (!prevCoords?.length || !currCoords?.length) return;

        const edgeDir = (coords) => {
            const idx = nearestEndIndex(coords, nodeCoord).index;
            const inner = idx === 0 ? 1 : idx - 1;
            if (inner < 0 || inner >= coords.length) return null;
            return unitVectorMetres(coords[inner], coords[idx]);
        };
        const u = edgeDir(prevCoords);
        const v = edgeDir(currCoords);
        if (!u || !v) return;

        // Local metric frame centred on the shared node.
        const MPERDEG = Math.PI / 180 * 6371008.8;
        const kx = Math.cos(nodeCoord[1] * Math.PI / 180);
        const vec = {
            x: (point.coordinates[0] - nodeCoord[0]) * kx * MPERDEG,
            y: (point.coordinates[1] - nodeCoord[1]) * MPERDEG
        };
        const perp = Math.abs(vec.x * u.y - vec.y * u.x);
        const along = Math.abs(vec.x * u.x + vec.y * u.y);
        const angleDeg = Math.acos(Math.max(-1, Math.min(1, u.x * v.x + u.y * v.y))) * 180 / Math.PI;

        const detail = `${scriptName}   junction ${label}: node is ${perp.toFixed(3)}m perpendicular / ` +
            `${along.toFixed(3)}m along the road from the shared point` +
            `  (junction angle ${angleDeg.toFixed(2)}°, want perp ${halfD.toFixed(2)}m)`;

        if (angleDeg < 1 && along > 0.5) {
            console.warn(`${detail}  ← MISMATCH: this junction is straight, so the along-road part should be ~0`);
        } else {
            log(`${detail}`);
        }
    }

    // ─── verifyAddNodes: confirm each dispatched AddNode really joined its pair ──
    // The SDK has no node-creation call — the beta Nodes class exposes only
    // allowNodeTurns / canEdit / canEditTurns / getAll / getById / isVirtual / moveNode —
    // so the junction node is created through the legacy Waze/Action/AddNode action. That
    // action can, in principle, attach to the wrong segments or to none at all, and it
    // reports nothing. The SDK can then tell us what actually happened: getById() returns
    // the node's geometry and connectedSegmentIds, which is the only trustworthy check
    // that the placement worked.
    function verifyAddNodes(wrappers) {
        for (const wrapper of wrappers) {
            const node = wrapper.node;
            if (!node) {
                console.warn(`${scriptName} AddNode check: the action produced no node`);
                continue;
            }

            const nodeId = typeof node.getID === 'function' ? node.getID() : node.attributes?.id;
            let sdkNode = null;
            try {
                sdkNode = sdk.DataModel.Nodes.getById({ nodeId });
            } catch (ex) {
                console.warn(`${scriptName} AddNode check: node ${nodeId} lookup threw:`, ex);
                continue;
            }
            if (!sdkNode) {
                console.warn(`${scriptName} AddNode check: node ${nodeId} is missing from the SDK model`);
                continue;
            }

            const connected = Array.isArray(sdkNode.connectedSegmentIds) ? sdkNode.connectedSegmentIds : [];
            const intended = wrapper.intendedSegmentIds ?? [];
            const missing = intended.filter((segId) => !connected.includes(segId));
            const drift = wrapper.intendedPoint
                ? distanceMetres(wrapper.intendedPoint, sdkNode.geometry.coordinates)
                : null;

            // NOTE: Nodes.isVirtual() is reported only for context. In WME a node joining
            // exactly two segments IS still "virtual" (a geometry node), so a true value
            // here is expected and is not a failure.
            let isVirtual = null;
            try {
                isVirtual = sdk.DataModel.Nodes.isVirtual({ nodeId });
            } catch (ex) { /* reported as null */ }

            const detail = `${scriptName} AddNode check: node ${nodeId} connected=[${connected.join(', ')}]` +
                ` (wanted both of [${intended.join(', ')}])` +
                (drift === null ? '' : `  drift=${drift.toFixed(3)}m`) +
                (isVirtual === null ? '' : `  isVirtual=${isVirtual}`);

            if (connected.length < 2 || missing.length > 0) {
                console.warn(`${detail}  ← MISMATCH: the node did not attach to both segments`);
            } else if (drift !== null && drift > ADD_NODE_TOLERANCE_M) {
                console.warn(`${detail}  ← MISMATCH: node placed off the intended point`);
            } else {
                log(`${detail}  ok`);
            }
        }
    }

    // ─── createSegments: split one segment and compute offset geometries ──────
    // 
    // NOTE: OpenLayers geometry operations (rotate, resize, clone on OL.Geometry.Point)
    // are replaced here with turf.js equivalents.
    // turf works in WGS84 (lon/lat). WME SDK segment.geometry is a GeoJSON LineString
    // already in WGS84.
    //
    function createSegments(sel, displacement, connMode, junctionSnap = null) {
        console.log(`${scriptName} createSegments: segId=`, sel.id, 'displacement=', displacement, 'connMode=', connMode, 'junctionSnap=', junctionSnap);
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

            // Half the gap in kilometres — the unit turf.destination expects.
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
        console.log(`${scriptName} createSegments: calling SplitSegment, leftPoints=`, leftPoints.length, 'rightPoints=', rightPoints.length);
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

        // Adjust endpoints to match previous iteration's cached connector coords.
        // junctionIndex() is the same rule executeSplitMutations() reads back with, so
        // the AddNode point is exactly the coordinate written here.
        //
        // junctionSnap (interior multi-segment junctions) wins when present: it is the
        // intersection of the two offset lines, the only point that keeps BOTH carriageways
        // parallel. It is null for a straight-through junction, where the two lines are
        // collinear and the cached connector coordinate is already exact.
        const cacheReady = last_coord_left_first !== null && last_coord_left_last !== null &&
            last_coord_right_first !== null && last_coord_right_last !== null;
        if (junctionSnap?.left || junctionSnap?.right || cacheReady) {
            const atEnd = junctionAtEnd(connMode);
            const snapLeft  = junctionSnap?.left  ?? (cacheReady ? (atEnd ? last_coord_left_first  : last_coord_left_last)  : null);
            const snapRight = junctionSnap?.right ?? (cacheReady ? (atEnd ? last_coord_right_last  : last_coord_right_first) : null);

            if (snapLeft)  leftPoints[junctionIndex(leftPoints, connMode, true)]    = snapLeft;
            if (snapRight) rightPoints[junctionIndex(rightPoints, connMode, false)] = snapRight;
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

        console.log(`${scriptName} createSegments: updateSegment geometry left=`, leftSegId, 'right=', rightSegId);
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

        console.log(`${scriptName} createSegments done — returning`, splitIds);
        return splitIds;
    }
    // Replaces legacy Waze/Action/SplitSegments require() pattern.
    // SDK: DataModel.Segments.splitSegment({ segmentId, splitPoint: GeoJSON Point })
    //
    function SplitSegment(seg) {
        console.log(`${scriptName} SplitSegment: segId=`, seg.id, 'coords=', seg.geometry.coordinates.length);
        if (!sdk.DataModel.Segments.hasPermissions({ segmentId: seg.id })) {
            console.log(`${scriptName} SplitSegment: no permissions for segment`, seg.id);
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

  function scriptupdatemonitor() {
    if (WazeToastr?.Ready) {
      // Create and start the ScriptUpdateMonitor
      // For GitHub raw URLs, we need to specify metaUrl explicitly (same as downloadUrl for GitHub)
      const updateMonitor = new WazeToastr.Alerts.ScriptUpdateMonitor(
        scriptName,
        scriptVersion,
        downloadUrl,
        GM_xmlhttpRequest,
        downloadUrl, // metaUrl - for GitHub, use the same URL as it contains the @version tag
        /@version\s+(.+)/i, // metaRegExp - extracts version from @version tag
      );
      updateMonitor.start(2, true); // Check every 2 hours, check immediately

      // Show the update dialog for the current version
      WazeToastr.Interface.ShowScriptUpdate(scriptName, scriptVersion, updateMessage, downloadUrl, forumURL);
    } else {
      setTimeout(scriptupdatemonitor, 250);
    }
  }
  scriptupdatemonitor();
    bootstrap();

})();

/* Changelog 
2026.09.25.10 - Split: a STRAIGHT junction now gets the shared point's perpendicular foot:
                 - REPORT: "where the connected segment is straight ... the added addnode is not
                   parallel/perpendicular to the old shared point". Bends were fine; only the
                   straight-through junction was off.
                 - WHY: parallelJunctionPoint() returns the intersection of the two offset
                   lines, which does not exist when those lines are parallel — i.e. exactly at
                   a straight-through junction. That case returned null and fell back to the
                   cached coordinate: the PREVIOUS carriageway's earlier endpoint rather than a
                   point derived from this junction's node, and unlike every bent junction it
                   also skipped pullCarriagewayEnd. So the straight junction was the one case
                   never positioned from its own shared point.
                 - FIX: the limit of that intersection as the bend closes is the PERPENDICULAR
                   FOOT of the shared node, which is where the previous carriageway's junction
                   end already sits. Return it. A self-check refuses the shortcut with a warning
                   unless that endpoint really is halfD from the node, so nothing is placed on
                   trust.
                 - ADD: logJunctionOffset() splits the node's displacement from the shared point
                   into PERPENDICULAR and ALONG-ROAD metres and warns when a straight junction
                   (edges within 1°) has a non-zero along-road part. Neither existing check could
                   see this: the distance-to-endpoints check reads 0.000m, and the deflection
                   check measures the bend just INSIDE the segment, not the placement.
                 - Harness: the 0° case now expects the perpendicular foot instead of a null
                   fallback, and 0.05°/0.5° were added to show the along-road part vanishing as
                   the junction straightens (0.0011m / 0.0109m, then 0.000000m). The module
                   constants the extracted functions rely on are now injected from the
                   userscript rather than re-typed, so the two cannot drift apart.
2026.09.25.09 - Cleanup: removed three pieces of dead code. No behaviour change.
                 Found by counting every reference to each identifier in the file and
                 ignoring the changelog text itself:
                 - drivableRoadIds — left over from the deactivated road-conversion code and
                   never read. Its own comment said it was "kept for reference", which is how
                   dead code survives.
                 - segLenKm in createSegments() — turf.distance computed for every edge of
                   every split segment and never used; only halfDKm (the gap in km) is needed.
                 - baseDirection — write-only state: declared, reset on every run, assigned at
                   the first junction, logged... and never read. The per-segment line already
                   reports connMode for every junction, so the log loses nothing.
                 Also removed a duplicated blank console.log('') in the test harness.
2026.09.25.08 - Split: the junction check now reports the KINK, not just the distance:
                 - WHY: on the .06 run the placement check printed "to prev end #0 = 0.000m
                   to curr end #14 = 0.000m ok" for a junction that was visibly kinked on the
                   map. When the new carriageway's end is written ONTO the previous
                   carriageway's endpoint, that point IS an endpoint of both segments — so
                   the distance is 0.000m no matter how badly the carriageway is bent there.
                   A point-coincidence check cannot see a snap onto the wrong line.
                 - ADD: junctionDeflectionDeg() — the angle between the edge ending at the
                   junction and the next edge inward — and logAddNodeCheck() prints it for
                   both participating segments. 0.0° means the carriageway runs straight
                   through the node. On a straight road that is the number to read; a
                   junction between two different original segments legitimately shows the
                   road's own bend instead.
                 - This is the measurement that should have caught the kink in the first place,
                   so it is now part of every split run's console output.
2026.09.25.07 - Split: the interior-junction lookup no longer depends on node ids:
                 - FIX: on a real run the shared node was found by intersecting the previous
                   carriageways' node-id sets with the current segment's, and it came back
                   EMPTY ("expected one shared node, got []") for a correct AA junction. The
                   carriageways are freshly split and unsaved, so their from/to node ids are
                   not dependable. The junction is now located GEOMETRICALLY: the shared node
                   is whichever endpoint of the current segment's ORIGINAL geometry lies
                   nearest the previously written carriageway ends. An endpoint IS its node,
                   so no id is needed.
                 - So a straight-through junction is no longer the only fallback — the previous
                   version silently used the cached coordinate for EVERY junction, which is
                   why the placement could still be wrong at a bend.
                 - junctionEndOfOriginal() refuses to guess when the segment's two ends are
                   comparably close (a short segment between two junctions); that falls back
                   to the cached coordinate, which at least stays self-consistent.
                 - HARDENING: the turn-allowance pass now treats a missing node id as missing
                   rather than as "not null", and warns when NONE of the produced segments
                   exposed from/to node ids. The same unsaved-segment behaviour can make that
                   pass a silent no-op, which would leave turns closed at new junctions — the
                   warning makes it visible instead of looking like it worked.
                 - Added junctionEndOfOriginal coverage to tools/junction-miter-test.js.
2026.09.25.06 - Split: interior junction node placed at the carriageways' TRUE intersection:
                 - FIX: at an interior junction of a multi-segment split the node was placed on
                   the PREVIOUS carriageway's own offset endpoint, and the next carriageway's
                   end was snapped onto it. That point lies on only ONE of the two offset
                   lines, so at a bend the following carriageway got dragged off its own
                   line — it kinked at the junction and stopped being parallel, and the node
                   fell away from the shared junction node's perpendicular while the previous
                   carriageway kept its own endpoint. parallelJunctionPoint() now intersects
                   the two offset lines, so BOTH carriageways stay parallel and the node sits
                   where they actually meet: halfD/cos(theta/2) along the bisector, which is
                   exactly halfD perpendicular when the junction is straight through.
                 - Both carriageways' junction endpoints are now written to that point (see
                   pullCarriagewayEnd), so the node, the previous carriageway and the new
                   segment all agree on where the junction is.
                 - The shared node is found by intersecting the node-id SETS of the two
                   carriageways and the current segment, rather than by the from/to A-B
                   convention — one less place that convention can be got wrong.
                 - A straight-through junction makes the two offset lines collinear, so the
                   intersection is undefined; parallelJunctionPoint() returns null there and
                   the cached-coordinate path is used, which is already exact at that angle.
                 - The junction point is computed BEFORE the split, because the current
                   segment's ORIGINAL geometry is needed: once the junction vertex carries the
                   previous carriageway's coordinate, the edge through it is on neither offset
                   line.
                 - Added tools/junction-miter-test.js.
2026.09.25.05 - Split: AddNode junction rule made a single source of truth, and measured:
                 - FIX: the "SDK segment not found" fallback in executeSplitMutations() selected the
                   OPPOSITE end of both carriageways from the live-model path — it read
                   last_coord_left_first where the geometry had been written with
                   last_coord_left_last, and vice versa. On that path the AddNode point was
                   roughly a whole segment length from the junction, so WME had to drag a
                   segment across to meet the new node.
                 - REFACTOR: the AB/AA-vs-BA/BB end convention was duplicated — once as the
                   endpoint adjustment in createSegments(), once as the endpoint read in
                   executeSplitMutations(). It is now junctionAtEnd()/junctionIndex(), so the
                   point handed to AddNode is by construction the coordinate the geometry was
                   written with, including that the two carriageways run in opposite
                   directions (junction at the END of the left geometry, the START of the right).
                 - ADD: logAddNodeCheck() measures, per AddNode, the distance from the chosen
                   point to the nearest end of BOTH participating segments — deliberately
                   convention-free — and console.warns above ADD_NODE_TOLERANCE_M = 0.05m.
                   Run a multi-segment split with DEBUG on and the console now reports the real
                   placement error instead of us assuming it is correct.
                 - ADD: a warning when a segment pair cannot be classified as AB/BA/AA/BB.
                   connMode was only ever assigned, never cleared, so an unmatched pair
                   silently reused the PREVIOUS iteration's mode, aiming the endpoint
                   adjustment at the wrong end. Behaviour is unchanged (it still reuses the
                   mode) but the condition is now visible; whether to skip the join instead
                   needs a real test.
                 - NOTE: the WME SDK still has no AddNode equivalent, so multi-segment junction
                   creation remains on the legacy Waze/Action/AddNode path. Confirmed against
                   the beta docs: the Nodes class exposes only allowNodeTurns / canEdit /
                   canEditTurns / getAll / getById / isVirtual / moveNode — there is no
                   node-creation method, and Segment.geometry is a GeoJSON LineString whose
                   coordinate order relative to fromNodeId/toNodeId is not documented.
                 - ADD: verifyAddNodes() asks the SDK what each dispatched AddNode produced —
                   the node's connectedSegmentIds must be exactly the two participants it was
                   given, and its geometry must match the intended point — because the legacy
                   action reports nothing and could attach to the wrong segments or to none.
                   Nodes.isVirtual() is logged for context only: a node joining exactly two
                   segments is still "virtual" in WME, so true is expected, not a failure.
                 - CAUTION: the placement check compares geometry endpoints, but the SDK does
                   not document which end of a LineString corresponds to fromNodeId. Every
                   inference here rests on the conventional from-node-to-to-node ordering; a
                   real split run is what will confirm it.
2026.09.25.04 - "Make it parallel" now places nodes by ARC LENGTH and rounds convex corners:
                 - FIX: nodes are positioned by walking the guide to the node's arc length and
                   stepping halfD along the LOCAL edge normal there. Previously a guide
                   fraction was mapped onto a fraction of the offset line's own length, which
                   assumed the offset stretches the guide proportionally. It cannot: at a bend
                   each guide leg shortens by a constant halfD*tan(theta/2), so on a corner
                   with uneven legs an interior node slid ALONG the curve. Measured drift at
                   the worst vertex: 15.83m (legs 20m|400m), 13.61m (50m|400m), 7.95m
                   (150m|400m), 6.06m (60 deg, 100m|400m), 2.81m (30 deg, 100m|400m); symmetric
                   corners were already 0.00m. Now ~0 in all cases.
                 - FIX: the convex (outside) side of a bend gets a rounded join — an arc of
                   radius halfD centred on the vertex — instead of a miter. A miter there sits
                   halfD/cos(theta/2) from the vertex because both perpendicular feet fall
                   beyond the edges: measured 24.75m where 17.5m was asked for, at a 90 deg
                   corner on a 35m gap. The concave (inside) side keeps the miter, which is
                   already exact at halfD.
                 - Removed the slice-subdivision step. It sampled extra points along the guide
                   slice, but extra points on a straight edge offset to collinear points, so it
                   never changed the shape — it only inflated the vertex count written into WME.
                 - The old per-vertex offsetGuideLine() is gone. offsetVertexCoords() is the
                   per-vertex form: one entry per guide vertex, each an ARRAY of points (a
                   single miter point, or the points of a rounded join), so it must never be
                   indexed against the guide as a flat list. Nodes and geometry come from
                   offsetPositionAt()/offsetSliceSegment(), which work purely in arc length.
                 - tools/offset-test.js (new) pulls these helpers straight out of this file and
                   asserts (a) every offset point is exactly halfD from the guide, (b) each
                   vertex's node straddles that vertex symmetrically, and (c) the two
                   placement paths agree, so neighbouring segments cannot disagree on a
                   shared node. Its "old shift" column reproduces the pre-fix drift.
2026.09.25.03 - Hardened guide-line handling against repeated coordinates:
                 - FIX: the drawn guide line is de-duplicated (consecutive repeated points
                   dropped) before it is simplified and offset. A repeated point creates a
                   zero-length edge, which leaves the offset's angle bisector undefined and
                   makes turf.bearing() return 0 for that pair. Measured with the harness on
                   a guide with a tripled vertex: the offset used to collapse to a 0.00m
                   clearance vertex (a node sitting on the guide line) and spike to 24.75m;
                   it is now exact like every other case.
                 - The same fix covers determineSideOfLine(), which reads guideCoords[idx]
                   and guideCoords[idx + 1] to get the guide's bearing and would compare two
                   identical points after such a repeat.
                 - Idea and the de-duplication idiom borrowed from WazePT Segments
                   (greasyfork 406000, same original author J0N4S13), which offsets a
                   segment's own polyline in spherical Mercator and mitres corners by
                   intersecting consecutive offset edge lines.
                 - That algorithm was benchmarked against this one and matches it on
                   perpendicular accuracy (17.48m vs 17.50m on a 35m gap; the 2cm gap is its
                   Mercator-vs-ground-metre conversion). It was NOT adopted because
                   offsetPolyline() merges duplicate/collinear edges and so cannot preserve
                   the 1:1 vertex correspondence with the guide that Step 6's per-segment
                   slicing depends on.
2026.09.25.02 - Fixed "Make it parallel" not actually being parallel to the guide line:
                 - FIX: offsetGuideLine() now offsets along the normal to the angle BISECTOR of
                   each vertex's two edges by halfD / cos(theta/2) — the standard miter —
                   instead of stepping halfD along the chord between that vertex's two
                   neighbours. The old form left the offset only halfD * cos(theta/2) from the
                   guide, so the parallel pair pinched at EVERY bend. Measured on a 35m gap
                   with a Node/turf harness: 12.37m at a 90 degree corner (exactly
                   17.5 * cos 45), 15.15m at 60 degrees, and 0.87m where a corner had 20m and
                   400m legs. All vertices are now exactly halfD at every bend tested
                   (straight, 10/30/45/60/90 degrees, uneven legs, and two arcs).
                 - FIX: the chord bearing was only perpendicular when a vertex's two edges were
                   the same length, which is what made the uneven-leg corner collapse. The
                   bisector is perpendicular by construction, and it is computed from summed
                   unit vectors so it avoids the 0/360 degree wrap that averaging bearings
                   would hit.
                 - Miter length is capped (OFFSET_MITER_MAX = 2.0, i.e. deflections up to
                   120 degrees) so a near-reversal cannot fling the offset point outwards.
                   Past the cap a vertex under-offsets slightly instead of spiking.
                 - The harness lives outside the repo and extracts this function straight from
                   the userscript, so it measures the shipped code rather than a copy.
2026.09.25.01 - Re-added the wme-sdk-plus dependency (pinned to v1.4.1) and grouped both
                 features into single-undo transactions:
                 - ADD: @require for wme-sdk-plus @0b212bca, initialised with
                   initWmeSdkPlus(sdk, { hooks: ['Editing.Transactions'] }) once the SDK is
                   ready. That module supplies Editing.beginTransaction /
                   commitTransaction / cancelTransaction / doActions, for which the native
                   SDK has no equivalent (sdk.Editing only exposes undo / redo / undoAll).
                 - CHANGE: a split and a "make it parallel" run are now each ONE undo entry
                   instead of one per segment / node / turn mutation.
                 - CHANGE: failures now roll back atomically — a throw inside the
                   transaction discards every change that run had made, so a half-split road
                   or a partially reshaped junction can no longer be left behind.
                   executeSplit() gained a try/catch for this. The delta-based rollback in
                   applyMakeParallel() is retained solely as the no-transaction-support
                   fallback (it is a no-op after a transaction cancel).
                 - REFACTOR: executeSplit()'s mutation phase moved to executeSplitMutations()
                   so it can be handed to withTransaction() as a single synchronous
                   callback; applyMakeParallelCore() now returns true/false (false = a
                   pre-mutation validation abort) rather than raising its own success toast.
                 - Supersedes the 2026.07.26.02 note about doActions being unavailable: that
                   was a missing initWmeSdkPlus() call, not an absent method.
2026.09.24.01 - Hardened & tidied "Make it parallel":
                 - FIX: segment endpoints are now reconciled with the moved node positions
                   before geometry is written, so node and geometry always agree (no gaps or
                   kinks at shared nodes). Applies to every node, not just cross-side ones.
                 - FIX: turns are snapshotted before the move and the captured state (allowed
                   AND forbidden) is re-applied afterwards, instead of blanket
                   allowNodeTurns() which un-forbade unrelated turn restrictions at every
                   touched node. Each turn is restored in its own try/catch so one rejected
                   turn cannot abandon the rest, and nodes without turn-edit permission are
                   skipped.
                 - FIX: offsetGuideLine() averages middle-vertex bearings across the 0°/360°
                   wrap, which spiked the offset on north-crossing guides; now uses the
                   neighbour chord (turf.bearing(prev, next)).
                 - FIX: the distance input is validated (finite, > 0, <= 200m) in both entry
                   points, and a failure anywhere in the run now rolls back via
                   Editing.undo() — stopping as soon as the unsaved-change count stops
                   falling, so it can never revert edits made before the run.
                 - Guarded against starting a draw while one is already in progress, and
                   against a distance that would collapse a selected segment to a point
                   (checked before any mutation, so nothing needs rolling back).
                 - Cleanup: selected segments are cached (removes the O(n²) getById scan in
                   chain detection), validation uses nearestPointOnLine().properties.location
                   instead of a lineSlice+length round-trip per endpoint, the unused
                   totalSpanDeg/guideLineDbg rebuilds and the unreachable slice-direction
                   branch are gone, node/geometry state uses Maps instead of plain objects,
                   and all trace logging is gated behind DEBUG (false).
2026.07.27.11 - Removed cross-side node alignment (caused lane crossing). Keep per-side
                 projection ranges to prevent segment shortening. Independent chains on
                 opposite sides stay fully separate.
2026.07.27.10 - Fixed "Make it parallel" segment shortening: use per-side projection ranges
                 for fraction calculation (prevents clipping). Align paired junction nodes
                 across side groups in a post-processing step instead.
2026.07.27.09 - Fixed "Make it parallel" node misalignment: average projection positions of
                 paired segments across side groups.
2026.07.27.08 - Fixed "Make it parallel" node misalignment across lanes: use a shared global
                 projection range for both side groups when 2 chains exist. Nodes at the same
                 position along the road now get matching fractions on both offset lines.
2026.07.27.07 - Fixed "Make it parallel" collapse with many segments: make each chain internally
                 consistent before cross-side detection. Mixed-side segments within a chain
                 now get forced to the chain's own majority side, preventing cross-side nodes
                 from triggering a global collapse to one side.
2026.07.27.06 - Fixed "Make it parallel" chain-side swapping: when 2 chains detect on the same
                 side, the chain FURTHER from the guide line stays on its detected side; the
                 CLOSER chain flips. This preserves the physically outermost chain's natural side.
2026.07.27.05 - Fixed "Make it parallel" overlap on same-side independent chains: detect
                 independent chains (segments not sharing nodes). When exactly 2 chains
                 exist, assign opposite sides so they spread outward as a parallel pair.
2026.07.27.04 - Fixed "Make it parallel" majority-side causing overlap on independent chains:
                 only force to majority side when cross-side shared nodes exist. Independent
                 chains on opposite sides (no shared nodes) keep their original sides.
2026.07.27.03 - Fixed "Make it parallel" cross-side distortion: force all selected segments
                 to the same side of the guide line (majority vote) when cross-side nodes
                 exist, preventing V-shaped kinks at shared nodes.
2026.07.27.02 - Fixed "Make it parallel" shape fidelity: restructured to compute segment
                 geometries first (offset-line slicing), then derive node positions from
                 slice endpoints. Follows guide line curvature without kinking.
2026.07.27.01 - Fixed "Make it parallel" kinking on curves: replaced chain-based offset-line slicing
                 with per-vertex projection (RA Util pattern).
2026.07.26.02 - Added "Make it parallel" feature: select two or more one-way segments, click the button, draw a guide line via sdk.Map.drawLine(), and the segments become parallel to the guide line at the specified distance apart. Includes automatic side detection (left/right of guide line), endpoint node movement, and full undo support. Reuses the existing distance dropdown. Cancelling the drawing (Escape) is silently ignored.
                 Fixed sdk.Editing.doActions not a function error: removed wme-sdk-plus dependency. Each SDK mutation call (updateSegment, moveNode, allowNodeTurns) creates its own undo action — matching the existing split feature pattern.
2026.06.29.01 - Fixed issue with lane count and able to split segments with equal number of defined lanes on both sides. Added a check to ensure that the segment has equal or zero defined lane on each side before proceeding with the split.
2026.03.31.01 - Replaced broken segment-address country detection with sdk.Countries.getTopCountry().
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
