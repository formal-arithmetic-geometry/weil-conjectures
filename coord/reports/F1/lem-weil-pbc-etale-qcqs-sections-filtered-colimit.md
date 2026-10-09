# Stage 1 report: `lem-weil-pbc-etale-qcqs-sections-filtered-colimit`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-qcqs-sections-filtered-colimit.json`: repaired the returned item in TeX, added exact Tags 0738 and 03Q4, and split the proof into the refinement, injectivity, and surjectivity steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-qcqs-cofinal-finite-coverings.json`: new public unsplit refinement node.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-site-sheafification-sections-local.json`: new public unsplit Sites 00WB/00WK sheafification-locality node.
- `coord/reports/F1/lem-weil-pbc-etale-qcqs-sections-filtered-colimit.md`: this report.

## Attachments

None. No Lean was written or compiled.

## Corrections

The previous delivery used ASCII mathematical notation, omitted the exact Tags in the item and refinement statement, and relied on an unstated local description of sheafification. The new nodes and all item proof steps use TeX notation. The new local node states the 00WB/00WK representation, compatibility, and local-equality facts, with four Mathlib searches and no exact Mathlib match. Steps 2 and 3 explicitly apply the finite affine etale refinement node at the witness covers and use quasi-compact pairwise fibre products on overlaps.

## Sources and cited nodes

The route follows Sites, Lemma Tag 0738, parts (2) and (4), and Etale Cohomology, Section 59.51, Tag 03Q4. The refinement node records the affine-etale refinement (Topologies Tag 0218), the qcqs finite-cover construction, and the exact 0738/03Q4 application. The parent proof cites the public refinement node; the public sheafification node for Sites Tags 00WB and 00WK; `lem-weil-pbc-filtered-colimit-sets-elementwise` for eventual equality in a filtered set colimit; and `lem-weil-pbc-pretopology-sheaf-condition` for equalizer gluing. The cross-unit `lem-weil-pbc-module-sheaves-colimits-forgetful` result is used only as a generic tool and is recorded in `tool_uses`.

## Validation

- `python3 tools/review_split.py lem-weil-pbc-etale-qcqs-sections-filtered-colimit` passes with two new nodes and the recorded tool use.
- Both new nodes and the item pass `python3 -m json.tool`.
- `git diff --check` succeeds.
- `python3 tools/check_dag.py --cycles` is run before delivery; any reachability warnings are pre-existing and unrelated.

## Review by F1

I checked the revised statement against Sites Tag 0738(4) and the etale application in Etale Cohomology Section 59.51, Tag 03Q4. The statement still says exactly that evaluation at a quasi-compact quasi-separated etale object preserves the filtered colimit, while the source tags are now present in the statement and source fields.

The refinement node is self-contained: it introduces the covering family, finite affine refinement, factorization through the original cover, and quasi-compact pairwise fibre products. Its search record covers LeanSearch, LeanFinder, Loogle, and source grep, and correctly records no exact Mathlib theorem. The sheafification node is also self-contained and records the local representatives and local equality needed by the parent; its 00WB/00WK source and four search records are explicit.

The parent proof uses the refinement node in Step 1 and again where Steps 2 and 3 refine the sheafification witness covers. Step 2 uses local equality after sheafification, eventual equality in the filtered sectionwise colimit, and the sheaf equalizer condition to prove injectivity. Step 3 uses local representatives, applies injectivity on quasi-compact overlaps, dominates the finite set of indices, and glues. The module conclusion is justified by the explicitly recorded generic tool use. No unit route or target statement was changed, and all new nodes remain public and unsplit.
