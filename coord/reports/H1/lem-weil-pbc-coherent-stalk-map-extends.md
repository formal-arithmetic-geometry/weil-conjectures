# Stage 1 delivery: `lem-weil-pbc-coherent-stalk-map-extends`

## Worker report

- Edited `dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-stalk-map-extends.json`: three proof steps and blueprint `same_as: []`.
- Created `dag/nodes/sec-proper-base-change/lem-weil-pbc-stalk-internal-hom-finite-presentation.json`: statement, unsplit; Mathlib search verdict: no match.
- No Lean attachment and no WANTED source.

The item matches Cohomology of Schemes 01Y4 (`lemma-map-stalks-local-map`, `coherent.tex` lines 2392-2407). Its proof cites 01XZ (`lemma-coherent-Noetherian`, lines 2225 onward) and Modules 01CP (`lemma-stalk-internal-hom`, `modules.tex` lines 3619-3678). Step 1 spells out why the coherent source is locally finitely presented, using the existing coherent definition and finite-presentation notion. Step 2 applies the new 01CP node to represent the given stalk map by a germ of sheaf Hom, hence by a map on a neighbourhood. Step 3 checks the induced stalk map is exactly the given map. The target F need not be finitely presented for 01CP, and the child accordingly requires finite presentation only of the source.

The child states exactly the finite-presentation isomorphism clause of 01CP for a ringed space and arbitrary target module. Its source proof uses a local finite free presentation and the exact Hom kernel sequence; those details remain its unsplit item. Search of DAG nodes for internal-Hom stalks and search of the whole blueprint for `01CP`, `01Y4`, `stalk hom coherent`, and `finitely presented stalk internal hom` found no existing node stating it. The existing sheaf-Hom kernel node supplies one ingredient but not the isomorphism. The Mathlib searches record LeanSearch, LeanFinder, and source grep with no exact result.

`python3 tools/review_split.py lem-weil-pbc-coherent-stalk-map-extends` passes with one new node. `python3 tools/check_dag.py` reports zero cycles and seven unrelated reachability warnings. Both JSON files parse. No build, commit, or push was run.

## Review by H1

I audited `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for an exact 01Y4 or 01CP declaration and found none, so the split is required. I read Cohomology 01Y4 and Modules 01CP in the sibling Stacks checkout. Step 1 uses the existing coherent finite-presentation node; step 2 uses the new internal-Hom stalk isomorphism with finite presentation only on the source; step 3 is the germ-to-neighbourhood representative argument. The new node is self-contained, unsplit, has three Mathlib searches and no exact match, and its blueprint ancestor and `same_as=[]` are recorded. I checked that the target need not be finitely presented. No changes were requested.
