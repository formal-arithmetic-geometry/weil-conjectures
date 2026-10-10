# Delivery report: lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image

## Changed

Split `lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image` in the `sk-thm-p1` unit. The target node now has a five-step proof following the proof of Stacks Cohomology of Schemes Lemma `0CYQ`, part (2). I added the Mathlib leaf `lem-weil-pbc-universally-closed-base-change` for the base-change stability assertion used in the second step. This repair adds exact-tag statement nodes for Schemes `0356` (reduced-source factorization) and Morphisms `07RK` (closed-immersion cancellation), and cites them directly in steps 1 and 2. No Lean files were changed or compiled.

## Source and node review

The source is `literature/stacks-project/coherent.tex`, Lemma `0CYQ` (the cited Stacks tag is `0CYQ`). Step 1 gives reduced induced structures on `Z` and `Z' = f(Z)`, forms the scheme-theoretic inverse image `Z''`, and records the induced map. Step 2 follows the source's base-change argument: `Z'' -> Z'` is universally closed by Stacks `01W4`, `Z -> Z''` is a closed immersion by the pullback closed-immersion node, and composition (`01W3`, represented by `lem-weil-pbc-closed-immersion-integral-separated-uc`) makes `Z -> Z'` universally closed and surjective. Step 3 uses the existing `09MQ` node `lem-weil-pbc-surjective-universally-closed-separated` to descend separatedness. Step 4 checks local finite type from the closed immersion and the given locally finite type map. Step 5 applies the existing `03GN` node `lem-weil-pbc-image-universally-closed` to obtain universal closedness and properness of `Z' -> S`; the reduced induced structure identifies its underlying closed subset with `f(Z)`.

The cited dependencies exist on the current `sheaf-dag`: `lem-weil-pbc-reduced-induced-closed-subscheme`, `def-pc-fibre-product`, `lem-weil-pbc-closed-immersion-base-change`, `lem-weil-pbc-closed-immersion-integral-separated-uc`, `lem-weil-pbc-surjective-universally-closed-separated`, `lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-image-universally-closed`, `def-weil-proper-morphism`, `def-weil-finite-type-morphism`, and `def-weil-surjective-morphism`. I searched `dag/nodes` for the exact target statement and the `01W4` base-change fact before creating the new node; no duplicate node was present on this base.

The new base-change leaf records LeanSearch, Loogle, and Mathlib grep searches. The exact Mathlib match is `AlgebraicGeometry.universallyClosed_isStableUnderBaseChange` in `Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean:65`; there is no Mathlib declaration for the full closed-subset image/proper-over-base statement. The repair node for `0356` records three searches with no direct Mathlib match, while the `07RK` node records three searches matching `AlgebraicGeometry.IsClosedImmersion.of_comp` in `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:242`. The existing blueprint node with an equivalent cancellation statement was not edited or substituted because this delivery requires the exact Stacks `07RK` source citation.

## Return repair

The return identified two uncited source steps. Step 1 now cites `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`, whose statement and source are Schemes Lemma `0356`; it supplies precisely the reduced-source/set-theoretic-image criterion used to factor `Z` through the scheme-theoretic inverse image `Z''`. Step 2 now cites `lem-weil-pbc-closed-immersion-cancellation`, whose source is Morphisms Lemma `07RK` and whose Mathlib match is `IsClosedImmersion.of_comp`; it supplies the closed immersion `Z -> Z''` from the closed immersion into `X` and separatedness of `Z'' -> X`. Both nodes are statement-only or Mathlib leaves, carry their three searches, and are created for this item.

## Checks

- `python3 tools/review_split.py lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image` passed.
- `python3 tools/check_dag.py --cycles` reported zero cycles and zero self-loops; it printed only the repository's existing eight reachability warnings.
- No Lean writing or compilation was performed, per Stage 1.

## Review by F1

I rechecked the returned points against the source text and the current DAG. In step 1, the new `0356` node exactly licenses the factorization from reduced `Z` once its image lies in the closed inverse image; this avoids treating the factorization as an unstated topological fact. In step 2, the new `07RK` node is applied with composite `Z -> X` closed and projection `Z'' -> X` separated, while the existing base-change node supplies that projection's closed-immersion property. The remaining composition, descent, finite-type, and image arguments still cite their prior nodes and preserve the hypotheses and full conclusion of `0CYQ`(2). I also verified that both new nodes have item ownership, exact Stacks places, and the required searches, with no Lean files changed or compiled.
