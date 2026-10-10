1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-affine-generic-second.json` — statement, no new child nodes; Mathlib searches recorded (no match; LeanSearch unavailable).

2. Attachments:

   - None. `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_two_lowerStar` still contains `sorry`.

3. WANTED:

   - None.

4. What was wrong or incomplete:

   - The imported proof used finite-etale trace, direct-image left exactness, long exact cohomology, and the normal-integral generic-constant comparison without naming the statements supplying them. I added the existing DAG nodes to the relevant steps and declared the cross-unit nodes as tool uses. The imported step for the general torsion module also compressed the finite-submodule and invariant-union argument; it now spells that argument out and marks only that elementary reduction as elementary.

## Review by H1

I read the source declaration and docstring in `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean:333-353`; its theorem has the same hypotheses and conclusion as the item but is sorried, so it cannot be attached. I read the imported blueprint proof and the statements of every cited DAG node. Step 1 uses the discrete Galois-module equivalence and Sylow filtration, then the finite-etale trace definition and degree identity; the latter two are the existing trace statements from the proper-base-change unit and are declared tool uses. Step 2 uses the finite normalization model and exactness of finite direct image. Step 3 uses the existing direct-image left-exactness statement, the zero-generic acyclicity statement, the derived-functor long exact sequence, the normal-integral generic-constant comparison, and the affine constant second-cohomology vanishing; each cited statement supplies exactly the clause used. Step 4 explicitly constructs the directed union of finite stable submodules, checks that generic-point sections are finite products of invariants and that invariants commute elementwise with directed unions, then applies the filtered-colimit cohomology statement.

I checked the smooth affine model hypotheses needed by the normal-integral comparison (Noetherian, normal, integral), and checked the small edge cases of the finite-module reduction (zero module and a trivial one-dimensional quotient). No statement was changed, no child node was duplicated, and the item is marked `split` with its blueprint proof paragraphs recorded.

## Second reading by H1

- Item statement: checked against `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean` theorem `subsingleton_sheafH_two_lowerStar` (lines 333–353); the smooth, integral, affine, connected, algebraically closed hypotheses and torsion generic sheaf conclusion agree.
- Step 1: checked `lem-exc-field-discrete-modules`, `lem-sc-sylow-module-filtration`, `def-weil-pbc-finite-etale-trace`, and `lem-weil-pbc-finite-etale-trace-degree`; the cited statements supply the discrete-module reduction, prime-to-ell filtration, restriction/trace, and degree splitting. The zero module and degree-one extension cases behave correctly.
- Step 2: checked `lem-sc-finite-extension-affine-model` and `lemma-weil-pbc-finite-direct-image-exact`; they provide the smooth affine normalization and exact finite direct image used. The direct-summand reduction is elementary.
- Step 3: checked `lem-weil-pbc-direct-image-left-exact`, `lem-sc-zero-generic-acyclic`, `lem-weil-pbc-derived-functor-long-exact`, `lem-fin-normal-generic-constant`, and `lem-sc-affine-constant-second`; each statement supplies the corresponding filtration, generic-vanishing, long-exact, normal-integral comparison, or affine constant-sheaf input. The zero filtration and one-dimensional trivial quotient are consistent.
- Step 4: checked `lem-weil-pbc-cohomology-filtered-colimit`; the finite stable-submodule union and invariant/filtered-colimit argument is explicitly written and the reduction is elementary.
- New nodes: none; therefore B1–B7 and duplicate/Mathlib-leaf checks are vacuous. The recorded Mathlib searches were rerun and found no matching theorem (LeanSearch was unavailable).
- Changed: added this second-reading section only. No statement, proof step, citation, or dependency was altered; delivery preflight passed.
