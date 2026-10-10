# Stage 1 report: lem-pc-perfect-generation-affine-base

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-affine-base.json`: item, statement split; no Mathlib leaf.
- `citations.json`: verbatim citations for both proof steps.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` carries the item, and no `(blueprint: lem-pc-perfect-generation-affine-base)` declaration was found.

## WANTED

None.

## Review by K1

I read the item source in `literature/stacks-project/perfect.tex`, Tag 09IS (affine case), and the affine comparison source Tag 06Z0. I also read the full statement of the existing node `lem-pc-affine-qcoh-derived-equivalence`; it states an equivalence `D(A) -> D_QCoh(O_Y)` with quasi-inverse `RΓ` and explicitly sends `A[k]` to `O_Y[k]`. Step 1 uses exactly those clauses, with `Y = Spec(A)`, so the affine and quasi-coherent hypotheses match the item.

The affine calculation in Step 2 is written directly: the degree-zero free rank-one complex is strictly perfect, and maps from its shifts identify with the corresponding cohomology groups, so vanishing for all shifts is equivalent to acyclicity. I checked the small cases `A = 0`, where both sides are the zero category, and `A = Z`, where this is the usual cohomology detection criterion. I initially tested a separate module child, but the delivery duplicate guard correctly identified it as a Tag 09IS clause/specialization of this item; it was removed and the calculation folded into the proof step.

Step 2 cites `def-pc-perfect-complex` for the strictly perfect finite-free description of `O_X` and the affine-equivalence node for transport; the module Hom/cohomology calculation is spelled out in the step itself. I corrected the imported empty proof, filled the item blueprint and split report, and supplied verbatim citation quotes.

## Second reading by K1

- Item statement: checked against Stacks `perfect.tex`, Tag 09IS theorem `theorem-bondal-van-den-Bergh`, affine sentence and its two equivalent clauses; the affine hypotheses, object `O_X`, and all-integer Hom test agree.
- Step 1: checked against Tag 06Z0 and the full statement of `lem-pc-affine-qcoh-derived-equivalence`; the cited equivalence and `A[n]` to `O_X[n]` identification supply exactly the transport used.
- Step 2: checked against Tag 06Z0's affine comparison and Tag 09IS's affine case; the free rank-one module is strictly perfect under `def-pc-perfect-complex`, and the shift-Hom/cohomology calculation gives the stated zero criterion.
- New nodes: none; the proposed module child was correctly removed as an elementary Tag 09IS specialization, so B1-B7 introduce no additional node to audit.
- Small cases: `A = 0` gives the zero affine category and vacuous equivalence; `A = Z` gives the ordinary derived cohomology detection criterion; the empty scheme is covered by the zero case, and shifts include `n = 0` and `n = 1`.
- Changed: no mathematical content; this second-reading section records the source, dependency, elementary-calculation, and edge-case checks.
