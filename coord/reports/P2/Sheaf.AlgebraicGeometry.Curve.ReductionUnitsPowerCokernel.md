## What changed

Reduced `AlgebraicGeometry.Scheme.nonempty_reductionUnitsPowerCokernelIso` without changing
its signature. The proof identifies the next units kernel as the kernel of restriction
from the current units kernel to units modulo the next ideal power. It constructs the
kernel universal property explicitly, then uses Mathlib's exact-sequence image theorem
and uniqueness of cokernels. It verifies both ideal-power inequalities and applies the
new general nil-ideal image linearization theorem.

Added `Sheaf.AlgebraicGeometry.Curve.NilIdealUnitsImageLinearization`, containing the
remaining affine comparison for arbitrary ideals J <= I, I squared <= J, I <= nilradical.
This statement concerns the image inside units modulo J, not the original units-filtration
cokernel. The original module proves the kernel calculation and categorical passage from
that cokernel to this image. Updated the original DAG proof and added the new node.

Added proof imports `Mathlib.CategoryTheory.Abelian.Exact` and
`Sheaf.AlgebraicGeometry.Curve.NilIdealUnitsImageLinearization`. Existing public imports
and all existing signatures stay unchanged. Both modules compile locally.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.nonempty_reductionUnitsPowerCokernelIso`
(node `lem-sc-reduction-units-power-cokernel`). No textual sorry remains in the item.

Added one hole:
`AlgebraicGeometry.Scheme.nonempty_nilIdealUnitsImageIso`
(node `lem-sc-nil-ideal-units-image-linearization`). Its whole proof is `by sorry`;
the docstring and node give the affine calculation and gluing argument. This is a
one-hole decomposition, not a sorry-free proof of the original theorem. Net holes: zero.
The categorical kernel calculation, exactness, cokernel-to-image comparison, and power
inequalities are fully proved. No definitions or arbitrary data witnesses were added.

## No longer needed

None. No imports were removed, and all three original dependency nodes remain needed.
No blueprint unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The three original dependencies construct the units kernels, their inclusion, the ideal
module quotient, and its tensor-sections sheaf; they do not state an affine linearization
lemma. Thus the original plan's linearization and gluing steps could not simply be applied
as existing declarations. The new node isolates those steps, while the categorical
cokernel argument is now Lean code.

The source blueprint file is absent from this machine's literature checkout. The source
argument is available in the original item's DAG proof and docstring, both read here.
LeanSearch returned an Internal Server Error; the recorded verdict is unavailable.
LeanFinder and grep found no matching sheaf comparison. Edge cases checked mathematically:
I=J, I=0, empty X, and j=0; no Noetherian or uniform nilpotence hypothesis was introduced.

## New nodes

`lem-sc-nil-ideal-units-image-linearization`, in
`dag/nodes/sec-curve-estimates/lem-sc-nil-ideal-units-image-linearization.json`, states the
remaining image linearization for nil ideals with square-zero quotient. Its Lean module
is `Sheaf.AlgebraicGeometry.Curve.NilIdealUnitsImageLinearization`. The categorical image
and ideal module quotient are genuine constructions. No change records are required:
no existing statement, definition, or visibility changed, and no adaptations were made.

## Second reading by P2

1. Compared the delivered reduction module with the repository version. The existing theorem
   signature is unchanged byte for byte; the added theorem is recorded as a new split node.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; there are no errors, forbidden
   declarations, or unlisted `sorry`s. The sole remaining `sorry` is the named affine
   linearization theorem and has a docstring and matching node. Verdict: pass.
3. Checked the split statement against the affine nil-ideal calculation and edge cases
   `I = J`, `I = 0`, empty `X`, and `j = 0`; it introduces no extra hypotheses beyond the
   stated quasi-coherence assumption. Searches found no existing declaration. Verdict: pass.
4. The proof follows the shortest available categorical route, then invokes the required
   affine linearization node; all original imports remain needed and no proof dependency is
   bypassed. Verdict: pass.
5. The item node and the new node agree with the Lean declarations, including proof steps,
   dependencies, origins, unit, and chapter. The unit route and realized steps are retained.
   Verdict: pass.

Changed only the two module proofs/imports, added the explicitly documented split theorem and
node, and appended this review. No existing definitions or target statements changed.
