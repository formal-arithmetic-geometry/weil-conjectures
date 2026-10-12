## What changed

Proved `AlgebraicGeometry.Scheme.affineEtale_model_arrows` with its signature unchanged.
The proof identifies the given arrows with scheme arrows on canonical limit pullbacks,
descends this finite family to a common stage, and constructs the canonical affine étale
stage objects and their comparison isomorphisms. Added two proved helper modules:
`FinitePullbackHomDescent` and `AffineEtalePullbackArrowComparison`. The former applies
the existing proved single-arrow spreading-out theorem and chooses a common upper bound;
the latter constructs arrows by pullback.lift and proves their comparison using naturality
and the pullback universal property. Updated the item's DAG proof to this route.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Scheme.affineEtale_model_arrows`.
Also proved `AlgebraicGeometry.Scheme.finite_pullback_hom_descent` and
`AlgebraicGeometry.Scheme.affineEtale_pullback_arrow_comparison`. No holes added or left
in any delivered module; this is a proof, not a decomposition with new holes.
All three modules compile. The empty finite family is covered by the finite upper-bound
lemma and vacuous arrow equations; the comparison proof also covers identity base change.

## No longer needed

Removed the direct proof import `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
from the item; it is now needed in the proved finite-descent helper. Removed the direct
proof import `Sheaf.AlgebraicGeometry.AffineEtaleSiteBaseChange`; its canonical base-change
construction remains used through the comparison helper, so its node is not pruned.
No planned dependency node or module is mathematically pruned: spreading-out, pullbacks,
and affine étale base change all remain needed. The earlier sandbox's unused copied
`AffineEtaleFiniteDiagramObjects.lean` was removed from the delivery.

## Where the brief, the DAG or earlier work was wrong

The previous early ABANDON overlooked a usable factorization of the planned argument.
The existing single-arrow theorem is sufficient after finite directed upper bounds;
the remaining compatibility follows from pullback uniqueness and q naturality.
An exploratory comparison statement that assumed only object pullback squares was too
strong: arbitrary fi need not descend the specified g. It was discarded. The delivered
comparison theorem explicitly assumes the scheme-arrow descent equation and proves the
categorical comparison from it. No existing signature, definition, or visibility changed.
The spreading-out node is used as an existing generic tool; no unit step is bypassed.

## New nodes

`lem-pbc-finite-pullback-hom-descent` records the proved finite wrapper around
`thm-pd-spreading-out`, with canonical pullback domains and explicit descent equations.

`lem-pbc-affine-etale-pullback-arrow-comparison` records the proved fixed-stage
comparison construction. It has no limit or directedness assumption and makes no descent
existence assertion: the required scheme arrows and descent equations are inputs.

## Second reading by S2

1. **Statements and accidental changes.** Compared the delivered item with the repository
version. The target theorem signature is byte-for-byte unchanged; the two helper modules are
new declarations with their stated interfaces, and no existing declaration was weakened.
Verdict: pass.
2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`; there are no
`sorry`, `axiom`, `unsafe`, `opaque`, or related escapes. The proofs use only the permitted
category and pullback constructions; no extra assumptions were introduced. Verdict: pass.
3. **Split statements.** Checked both helper theorems against their node statements and tested
the finite-family edge case (including `n = 0`) in the construction. They are strictly simpler
than the target and are needed by its proof; neither duplicates an existing library result.
Verdict: pass.
4. **Pruning and route.** The target proof uses finite simultaneous descent followed by the
fixed-stage pullback comparison, preserving the unit route. The direct transition-limit import
was moved to the finite-descent helper, and the direct base-change import to the comparison
helper; no unused planned dependency was removed. Verdict: pass.
5. **DAG agreement.** The target and both new nodes record the declarations, proof steps,
dependencies, source, and module paths exactly as delivered. The unit `sk-thm-p1` route remains
realized through the target. Verdict: pass.

Changed after this reading: added this review record only; no Lean source or DAG content needed
repair.
