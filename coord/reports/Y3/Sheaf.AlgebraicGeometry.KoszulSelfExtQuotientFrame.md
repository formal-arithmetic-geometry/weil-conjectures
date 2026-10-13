## What changed

Closed `AlgebraicGeometry.koszul_self_ext_quotient_frame` with its statement unchanged. The proof takes the quotient-coefficient isomorphism from `koszulExtCoefficient_affine_model`, composes it with a new fully proved quotient homology frame, then transports through `Scheme.Modules.overEquiv` using `overFunctorEquiv` and `preimageIso`.

Added `Sheaf.AlgebraicGeometry.KoszulQuotientHomologyFrame`, proving `AlgebraicGeometry.koszul_quotient_homology_frame`. The proof explicitly shows quotient-valued differentials vanish, identifies homology with the Hom term, evaluates on the exterior basis, identifies finite functions with the module coproduct, and transports the coproduct through tilde and affine restriction. Its private contraction and zero-differential proofs are adapted from `KoszulCoefficientTopHomology`; the proved private quotient presentation is adapted from `AffineKoszulFiniteFreeResolution`. No other existing module is changed.

Updated the target node's proof route and added the node for the new proved theorem. Every existing public import, declaration signature, universe and docstring of the target module is preserved. Both delivered modules compile without warnings.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.koszul_self_ext_quotient_frame` (`lem-u1-koszul-self-ext-quotient-frame`). No holes added or split off, and no `sorry` remains in either delivered module.

The new `AlgebraicGeometry.koszul_quotient_homology_frame` (`lem-y3-koszul-quotient-homology-frame`) has only `propext`, `Classical.choice`, and `Quot.sound` in its axiom check. The target still has transitive `sorryAx` from existing library comparison dependencies, as allowed in stage 3; this delivery does not assert that its entire import closure is proved. In particular the existing underived `AlgebraicGeometry.affine_koszul_coefficient_hom_coordinates`, used by the affine coefficient model, remains unfinished and is not changed here.

Edge cases do not need new assumptions: the empty exterior basis for n>m, singleton empty wedge for n=0, m=0, zero quotient rings and empty charts are covered by the same basis, finite-functions and coproduct constructions. The new theorem requires no regularity or derived category.

## No longer needed

Removed direct proof-only imports `Sheaf.RingTheory.KoszulProjectiveResolution`, `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`, `Sheaf.Paper.DerivedInternalHomRestrictOpen`, `Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel`, and `Mathlib.LinearAlgebra.ExteriorPower.Basis` from the target module. Added only the two proof imports actually used: the existing affine coefficient model and the new quotient homology frame.

The old target proof dependency edges to `new-j3-koszul-projective-resolution`, `lem-sc-affine-quotient-resolution-sheafification`, `lem-sc-derived-internal-hom-restrict-open`, and `lem-sc-derived-hom-finite-free-model` are replaced by `new-k1-koszul-ext-coefficient-affine-model` and `lem-y3-koszul-quotient-homology-frame`. The old ingredients are still needed transitively by the existing affine comparison, so no globally unreachable module is claimed pruned. The exterior basis remains used in the new module. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction. The DAG's unbundled resolution and finite-free comparison steps can be reused through the stronger existing affine coefficient model, avoiding a second derived comparison implementation. Blueprint search for Koszul and Ext returned two unrelated imported nodes, neither stating the new quotient homology frame; the nearest blueprint ancestor is retained from the target's own blueprint record.

## New nodes

`lem-y3-koszul-quotient-homology-frame`, in `dag/nodes/sec-picard-framework/lem-y3-koszul-quotient-homology-frame.json`, records the completely proved underived quotient-valued homology frame. It is strictly below the target: it has no Koszul regularity, derived category, or self Ext assertion. Its source is Stacks Project Tag 0BQY, the zero-differential Hom calculation. No change record is required because no existing interface is changed.

## Second reading by Y3

1. Compared both delivered modules with the repository versions. The target theorem signature and all existing declarations are byte for byte unchanged; the new homology theorem is a new declaration. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`. There are no errors, warnings, `sorry`, axioms, unsafe declarations, or hollow definitions in the delivered files. The proof uses only ordinary constructions and the permitted categorical axioms. Verdict: pass.
3. Checked the new theorem against the stated quotient-valued zero-differential calculation and its edge cases (empty basis, degree zero, zero quotient, and `n > m`). The statement is true and strictly below the target; no duplicate library declaration was found. Verdict: pass.
4. The proof follows the shortest available route through the existing affine coefficient model and the new explicit quotient homology frame. The removed direct imports are not needed by the target proof, and the unit route remains represented by the target and its quotient frame. Verdict: pass.
5. The target node now records the two proof dependencies actually used, and the new node records the homology theorem, its source, proof steps, and searches. Verdict: pass.

Changed only the target proof, its proof imports and DAG proof route, and added the proved quotient homology module and node. No statement or definition was changed; no holes were added.
