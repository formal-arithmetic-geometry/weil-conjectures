## What changed

Prove `AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_properties`
in `Sheaf.Paper.NormalizedTateTensorTowerProperties`, with its statement unchanged.
The finite Tate twist is a finite-lisse sheaf placed in degree -2d. Exact coefficient
realization and the level isomorphisms give the same cohomological bounds and finite
local constancy for the given normalized tower. Apply the existing generic theorem
`lisseNormalizedTower_local_models` on the identity stratum, invert its local
identifications, and assemble `UniformAdicTowerData`. Both constructibility clauses
follow on the trivial stratification. No definition or public interface is changed.

Private proved helpers transport finite local constancy between finite coefficient
presentations using the existing underlying-sheaf comparisons and finite refinement
lemma. The pullback/restriction comparison is used in the reverse direction from
`local_finite` in `PbcUniformLocalModelCohomology`.

The generic local-model theorem is a tool from the proper-base-change unit. Its
statement supplies exactly the local complexes needed here; no smooth-purity unit
statement or realized step is bypassed. The coefficient Serre and intrinsic
constructibility modules supply proved comparison helpers; finite-model local
constancy and finite-model stalks give fixed-coefficient constructibility directly.

Validation: `lcompile.py` compiled the complete proof in 37.5 seconds. The final
revision explicitly references the retained unused hypotheses to remove the linter
warnings. `deliver3.py` runs the final compile and mechanical preflight.

## Proved and sorry left

Close the one original hole in
`AlgebraicGeometry.Scheme.PurityIntegralTower.normalizedTateTensorTower_properties`
(node `lem-pur-normalized-tate-tensor-models`). No holes are added or split off.
There are zero `sorry` statements in the delivered module. This proof uses existing
library declarations and does not claim to close any holes in their dependency
closure.

## No longer needed

No original public import is removed. Exploratory proof imports of
`PbcUniformLocalModelCohomology`, `ConstructibleCoefficientSiteSquare`, and
`ConstructibleSheaf.Monoidal` are removed: direct finite-lisse constructibility
and the more precise `OpenClosed` import suffice. The direct primitive-root integral tensor
construction in the old proof plan is replaced by the generic finite-lisse
normalized-tower local-model theorem. The following old proof dependencies are not
used as separate steps: `lem-pur-twist-sheaf-locally-free`,
`det-def-sp-tate-twist-locally-free`, `def-weil-pbc-adic-lisse-module`,
`def-pur-sheaf-tensor-product`, `def-pc-kflat-complex`,
`lem-pur-site-restriction-module-adjunction-exact`, and
`lem-pur-derived-change-of-rings`. This is pruning of this node's direct plan,
not a claim that their modules are unused by the entire library. The corresponding
modules are `Sheaf.Paper.PurTwistSheafLocallyFree`, `Sheaf.Paper.TateTwistLocallyFree`,
`Sheaf.Paper.AdicLisseModule`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`, and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`. No module is
withdrawn, and no adopted source-library declaration is removed.

The proof does not need the stronger retained hypotheses `h`, `hp`, or `hsquare`:
normalization is already part of `AdicTower`, and the generic theorem supplies the
compatible local models from uniform bounds and finite lissity.

## Where the brief, the DAG or earlier work was wrong

The old plan did not identify the existing generic theorem
`lisseNormalizedTower_local_models`. It avoids a new direct computation of derived
quotients of integral root tensor lines. The DAG proof, proof dependencies, and
proof origin now describe the route used by the Lean proof. No statement is disputed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
