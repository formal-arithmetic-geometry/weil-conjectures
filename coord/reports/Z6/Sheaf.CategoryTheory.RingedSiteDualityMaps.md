## What changed

Proved `CategoryTheory.ringedSiteDualityMaps_exists` using the already stated,
normalized `ringedDerived_closed_symmetric_monoidal` theorem. The coefficient
unit is K-flat by the ordinary right unitor; the supplied symmetry, right unitor
and associator give the required representative morphisms after rewriting their
K-flat tensor comparisons. Existing public signatures and imports are unchanged.

Proved `CategoryTheory.ringedSiteOrdinaryBidual_existsUnique` by an actual
sectionwise construction. Proved private helpers construct sheaf evaluation,
assemble its signed Hom-product components, check the chain-map equation using
the Hom differential and the sign identity, and establish uniqueness using the
zero terms of the coefficient unit outside degree zero. The Hom-differential API
is proved first for a general target complex with zero differential, then specialized to the coefficient unit. No new existence premise
or postponed component of the argument is introduced.

The original packet refactored `WeilConjectures.coefficientHomComponent` to
use the definitionally equal `homComplexπ` API. That refactor has independently
landed. This repair preserves the current
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation` and its definition node
verbatim, including its private native-projection compatibility lemma.

Repaired the return of head `793a42702`: the change record's `## Users` table
now includes `Sheaf.Algebra.Homology.RingedSliceEvaluationModels`, whose
`RingedSliceHomModel` uses the projection for both the original site and its
slice. Both formulas are unchanged. The table also includes the current full
downstream inventory and current direct declaration users, with current holders.
The unchanged `RingedSliceEvaluationModels` source compiled through
`lcompile.py` in 14.5 seconds. No consumer adaptation is needed. The retained record is
`coord/changes/coefficient-hom-component-projection-api.md`.

The item's DAG record describes the two retained proofs. The original plans for
its remaining theorems stay in the record. No module is withdrawn. The repaired
item compiled cleanly through `lcompile.py` in 38.8 seconds; the unchanged named
consumer compiled in 14.5 seconds. The delivery command runs the final preflight
and axiom probe.

## Proved and sorry left

Closed two of the item's six original holes:

- `CategoryTheory.ringedSiteDualityMaps_exists`.
- `CategoryTheory.ringedSiteOrdinaryBidual_existsUnique`.

Added zero holes and split off zero statements. The unchanged projection module
has zero holes. This is a partial delivery of a module with several original
holes; the four remaining declarations are unchanged:

- `CategoryTheory.ringedSiteOrdinaryEvaluation_existsUnique`.
- `CategoryTheory.ringedSiteBidual_normalization`.
- `CategoryTheory.ringedSiteDualEvaluation_normalization`.
- `CategoryTheory.ringedSiteDualityMaps_restriction`.

All six declarations realize `lem-sfb-ringed-site-duality-maps`. Model existence
uses the previously stated dependency
`lem-sf-ringed-derived-closed-symmetric-monoidal`; its own proof obligation is
retained in its existing module. Every new private helper in this delivery is
proved. The coefficient unit also has private zero-differential and zero-term
lemmas, so the component argument treats that complex through its API.

## No longer needed

Removed these old proof imports from the item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`.
- `WeilConjectures.Algebra.Homology.HomComplex`.
- `WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy`.
- `WeilConjectures.Algebra.Homology.HomComplexUnitIso`.
- `WeilConjectures.Algebra.Homology.HomTensorTotal`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`.
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`.
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`.
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`.

The completed model construction no longer directly uses these old planned
proof dependencies:

- `def-pc-flat-sheaf-modules`.
- `def-pc-kflat-complex`.
- `lem-pc-kflat-closure`.
- `lem-pur-hom-complex-global-homotopy`.
- `lem-pur-hom-kflat-into-kinjective`.
- `lem-weil-pbc-kinjective-hom-derived`.

Their role in constructing the general closed monoidal structure belongs to the
existing closed-structure theorem. This delivery does not claim that their
modules are globally unnecessary: they may still be imported by that theorem or
other consumers. Dependencies appearing in the remaining normalization and
restriction plans stay in the item's node. No adopted source declaration or
module is deleted. The unit record has no realized route that this change would
bypass.

## Where the brief, the DAG or earlier work was wrong

The first two planned construction steps duplicate an existing statement with
the needed representative normalizations. Reusing that statement is shorter.
The projection definition was mathematically correct, but its nested choice
expression was expensive to convert to the library's named projection API; the
refactor changes the spelling of the same data. No target, hypothesis,
conclusion, universe, or mathematical convention is changed or disputed.

The remaining ordinary evaluation and derived normalization arguments are not
claimed proved. In particular, the older Hom-total-tensor APIs with coefficient
universe fixed to the maximum of the two site universes do not immediately fit
this module's independent coefficient universe.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
