# Frobenius cohomology realization declarations

## Reason

The proof of common-stage functor descent needs the coefficient-enlargement equality
for the explicitly constructed realization arrows. That equality belongs in a new
statement module, which must import the realization definitions without importing
the parent functor-existence theorem. Moving the existing definitions into a
publicly re-exported prerequisite removes that cycle. This is a dependency
refactor, not a split to avoid a compile timeout.

## Old

The following existing comparison, and its thirteen prerequisite public declarations,
lived in `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`.

```lean
def frobeniusCohomologyRealizedComparison (c₀ : Compactification Y₀.hom) (compact : Bool)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (L : Index l Ω) (h : K.stage ≤ L) :
    (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact K.stage).obj K.obj ≅
      (frobeniusCohomologyRealizedStage D l hl Y₀ Ω c₀ compact L).obj (K.toStage h) :=
  eqToIso (congrArg
      (fun φ ↦ (frobeniusCohomologyCoefficientExtension φ).obj
        ((frobeniusCohomologyRationalFunctor D l hl
          (Coefficient.{u} l Ω K.stage) Y₀ c₀ compact).obj K.obj).obj)
      (frobeniusCohomologyStageEmbedding_comp l Ω K.stage L h).symm) ≪≫
    (frobeniusCoefficientTower
      (coefficientInclusion.{u} l Ω K.stage L h).toRingHom
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).symm.app _ ≪≫
    (frobeniusCohomologyCoefficientExtension
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).mapIso
      ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι.mapIso
        ((frobeniusCohomologyRationalScalar D l hl
          (Coefficient.{u} l Ω K.stage) Y₀ c₀ compact (Coefficient.{u} l Ω L)
          (coefficientInclusion.{u} l Ω K.stage L h)).app K.obj)) ≪≫
    (frobeniusCohomologyCoefficientExtension
      (frobeniusCohomologyStageEmbedding.{u, v} l Ω L)).mapIso
      ((DerivedCategory.pointFiniteDimensional (Coefficient.{u} l Ω L)).ι.mapIso
        ((frobeniusCohomologyRationalFunctor D l hl
          (Coefficient.{u} l Ω L) Y₀ c₀ compact).mapIso
            ((operationStageTransitionIso l Ω (D.geometricFiber Y₀).left
              K.stage L h).symm.app K.obj)))

```

The full moved declaration list is:

- `WeilConjectures.frobeniusCoefficientLiftHom`
- `WeilConjectures.frobeniusCoefficientModules`
- `WeilConjectures.frobeniusCoefficientModulesTower_existsUnique`
- `WeilConjectures.frobeniusCoefficientTower`
- `WeilConjectures.frobeniusCohomologyRationalFunctor`
- `WeilConjectures.frobeniusCohomologyRationalOperation`
- `WeilConjectures.frobeniusCohomologyIntegralScalar`
- `WeilConjectures.frobeniusCohomologyRationalOperationScalar_existsUnique`
- `WeilConjectures.frobeniusCohomologyRationalOperationScalar`
- `WeilConjectures.frobeniusCohomologyRationalScalar`
- `WeilConjectures.frobeniusCohomologyStageEmbedding`
- `WeilConjectures.frobeniusCohomologyStageEmbedding_comp`
- `WeilConjectures.frobeniusCohomologyRealizedStage`
- `WeilConjectures.frobeniusCohomologyRealizedComparison`

## New

The comparison above, all thirteen prerequisite declarations, their signatures,
attributes, definition bodies and proved theorem bodies are verbatim in
`Sheaf.SixFunctors.FrobeniusCohomologyRealization`. The original module publicly
imports it, so the existing public names remain available to all consumers.
Only module headers, import placement and documentation differ. No target or
mathematical definition changes meaning. The private quotient-descent proof and
the new coefficient-transport lemma use these same specified maps.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.TwistFrobeniusScalar | F2 | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Names and definition bodies unchanged; re-exported by the original module. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | U9 | Names and definition bodies unchanged; re-exported by the original module. |

The read-only `tools/downstream.py` audit also found 107 transitive consumers.
A direct name-use scan of all fourteen moved names found exactly the rows above.
Each consumer still imports the original module, directly or transitively, and
therefore sees the same names, types and definition bodies through its new public
import. No consumer adaptation is needed. No `WeilConjectures` source module is changed.

## Status

landed 20261025T203421-L-2813352 2026-10-25 (merge of deliver/U9/Sheaf.SixFunctors.FrobeniusCohomologyTransportIso)
