# WeilConjectures.SixFunctors.integralReductionHasEtaleOrigin

## Reason

Reduce elaboration of the specified reduction predicate without changing its meaning.
Profiling in one process measured 15.9 seconds for the original definition and 6.0 seconds
for the new definition. The new body elaborates derived scalar extension while both ring
objects are abstract, and shares the input complex, quotient ring, and reduced complex.
It adds only local let bindings and a local generic function; it introduces no chosen data,
new public declaration, hypothesis, or mathematical assertion.

A separate diagnostic compiled the original and optimized definitions together and proved
that their values are equal by `rfl`, for all original parameters. The whole diagnostic
compiled in 35.0 seconds. Thus the change is beta/delta/zeta equality, including the
specified scalar maps, derived functors, exponent n-1, and fixed-scalar realization.
The declaration signature and attributes stay identical. No Challenge.lean target changes;
none of its target signatures uses this predicate. Its use in the conclusion of
integral_models_generators and the integral-models unit retains the identical proposition.

## Old

```lean
noncomputable def integralReductionHasEtaleOrigin (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    {S V : Scheme.{u}} (u : S ⟶ V) (i : V ⟶ X)
    [IsOpenImmersion u] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (integralCoefficientObject S ℓ E)) : Prop :=
  constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
    ((DerivedCategory.singleFunctor _ 0).obj
      (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀)) ∧
  ∀ n : ℕ, 1 ≤ n →
    Nonempty
      (((Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (integralLowerShriek X
            (Profinite.continuousMapRingObj (completedResidue ℓ E π (n - 1))) u i
            ((Mod.extendScalars (integralModelReductionMap S ℓ E π n).hom).obj L₀))) ∧
    constantModelBoundedConstructible
      (Profinite.continuousMapRingObj (completedResidue ℓ E π (n - 1))) X
      ((Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))) ∧
    ∃ (_ : Finite (completedResidue ℓ E π (n - 1)))
      (_ : DiscreteTopology (completedResidue ℓ E π (n - 1))),
      (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} (ULift.{u, 0} (completedResidue ℓ E π (n - 1)))) X) ⋙
        finiteCoefficientIntrinsicDerivedComparison X
          (ULift.{u, 0} (completedResidue ℓ E π (n - 1)))).essImage
        ((integralModelIntrinsicRealization X
          (completedResidue ℓ E π (n - 1))).rightDerivedFunctor.obj
          ((Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀))))
```

## New

```lean
noncomputable def integralReductionHasEtaleOrigin (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    {S V : Scheme.{u}} (u : S ⟶ V) (i : V ⟶ X)
    [IsOpenImmersion u] [IsClosedImmersion i]
    (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (integralCoefficientObject S ℓ E)) : Prop :=
  let derivedScalar {R A : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
      [MonObj R] [IsCommMonObj R] [MonObj A] [IsCommMonObj A]
      (φ : R ⟶ A) [IsMonHom φ] :
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) A) :=
    (Mod.extendScalars φ).leftDerivedFunctor
  let K := (DerivedCategory.singleFunctor _ 0).obj
    (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) u i L₀)
  constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ∧
  ∀ n : ℕ, 1 ≤ n →
    let A := completedResidue ℓ E π (n - 1)
    let Kbar := (derivedScalar (integralModelReductionMap X ℓ E π n).hom).obj K
    Nonempty (Kbar ≅ (DerivedCategory.singleFunctor _ 0).obj
      (integralLowerShriek X (Profinite.continuousMapRingObj A) u i
        ((Mod.extendScalars (integralModelReductionMap S ℓ E π n).hom).obj L₀))) ∧
    constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X Kbar ∧
    ∃ (_ : Finite A) (_ : DiscreteTopology A),
      (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} (ULift.{u, 0} A)) X) ⋙
        finiteCoefficientIntrinsicDerivedComparison X (ULift.{u, 0} A)).essImage
        ((integralModelIntrinsicRealization X A).rightDerivedFunctor.obj Kbar)

```

The new definition is elaborated under the two scoped backward.isDefEq.respectTransparency
options, both false, as in the separate compiled equality check. These affect elaboration,
not the resulting mathematical definition.

## Users

`tools/downstream.py Sheaf.SixFunctors.IntegralModelsGenerators --uses
integralReductionHasEtaleOrigin` reports 64 downstream modules in the final shared snapshot.
The only external textual use is the unchanged conclusion in `Sheaf.Paper.IntegralModels`.
The compiled universal `rfl` check preserves its proposition and all indirect consumers.
No module needs adaptation. No Challenge target changes. Each row below is checked
by substituting the definitionally identical value; its statement and proof stay unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Equal implementation; unchanged signatures. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Definitionally identical; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Definitionally identical; no adaptation. |

## Status

landed 20261022T025343-L-1291361 2026-10-22 (merge of deliver/W4/Sheaf.SixFunctors.IntegralModelsGenerators)
