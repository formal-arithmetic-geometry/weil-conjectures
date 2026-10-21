# IsConstructibleSheaf.of_shortExact_of_isNoetherianRing

## Reason

The residue-field closure argument needs the global fixed-scalar form of Noetherian
constructible extension closure. The original module already proves the requisite
`noetherian_flc_of_shortExact` privately, but exports only the intrinsic affine-local
module form. The adopted source global extension API assumes a finite underlying ring,
which does not apply to an arbitrary residue field. Add a proved global consequence in
the unclaimed `Sheaf` module. It intersects the two finite stratifications and uses the
existing private finite-locally-constant extension theorem on every stratum. No source
module under `WeilConjectures/` is changed; no old declaration or import is altered.
This is an additional realization of the same discrete Noetherian Serre argument and is
attached to its existing node `lem-sfb-discrete-noetherian-constructible-serre`.

## Old

There was no public declaration named
`AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_shortExact_of_isNoetherianRing`.
Every existing declaration and its body is retained verbatim.

## New

```lean
/-- Global constructible fixed-scalar module sheaves over a Noetherian ring are
closed under extensions, without a finite-underlying-ring assumption.
Source: Stacks Project, Modules on Sites, Tag 093U (3)
(blueprint: lem-sfb-discrete-noetherian-constructible-serre).
Proof: take the fibre-product common refinement of the two finite stratifications.
Exact immersion pullback gives extensions of finite locally constant sheaves on each
stratum. The finite-presentation lifting argument noetherian_flc_of_shortExact above
makes the middle sheaf locally constant, and stalkwise exactness makes its values
finitely generated. The common refinement witnesses global constructibility. -/
theorem IsConstructibleSheaf.of_shortExact_of_isNoetherianRing
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁]
    [IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃] :
    IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₂ := by
  obtain ⟨T₁, hT₁⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₁)
  obtain ⟨T₃, hT₃⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := S.X₃)
  refine ⟨T₁.inter T₃, fun k ↦ ?_⟩
  have h₁ := (T₁.inter_refines_left T₃).isFiniteLocallyConstantSheaf_upperStar S.X₁ hT₁ k
  have h₃ := (T₁.inter_refines_right T₃).isFiniteLocallyConstantSheaf_upperStar S.X₃ hT₃ k
  let F := Etale.upperStar (ModuleCat.{u + 1} Λ) ((T₁.inter T₃).immersion k)
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₁ := h₁
  have : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (S.map F).X₃ := h₃
  exact noetherian_flc_of_shortExact hS'
```

## Users

The module is unclaimed. `tools/downstream.py
Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre --uses IsConstructibleSheaf`
was run against the shared snapshot on 2026-10-21. This is an additive API extension, so
all original consumer statements are unchanged and no forced adaptations occur. The new
`Sheaf.Paper.AdicConstructibleTriangulated` is its sole new consumer, checked by compilation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.AlgebraicGeometry.NoetherianAffineFreePresentation | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.DeligneLaumon.ConstructibleExtensionFiniteStage | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.AdicStratifiedPerfect | U2 | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.CtfHomConditionB | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.CtfHomLocalizationDevissage | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.DirectedGaloisFiniteTensorGenerators | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.DirectedGaloisTensorFiltrationClosure | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.GaloisLocalizationUniformBounds | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralModels | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.Paper.PrimeFieldTensorDevissage | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Original declarations unchanged; additive proved API only |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Original declarations unchanged; additive proved API only |

| Sheaf.Paper.AdicConstructibleTriangulated | U2 (new) | Uses new global extension consequence |

## Status

landed 20261021T144006-L-34028 2026-10-21 (merge of deliver/U2/Sheaf.Paper.AdicStratifiedPerfect)
