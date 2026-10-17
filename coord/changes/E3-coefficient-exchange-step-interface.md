# finiteDiscreteExchangeSteps: equal cached specified factors

## Reason

The complete coefficient comparison proof times out when checking casts against the
exposed concrete restricted step implementations. Keep a cached alias of each step
in the existing Sheaf interface module, together with its defining equation and an
explicit proved equality to the original step. These aliases contain real data: each
body is exactly an application of the original construction, with no witness choice.
`finiteDiscreteExchangeSteps` uses the equal cached factors. Its original total
internal exchange and total etale exchange morphisms remain exactly the same.

No adopted-source file is changed. No compiler timer or heartbeat budget is changed.
Every existing public signature and every Challenge declaration stays identical.
The predicate's implementation is changed; the independent reader should review its
meaning together with the three `_eq_original` certificates. They identify all three
specified factors exactly, preserving every hypothesis and conclusion.
The interface module is unclaimed in the shared snapshot; E3 holds the item.

## Old

```lean
def finiteDiscreteExchangeSteps (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B X ⥤ DerivedCategory (FiniteDiscreteInternalModules B X))
    (F1 : FiniteDiscreteEtalePlus B Y' ⥤ DerivedCategory (FiniteDiscreteInternalModules B Y')) :
    Prop :=
  ∀ (L : FiniteDiscreteEtalePlus B X)
        (hL : ProEtale.boundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) (F0.obj L)),
      let N : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) := ⟨F0.obj L, hL⟩
      Nonempty (FiniteDiscreteFactoredComparison
        (((boundedConstructibleBaseChangeUnitStep (Profinite.continuousMapRingObj B) ℓ (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))).app N).hom)
        (((boundedConstructibleBaseChangeSquareStep (Profinite.continuousMapRingObj B) ℓ (sq.asOver (Spec (.of k)))).hom.app N).hom)
        (((boundedConstructibleBaseChangeCounitStep (Profinite.continuousMapRingObj B) ℓ (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k))) (g'.asOver (Spec (.of k)))).app N).hom)
        (F1.map ((Etale.baseChangeUnitStep
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g f').app L))
        (F1.map ((Etale.baseChangeSquareStep
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app L))
        (F1.map ((Etale.baseChangeCounitStep
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) f f' g').app L))
        (((boundedConstructibleBaseChange (Profinite.continuousMapRingObj B) ℓ (sq.asOver (Spec (.of k)))).app N).hom)
        (F1.map ((Etale.baseChange
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L)))
```

The item's three private component statements use
`boundedConstructibleBaseChangeUnitStep`,
`boundedConstructibleBaseChangeSquareStep`, and
`boundedConstructibleBaseChangeCounitStep` as their left-hand factors.

The old private component signatures are:

```lean
private lemma unit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeUnitStep Λ ℓ
      (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))
      (f'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedAdjunction Λ f').unit.app
        ((coefficientDerivedUpperStar Λ g).obj
          ((coefficientDerivedLowerStar Λ f).obj K.obj))

private lemma square_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeSquareStep Λ ℓ (sq.asOver (Spec (.of k)))).hom.app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientAmbientSquare Λ sq).hom.app
          ((coefficientDerivedLowerStar Λ f).obj K.obj))

private lemma counit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((boundedConstructibleBaseChangeCounitStep Λ ℓ
      (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))
      (g'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientDerivedUpperStar Λ g').map
          ((coefficientDerivedAdjunction Λ f).counit.app K.obj))
```

## New

```lean
def finiteDiscreteExchangeSteps (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B X ⥤ DerivedCategory (FiniteDiscreteInternalModules B X))
    (F1 : FiniteDiscreteEtalePlus B Y' ⥤ DerivedCategory (FiniteDiscreteInternalModules B Y')) :
    Prop :=
  ∀ (L : FiniteDiscreteEtalePlus B X)
        (hL : ProEtale.boundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) (F0.obj L)),
      let N : ProEtale.BoundedConstructible
          (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) := ⟨F0.obj L, hL⟩
      Nonempty (FiniteDiscreteFactoredComparison
        (((coefficientExchangeUnitStep (Profinite.continuousMapRingObj B) ℓ
          (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))
          (f'.asOver (Spec (.of k)))).app N).hom)
        (((coefficientExchangeSquareStep (Profinite.continuousMapRingObj B) ℓ
          (sq.asOver (Spec (.of k)))).hom.app N).hom)
        (((coefficientExchangeCounitStep (Profinite.continuousMapRingObj B) ℓ
          (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))
          (g'.asOver (Spec (.of k)))).app N).hom)
        (F1.map ((Etale.baseChangeUnitStep
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) f g f').app L))
        (F1.map ((Etale.baseChangeSquareStep
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app L))
        (F1.map ((Etale.baseChangeCounitStep
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) f f' g').app L))
        (((boundedConstructibleBaseChange (Profinite.continuousMapRingObj B) ℓ
          (sq.asOver (Spec (.of k)))).app N).hom)
        (F1.map ((Etale.baseChange
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L)))
```

The three private component statements use the corresponding equal
`coefficientExchangeUnitStep`, `coefficientExchangeSquareStep`, and
`coefficientExchangeCounitStep`. All other binders and both sides' ambient component
formulas stay identical; their proofs use the cache defining equations.
The new scoped API, before the existing coefficient declarations, is:

```lean
section ExchangeStepCache

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

/-- The *unit insertion* step of the base-change morphism on bounded constructible complexes:
the natural transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the
unit of the adjunction `Lf'^* ⊣ Rf'_*`. -/
@[no_expose]
noncomputable def coefficientExchangeUnitStep :
    boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g ⟶
      (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStar Λ ℓ f') :=
  boundedConstructibleBaseChangeUnitStep Λ ℓ f g f'

/-- Equation for the specified unit insertion, keeping its implementation folded in importers. -/
theorem coefficientExchangeUnitStep_def :
    coefficientExchangeUnitStep Λ ℓ f g f' =
      (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft
        (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f').unit := by
  unfold coefficientExchangeUnitStep boundedConstructibleBaseChangeUnitStep
  rfl

variable {f g f' g'} in
/-- The *square transport* step of the base-change morphism on bounded constructible
complexes: `Functor.squareTransport` applied to the pullback comparison `θ_sq`, under `Rf_*` on
the left and `Rf'_*` on the right. -/
@[no_expose]
noncomputable def coefficientExchangeSquareStep (sq : CommSq g' f' f g) :
    (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ g) ⋙
        (boundedConstructibleUpperStar Λ ℓ f' ⋙ boundedConstructibleLowerStar Λ ℓ f') ≅
      (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f') :=
  boundedConstructibleBaseChangeSquareStep Λ ℓ sq

variable {f g f' g'} in
/-- Equation for the specified square transport, without exposing its concrete components. -/
theorem coefficientExchangeSquareStep_def (sq : CommSq g' f' f g) :
    coefficientExchangeSquareStep Λ ℓ sq =
      Functor.squareTransport (boundedConstructibleLowerStar Λ ℓ f)
        (boundedConstructibleLowerStar Λ ℓ f')
        (boundedConstructiblePullbackSquareComparison Λ ℓ sq) := by
  unfold coefficientExchangeSquareStep boundedConstructibleBaseChangeSquareStep
  rfl

/-- The *counit contraction* step of the base-change morphism on bounded constructible
complexes: the natural transformation obtained by contracting the counit of the adjunction
`Lf^* ⊣ Rf_*`. -/
@[no_expose]
noncomputable def coefficientExchangeCounitStep :
    (boundedConstructibleLowerStar Λ ℓ f ⋙ boundedConstructibleUpperStar Λ ℓ f) ⋙
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f') ⟶
      boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f' :=
  boundedConstructibleBaseChangeCounitStep Λ ℓ f f' g'

/-- Equation for the specified counit contraction, keeping derived constructions folded. -/
theorem coefficientExchangeCounitStep_def :
    coefficientExchangeCounitStep Λ ℓ f f' g' =
      Functor.whiskerRight (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ f).counit
        (boundedConstructibleUpperStar Λ ℓ g' ⋙ boundedConstructibleLowerStar Λ ℓ f') ≫
        (Functor.leftUnitor _).hom := by
  unfold coefficientExchangeCounitStep boundedConstructibleBaseChangeCounitStep
  rfl

/-- The cached insertion is exactly the existing specified insertion. -/
theorem coefficientExchangeUnitStep_eq_original :
    coefficientExchangeUnitStep Λ ℓ f g f' =
      boundedConstructibleBaseChangeUnitStep Λ ℓ f g f' := by
  unfold coefficientExchangeUnitStep
  rfl

variable {f g f' g'} in
/-- The cached square is exactly the existing specified square. -/
theorem coefficientExchangeSquareStep_eq_original (sq : CommSq g' f' f g) :
    coefficientExchangeSquareStep Λ ℓ sq =
      boundedConstructibleBaseChangeSquareStep Λ ℓ sq := by
  unfold coefficientExchangeSquareStep
  rfl

/-- The cached contraction is exactly the existing specified contraction. -/
theorem coefficientExchangeCounitStep_eq_original :
    coefficientExchangeCounitStep Λ ℓ f f' g' =
      boundedConstructibleBaseChangeCounitStep Λ ℓ f f' g' := by
  unfold coefficientExchangeCounitStep
  rfl

variable {f g f' g'} in
/-- The original specified exchange factors through the three equal cached steps. -/
theorem coefficientExchange_factorization (sq : CommSq g' f' f g) :
    boundedConstructibleBaseChange Λ ℓ sq =
      coefficientExchangeUnitStep Λ ℓ f g f' ≫
        (coefficientExchangeSquareStep Λ ℓ sq).hom ≫
          coefficientExchangeCounitStep Λ ℓ f f' g' := by
  rw [coefficientExchangeUnitStep_eq_original, coefficientExchangeSquareStep_eq_original,
    coefficientExchangeCounitStep_eq_original]
  exact boundedConstructibleBaseChange_eq_unit_square_counit Λ ℓ sq

end ExchangeStepCache
```

The section confines its variables and the `open Scheme` command. Existing declarations
outside it retain their original elaboration scope. The four old long lines in the
changed predicate are wrapped. The item directly imports the interface as a proof
dependency so the delivery compiles it before checking the new component proofs.

The new private component signatures are:

```lean
private lemma unit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((coefficientExchangeUnitStep Λ ℓ
      (f.asOver (Spec (.of k))) (g.asOver (Spec (.of k)))
      (f'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedAdjunction Λ f').unit.app
        ((coefficientDerivedUpperStar Λ g).obj
          ((coefficientDerivedLowerStar Λ f).obj K.obj))

private lemma square_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((coefficientExchangeSquareStep Λ ℓ (sq.asOver (Spec (.of k)))).hom.app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientAmbientSquare Λ sq).hom.app
          ((coefficientDerivedLowerStar Λ f).obj K.obj))

private lemma counit_step_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    ((coefficientExchangeCounitStep Λ ℓ
      (f.asOver (Spec (.of k))) (f'.asOver (Spec (.of k)))
      (g'.asOver (Spec (.of k)))).app K).hom =
      (coefficientDerivedLowerStar Λ f').map
        ((coefficientDerivedUpperStar Λ g').map
          ((coefficientDerivedAdjunction Λ f).counit.app K.obj))
```

## Users

`tools/downstream.py` lists 35 downstream modules. Textual predicate uses
occur only in the interface, the item, `FiniteDiscreteCoefficientExchange`, and
`FiniteDiscreteExchangeRealization`.
No other consumer unfolds the changed predicate. No signature or mathematical
construction is weakened, strengthened or replaced by a different morphism.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | E3 | Private component statements use equal cached factors; main theorem proved. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Uses the same named predicate abstractly; existing statement and proof unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | held (coord/claims) | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Uses the same named predicate and forwards its objectwise witness; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Cache the three specified factors; use equal cached factors in the predicate. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| TargetsCheck | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | held (coord/claims) | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | held (coord/claims) | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | held (coord/claims) | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No direct use of the predicate body or new caches; no source adaptation. |

## Status

landed 20261017T053257-L-3673023 2026-10-17 (merge of deliver/E3/Sheaf.Paper.CoefficientExchangeFromComparisons)
