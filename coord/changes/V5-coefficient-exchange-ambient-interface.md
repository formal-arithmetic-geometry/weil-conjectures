# AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteExchangeSteps

## Reason

The quarantined CoefficientExchangeFromComparisons proof repeatedly normalizes derived
functor object maps, restricted subcategory maps, and category quivers while comparing
implicit morphism endpoints. The archived proof exceeds the single-file limit. Profiling
also found this behavior when connecting the expanded etale factorization to its mapped
comparison. The repair retains the four objects and three arrows in ExchangeChain, and
retains those diagrams as arguments of the comparison and factorization records. Generic
map/composite and adjunction-mate equations are proved once over abstract categories.

The internal chain uses the actual residueExchange adjunctions and square comparison.
Their equations with coefficientDerivedAdjunction and coefficientAmbientSquare are proved
in the restored item. The original bounded exchange is cached without altering it, and
boundedConstructibleBaseChange_hom_eq_ambient identifies it with the actual ambient mate.
The etale chain uses the actual etale adjunction and square comparison. The existing etale
component/mate formulas identify its factors with the specified unit, square, and counit.
Both typed total-map caches have proved equations with the original total maps. No
properness, Cartesianity, invertibility, or new coefficient hypothesis is introduced.

ExchangeChain.Comparison is exactly FiniteDiscreteThreeStepComparison on its six arrow
fields. ExchangeChain.FactoredComparison stores this comparison and both original total
factorizations, now written using the diagrams' composite function. Its toOriginal
construction retains all four vertex isomorphisms, all three squares, and both equations.
Its nonemptyArrowIso API therefore identifies precisely the same total arrows as before.
ExchangeChain.mapHom retains the mapped diagram endpoints in the type of a mapped
arrow. The proved mapHom_eq equation identifies it with the original functor map;
mapHom_composite proves the functorial factorization without expanding endpoints.
The old restricted internal factors and the ambient factors agree under fully faithful
inclusion by the existing restriction unit/counit and pullback-composition equations; this
is the same identification used by BoundedExchangeAmbient.

The finite-discrete predicate specializes the arbitrary-coefficient predicate to the
continuous-function condensed ring. This is a representation change of the same diagram,
with direct constructions throughout and no chosen witness from an unproved existence.
Empty schemes, zero objects, and zero coefficient rings use the same formulas.

The existing public theorem coefficientComparisonData_exchangeSteps has its quarantined
signature verbatim. The adopted WeilConjectures tree is untouched. The unchanged original
realization functors, module categories, and comparison records keep their definitions.
A local priority for the category's direct quiver avoids reducing the equivalent reflexive
quiver when elaborating the new diagram API; it exports no instance attribute.

This predicate is an intermediate proof interface. Target signatures and the actual
exchange constructions remain unchanged. The definition repair requests independent
semantic review, including any target whose statement definitions use this predicate.
No protected blueprint unit or its realized proof steps are bypassed.

## Old

```lean
def finiteDiscreteExchangeSteps [IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj.{u} B)]
    (sq : CommSq g' f' f g)
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

## New

```lean
namespace ExchangeChain

/-- A comparison retaining its two diagrams as arguments.
(blueprint: def-weil-pbc-three-step-chain-comparison). -/
def Comparison {C : Type*} [Category C] (s t : ExchangeChain C) :=
  FiniteDiscreteThreeStepComparison s.first s.second s.third t.first t.second t.third

/-- Two actual arrows with specified three-step diagrams and a comparison of those diagrams. -/
structure FactoredComparison {C : Type*} [Category C] (s t : ExchangeChain C)
    (η : s.obj0 ⟶ s.obj3) (θ : t.obj0 ⟶ t.obj3) where
  comparison : Comparison s t
  source_eq : η = s.composite
  target_eq : θ = t.composite

/-- Recover the original arrow-level interface without changing any vertex or arrow. -/
def FactoredComparison.toOriginal {C : Type*} [Category C] {s t : ExchangeChain C}
    {η : s.obj0 ⟶ s.obj3} {θ : t.obj0 ⟶ t.obj3} (h : FactoredComparison s t η θ) :
    FiniteDiscreteFactoredComparison s.first s.second s.third
      t.first t.second t.third η θ :=
  ⟨h.comparison, h.source_eq, h.target_eq⟩

/-- The retained factorizations identify their original total arrows. -/
theorem FactoredComparison.nonemptyArrowIso {C : Type*} [Category C]
    {s t : ExchangeChain C} {η : s.obj0 ⟶ s.obj3} {θ : t.obj0 ⟶ t.obj3}
    (h : FactoredComparison s t η θ) : Nonempty (Arrow.mk η ≅ Arrow.mk θ) :=
  h.toOriginal.nonemptyArrowIso

end ExchangeChain

/-- The actual internal exchange diagram, retaining its four ambient vertices.
(blueprint: def-weil-pbc-ambient-typed-bounded-exchange). -/
noncomputable def coefficientInternalExchangeChain
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : residueExchangeDerived Λ X) : ExchangeChain (residueExchangeDerived Λ Y') :=
  Adjunction.exchangeChain (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f') (residueExchangeSquare Λ sq).hom K

/-- The actual etale exchange diagram, retaining its four vertices.
(blueprint: def-weil-pbc-ambient-typed-etale-exchange). -/
noncomputable def coefficientEtaleExchangeChain (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    ExchangeChain (FiniteDiscreteEtalePlus B₀ Y') :=
  Adjunction.exchangeChain
    (Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) f)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) f')
    (Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).hom L

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- The original bounded exchange with endpoints fixed by its actual exchange diagram.
Source: boundedConstructibleBaseChange.
(blueprint: def-weil-pbc-ambient-typed-bounded-exchange). -/
noncomputable def coefficientAmbientBoundedExchange
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    (coefficientInternalExchangeChain Λ sq K.obj).obj0 ⟶
      (coefficientInternalExchangeChain Λ sq K.obj).obj3 :=
  ((boundedConstructibleBaseChange Λ ℓ (sq.asOver (Spec (.of k)))).app K).hom

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- The typed cache is exactly the original bounded exchange component. -/
theorem coefficientAmbientBoundedExchange_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    coefficientAmbientBoundedExchange ℓ k Λ sq K =
      ((boundedConstructibleBaseChange Λ ℓ (sq.asOver (Spec (.of k)))).app K).hom := by
  unfold coefficientAmbientBoundedExchange
  rfl

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- The bounded exchange factors through the three actual diagram arrows. -/
theorem coefficientAmbientBoundedExchange_factorization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    coefficientAmbientBoundedExchange ℓ k Λ sq K =
      (coefficientInternalExchangeChain Λ sq K.obj).composite := by
  rw [coefficientAmbientBoundedExchange_eq]
  exact (boundedConstructibleBaseChange_hom_eq_ambient Λ ℓ k sq K).trans
    (Adjunction.mate_eq_exchangeChain_composite
      (residueExchangeAdjunction Λ f) (residueExchangeAdjunction Λ f')
      (residueExchangeSquare Λ sq).hom K.obj)

/-- The original etale exchange, with endpoints fixed by its actual exchange diagram.
Source: Etale.baseChange.
(blueprint: def-weil-pbc-ambient-typed-etale-exchange). -/
noncomputable def coefficientEtaleExchange (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    (coefficientEtaleExchangeChain B₀ sq L).obj0 ⟶
      (coefficientEtaleExchangeChain B₀ sq L).obj3 :=
  (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).app L

/-- The typed bounded cache retains the original arrow, including both endpoints. -/
theorem coefficientAmbientBoundedExchange_arrow_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj Λ X)) :
    Arrow.mk (coefficientAmbientBoundedExchange ℓ k Λ sq K) =
      Arrow.mk (((boundedConstructibleBaseChange Λ ℓ
        (sq.asOver (Spec (.of k)))).app K).hom) := by
  unfold coefficientAmbientBoundedExchange coefficientInternalExchangeChain
    Adjunction.exchangeChain residueExchangeUpperStar residueExchangeLowerStar
    boundedConstructibleLowerStar boundedConstructibleUpperStar
  rfl

/-- The mapped typed etale cache retains the original mapped arrow and its endpoints. -/
theorem coefficientEtaleExchange_map_arrow_eq (B₀ : Type) [CommRing B₀]
    {D : Type*} [Category D] (F : FiniteDiscreteEtalePlus B₀ Y' ⥤ D)
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    Arrow.mk ((coefficientEtaleExchangeChain B₀ sq L).mapHom F
        (coefficientEtaleExchange B₀ sq L)) =
      Arrow.mk (F.map ((Etale.baseChange
        (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).app L)) := by
  unfold ExchangeChain.mapHom coefficientEtaleExchange
  rfl

/-- The typed etale cache is exactly the original exchange component. -/
theorem coefficientEtaleExchange_eq (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    coefficientEtaleExchange B₀ sq L =
      (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).app L := by
  unfold coefficientEtaleExchange
  rfl

/-- The etale exchange factors through the three actual diagram arrows. -/
theorem coefficientEtaleExchange_factorization (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    coefficientEtaleExchange B₀ sq L =
      (coefficientEtaleExchangeChain B₀ sq L).composite := by
  rw [coefficientEtaleExchange_eq]
  unfold coefficientEtaleExchangeChain
  rw [Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  exact (Etale.baseChange_app_eq_mateEquiv
    (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq L).trans
      (Adjunction.mate_eq_exchangeChain_composite _ _ _ _)

/-- Every functor preserves this specified etale exchange factorization. -/
theorem coefficientEtaleExchange_map_factorization (B₀ : Type) [CommRing B₀]
    {D : Type*} [Category D] (F : FiniteDiscreteEtalePlus B₀ Y' ⥤ D)
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    (coefficientEtaleExchangeChain B₀ sq L).mapHom F
        (coefficientEtaleExchange B₀ sq L) =
      ((coefficientEtaleExchangeChain B₀ sq L).map F).composite := by
  rw [coefficientEtaleExchange_factorization]
  exact ExchangeChain.mapHom_composite _ F

/-- The shared diagram predicate for an arbitrary condensed coefficient ring.
The four vertices, three factors, and both original total exchange maps are retained.
(blueprint: def-weil-pbc-coefficient-exchange-diagram). -/
def coefficientExchangeSteps (B₀ : Type) [CommRing B₀]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] [IsFinitenessCoefficient ℓ Λ]
    (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B₀ X ⥤ residueExchangeDerived Λ X)
    (F1 : FiniteDiscreteEtalePlus B₀ Y' ⥤ residueExchangeDerived Λ Y') : Prop :=
  ∀ (L : FiniteDiscreteEtalePlus B₀ X)
      (hL : ProEtale.boundedConstructible (condensedRingObj Λ X) (F0.obj L)),
    let N : ProEtale.BoundedConstructible (condensedRingObj Λ X) := ⟨F0.obj L, hL⟩
    let s := coefficientInternalExchangeChain Λ sq N.obj
    let t := (coefficientEtaleExchangeChain B₀ sq L).map F1
    Nonempty (ExchangeChain.FactoredComparison s t
      (coefficientAmbientBoundedExchange ℓ k Λ sq N)
      ((coefficientEtaleExchangeChain B₀ sq L).mapHom F1
        (coefficientEtaleExchange B₀ sq L)))

/-- Compatibility with the three specified exchange steps for realization functors. -/
def finiteDiscreteExchangeSteps [IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj.{u} B)]
    (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B X ⥤ DerivedCategory (FiniteDiscreteInternalModules B X))
    (F1 : FiniteDiscreteEtalePlus B Y' ⥤ DerivedCategory (FiniteDiscreteInternalModules B Y')) :
    Prop :=
  coefficientExchangeSteps ℓ k B (Profinite.continuousMapRingObj B) sq F0 F1

/-- A step comparison identifies the two original specified total arrows.
Source: the factored comparison and the defining equations for the two typed arrows.
(blueprint: def-weil-pbc-coefficient-exchange-diagram).

Proof. Apply the generic factored-comparison arrow isomorphism. Rewrite both entire
arrow objects by the cache equations, retaining the original endpoints as well as
its morphisms. No component or derived functor is expanded in the consumer. -/
theorem finiteDiscreteExchangeSteps_arrowIso
    [IsFinitenessCoefficient ℓ (Profinite.continuousMapRingObj.{u} B)]
    (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B X ⥤ DerivedCategory (FiniteDiscreteInternalModules B X))
    (F1 : FiniteDiscreteEtalePlus B Y' ⥤ DerivedCategory (FiniteDiscreteInternalModules B Y'))
    (hsteps : finiteDiscreteExchangeSteps B ℓ k sq F0 F1)
    (L : FiniteDiscreteEtalePlus B X)
    (hL : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj B) X)
      (F0.obj L)) :
    Nonempty (Arrow.mk (((boundedConstructibleBaseChange
      (Profinite.continuousMapRingObj B) ℓ (sq.asOver (Spec (.of k)))).app
        ⟨F0.obj L, hL⟩).hom) ≅
      Arrow.mk (F1.map ((Etale.baseChange
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L))) := by
  obtain ⟨H⟩ := hsteps L hL
  have h := H.nonemptyArrowIso
  rw [coefficientAmbientBoundedExchange_arrow_eq,
    coefficientEtaleExchange_map_arrow_eq] at h
  exact h

```

The new generic ExchangeChain data and its fully proved equations are in
Sheaf.CategoryTheory.AdjunctionExchangeChain. The diagram-indexed comparison is in the
existing FiniteDiscreteRealizationFunctor module. ThreeStepAdjunctionComparison adds a
fully proved wrapper of its existing theorem returning the diagram-indexed comparison,
and a coherent-family specialization of that wrapper. The family specialization keeps
FunctorComparisonSquare folded while the concrete families are supplied. Its public
import of CoefficientDerivedFunctorAPI is required by that predicate in its statement;
the API does not import ThreeStepAdjunctionComparison, so the dependency is acyclic.
The original theorem statement and proof remain unchanged. The restored item also
transports P.square across the reflexive equality between its eta-expanded pullback
family and the original whole family. This is an equality of the same data; no
coherence equation, comparison isomorphism, or coefficient construction changes. CoefficientDerivedFunctorAPI
and IntegralResidueComparisonInterface are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Original theorem preserved; add its diagram-indexed conclusion and coherent-family specialization. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | V5 | Restored theorem; original public signature retained; proof uses the diagram API. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Passes the same exchange-step predicate through its unchanged public signature; quarantined source restored byte-identically as a prerequisite of the adapted consumer. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Forced proof adaptation: use finiteDiscreteExchangeSteps_arrowIso to return the identical original total-arrow conclusion; original signature preserved. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Passes the same exchange-step predicate through its unchanged public signature; quarantined source restored byte-identically as a prerequisite of the adapted consumer. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Repair the diagram predicate; preserve all original module categories, realization functors, and public generic comparison records. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.Paper.FiniteDiscreteScalarConstantModels | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | No occurrence of the changed predicate in its declarations; existing realization and module categories retained. |

The table includes all 22 current live downstream modules listed by downstream.py and the
quarantined parent chain. Zero live importers of the quarantined item does not withdraw
it or its parents. No module is withdrawn. Compilation results are recorded in report.md.

## Forced adaptation and restored prerequisites

All three parent modules are unclaimed. With the changed interface, the original
FiniteDiscreteExchangeComparison fails at line 190: H.nonemptyArrowIso has the typed
cache Arrow endpoints, while the goal has the original boundedConstructibleBaseChange
and F.map (Etale.baseChange ...) Arrow endpoints. The original two lines obtaining H
and returning H.nonemptyArrowIso are replaced by one application of the fully proved
finiteDiscreteExchangeSteps_arrowIso. Its API rewrites equality of entire Arrow objects,
so neither endpoints nor morphisms are hidden by the adaptation. The pre-existing
139-character conclusion line is only wrapped; every binder and public signature remains
identical. The original failure and passing adaptation are recorded in report.md.

FiniteDiscreteExchangeRealization and FiniteDiscreteCoefficientExchange are restored
byte-identically from their quarantine archives, because they are the two missing
prerequisites of this consumer. Their source attachments and proof dependencies remain
intact. The comparison node keeps its mathematical statement and original unit route;
its stale lean.statement containing an already-discharged encoding hypothesis is
synchronized with the archived Lean signature, without changing that signature.

## Status

landed 20261022T011939-L-3235863 2026-10-22 (merge of deliver/V5/Sheaf.Paper.CoefficientExchangeFromComparisons)
