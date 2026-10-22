/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Sheaf.Paper.IntegralResidueComparisonInterface
public import Sheaf.CategoryTheory.AdjunctionExchangeChain
public import Sheaf.Paper.BoundedExchangeAmbient
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Sheaf.Paper.FiniteDiscreteEtaleRealizationFull
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Deriving the finite discrete coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits

-- Keep hom types on the category's direct quiver, including the diagram records.
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

/-- Four isomorphisms identifying the three consecutive arrows in two diagrams. -/
structure FiniteDiscreteThreeStepComparison {C : Type*} [Category C]
    {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    (a : A0 ⟶ A1) (b : A1 ⟶ A2) (c : A2 ⟶ A3)
    (d : B0 ⟶ B1) (e : B1 ⟶ B2) (f : B2 ⟶ B3) where
  e0 : A0 ≅ B0
  e1 : A1 ≅ B1
  e2 : A2 ≅ B2
  e3 : A3 ≅ B3
  first : a ≫ e1.hom = e0.hom ≫ d
  second : b ≫ e2.hom = e1.hom ≫ e
  third : c ≫ e3.hom = e2.hom ≫ f

/-- Compose the three commuting squares. -/
noncomputable def FiniteDiscreteThreeStepComparison.arrowIso
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    (h : FiniteDiscreteThreeStepComparison a b c d e f) :
    Arrow.mk (a ≫ b ≫ c) ≅ Arrow.mk (d ≫ e ≫ f) :=
  Arrow.isoMk h.e0 h.e3 (by
    change h.e0.hom ≫ (d ≫ e ≫ f) = (a ≫ b ≫ c) ≫ h.e3.hom
    symm
    simp only [Category.assoc]
    rw [h.third, reassoc_of% h.second, reassoc_of% h.first])

/-- The three commuting squares identify their composite arrows.
Source: Mathlib `Arrow.isoMk`
(blueprint: lem-weil-pbc-three-step-arrow-comparison).

Proof. Reassociate and substitute the third, second and first square equations.
Use the endpoint isomorphisms in Arrow.isoMk. -/
theorem FiniteDiscreteThreeStepComparison.nonemptyArrowIso
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    (h : FiniteDiscreteThreeStepComparison a b c d e f) :
    Nonempty (Arrow.mk (a ≫ b ≫ c) ≅ Arrow.mk (d ≫ e ≫ f)) := ⟨h.arrowIso⟩

/-- Apply the three-step interface to arrows with specified factorizations. -/
theorem FiniteDiscreteThreeStepComparison.nonemptyArrowIsoOfFactorizations
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    (h : FiniteDiscreteThreeStepComparison a b c d e f)
    {η : A0 ⟶ A3} {θ : B0 ⟶ B3}
    (hη : η = a ≫ b ≫ c) (hθ : θ = d ≫ e ≫ f) :
    Nonempty (Arrow.mk η ≅ Arrow.mk θ) := by
  rw [hη, hθ]
  exact h.nonemptyArrowIso

/-- Three specified factors for each arrow, with their comparison squares. -/
structure FiniteDiscreteFactoredComparison {C : Type*} [Category C]
    {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    (a : A0 ⟶ A1) (b : A1 ⟶ A2) (c : A2 ⟶ A3)
    (d : B0 ⟶ B1) (e : B1 ⟶ B2) (f : B2 ⟶ B3)
    (η : A0 ⟶ A3) (θ : B0 ⟶ B3) where
  comparison : FiniteDiscreteThreeStepComparison a b c d e f
  source_eq : η = a ≫ b ≫ c
  target_eq : θ = d ≫ e ≫ f

/-- The comparison interface remembers the specified total arrows as well as their factors. -/
theorem FiniteDiscreteFactoredComparison.nonemptyArrowIso
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    {η : A0 ⟶ A3} {θ : B0 ⟶ B3}
    (h : FiniteDiscreteFactoredComparison a b c d e f η θ) :
    Nonempty (Arrow.mk η ≅ Arrow.mk θ) :=
  h.comparison.nonemptyArrowIsoOfFactorizations h.source_eq h.target_eq

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

namespace AlgebraicGeometry.ProEtale.CondensedRing

section ExchangeStepCache

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k

variable [IsFinitenessCoefficient ℓ Λ] (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

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

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Internal modules with the condensed continuous-function coefficient ring. -/
abbrev FiniteDiscreteInternalModules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)

/-- The bounded below etale category for these coefficients. -/
abbrev FiniteDiscreteEtalePlus (T : Scheme.{u}) :=
  DerivedCategory.Plus (Sheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} B)))

/-- Module-valued sheaves on the pro-etale site. -/
abbrev FiniteDiscreteProEtaleSheaves (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B))

variable (T : Scheme.{u})
  (E : FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T)

noncomputable instance finiteDiscreteEncoding_additive : E.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Realization is inverse image from the etale site followed by the given exact
coefficient equivalence, applied termwise to complexes. -/
@[irreducible] noncomputable def finiteDiscreteRealization :
    FiniteDiscreteEtalePlus B T ⥤ DerivedCategory (FiniteDiscreteInternalModules B T) :=
  DerivedCategory.Plus.ι ⋙
    D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)]) ⋙ D(E.functor)

noncomputable instance : (finiteDiscreteRealization B T E).CommShift ℤ := by
  unfold finiteDiscreteRealization
  infer_instance

instance : (finiteDiscreteRealization B T E).IsTriangulated := by
  unfold finiteDiscreteRealization
  infer_instance

instance : (finiteDiscreteRealization B T E).Full := by
  let V := DerivedCategory.Plus.ι ⋙
    D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)])
  have : V.Full := finiteDiscreteEtaleRealization_full B T
  exact inferInstanceAs (V ⋙ D(E.functor)).Full

/-- A sheaf in the underived realization has its single complex in the derived
realization's essential image. This is purely functorial and needs no descent theorem.
(blueprint: lem-weil-pbc-finite-discrete-single-realization)

Proof. Put the etale sheaf in degree zero, commute each of the two exact functors
with the single-complex functor, and apply the supplied sheaf isomorphism. -/
theorem finiteDiscreteRealization_single
    (M : FiniteDiscreteInternalModules B T)
    (hM : (ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)] ⋙ E.functor).essImage M) :
    (finiteDiscreteRealization B T E).essImage
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨A, ⟨e⟩⟩ := hM
  refine ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj A, ⟨?_⟩⟩
  unfold finiteDiscreteRealization
  exact D(E.functor).mapIso
      ((ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)]).mapDerivedCategorySingleFunctor 0 |>.app A) ≪≫
    (E.functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e


variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

open Scheme


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

end AlgebraicGeometry.ProEtale.CondensedRing
