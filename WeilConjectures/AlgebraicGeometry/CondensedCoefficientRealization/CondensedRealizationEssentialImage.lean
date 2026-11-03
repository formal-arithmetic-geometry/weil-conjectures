/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicQbarConstructibleRealization

/-! # Essential image of the kept condensed section realization

Source: current sk-def-sfb-constructible, final paragraph, and
cor-coef-verdier-weil-equivariance.proof.md, paragraph 2.
(blueprint: lem-sf-condensed-realization-essential-image).

These lemmas use the literal section functor of the kept H4 realization. They are
independent of the compatibility data still used by legacy importers.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale.CondensedCoefficientRealization

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
open scoped CategoryTheory.Obj

set_option synthInstance.maxSize 4096

attribute [local instance 1000001] ModuleObjectRingedComparison.sectionRingHasSheafCompose

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- Transport finite constant models, their stratifications, and their bounded
cohomology along isomorphisms. This is the repleteness argument used by the kept
constructible section equivalence. -/
private theorem constantModel_isoClosed :
    (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms := by
  classical
  have hlocal (Y : Scheme.{u})
      {M N : Internal Λ Y} (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := hM
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u}) {M N : Internal Λ Y} (e : M ≅ N)
      (hM : IsFiniteConstantStratified Λ Y M) : IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ hlocal _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  let : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) :=
    ⟨fun e hM ↦ by
      unfold IsConstantModelConstructible at hM ⊢
      split_ifs at hM ⊢ with hX
      · exact hstrat _ e hM
      · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)⟩
  exact ⟨fun e hK ↦ ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
    fun n ↦ ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩⟩

/-- The essential image of the literal section realization consists exactly of the
existing bounded constructible objects in section coordinates.
Source: current sk-def-sfb-constructible, final paragraph, and
cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-condensed-realization-essential-image).
Proof: a constructible section object has its inverse-equivalence object as a
constructible preimage, and the counit identifies its realization with the object.
Conversely apply the inverse equivalence to an isomorphism from a realized object;
compose with the unit and transport boundedness and the finite constant models.
The proof applies to every commutative condensed coefficient and every scheme. -/
theorem sectionConstructible_iff_realized :
    ∀ L, sectionConstructible Λ X L ↔
      ∃ K : ConstantModelBoundedConstructible Λ X,
        Nonempty ((forward Λ X).obj K.obj ≅ L) := by
  intro L
  let := constantModel_isoClosed Λ X
  constructor
  · intro hL
    exact ⟨⟨(ambientEquivalence Λ X).inverse.obj L, hL⟩,
      ⟨(ambientEquivalence Λ X).counitIso.app L⟩⟩
  · rintro ⟨K, ⟨e⟩⟩
    exact (constantModelBoundedConstructible Λ X).prop_of_iso
      ((ambientEquivalence Λ X).unitIso.app K.obj ≪≫
        (ambientEquivalence Λ X).inverse.mapIso e) K.property

/-- Realization induces a bijection on the actual ambient morphisms of bounded
constructible complexes, without choosing a coefficient representative.
Source: current sk-def-sfb-constructible, final paragraph, and
cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-condensed-realization-essential-image).
Proof: the fixed ambient section functor is an equivalence. Its map on each Hom
set is therefore bijective; full subcategories retain these same morphisms. -/
theorem constructible_realization_map_bijective
    (K L : ConstantModelBoundedConstructible Λ X) :
    Function.Bijective
      ((forward Λ X).map : (K.obj ⟶ L.obj) → (_ ⟶ _)) := by
  let : (forward Λ X).IsEquivalence := by unfold forward; infer_instance
  exact ⟨Functor.map_injective _, Functor.map_surjective _⟩

end AlgebraicGeometry.ProEtale.CondensedCoefficientRealization
