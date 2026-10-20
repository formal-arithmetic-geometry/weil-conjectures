/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-!
# Descent of morphisms in the derived category along a surjective étale morphism

Let `u : U ⟶ T` be surjective and étale, and let `Z` with projections `r₁, r₂ : Z ⟶ U` be a
fibre product `U ×_T U`. Morphisms `K ⟶ M` in `D(T_ét, Λ)` between objects which are, up to a
common shift, sheaves placed in degree zero, descend along `u`: a morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for some `γ : K ⟶ M`.
Morphisms between sheaves placed in one degree are morphisms of sheaves, and those glue
(`AlgebraicGeometry.Etale.exists_hom_of_upperStar`).

## Main statements

- `AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`: degree zero.
- `AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift`: up to a
  common shift.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E] {A : Type*} [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A] (Φ : C ⥤ D) (Ψ : D ⥤ E) [Φ.CommShift A]
  [Ψ.CommShift A]

/-- A morphism `δ : Φ K ⟶ Φ M`, transported to `Φ (K⟦a⟧) ⟶ Φ (M⟦a⟧)` along the commutation of
`Φ` with the shift, and then mapped by `Ψ`, is `(Ψ δ)⟦a⟧` up to the commutation of `Φ ⋙ Ψ`
with the shift. -/
@[reassoc]
lemma commShiftIso_comp_inv_app_map_shift_comp {K M : C} (δ : Φ.obj K ⟶ Φ.obj M) (a : A) :
    ((Φ ⋙ Ψ).commShiftIso a).inv.app K ≫
        Ψ.map ((Φ.commShiftIso a).hom.app K ≫ δ⟦a⟧' ≫ (Φ.commShiftIso a).inv.app M) ≫
        ((Φ ⋙ Ψ).commShiftIso a).hom.app M = (Ψ.map δ)⟦a⟧' := by
  rw [Functor.commShiftIso_comp_inv_app, Functor.commShiftIso_comp_hom_app, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp

/-- Conjugating by an isomorphism `τ : Θ ≅ Φ ⋙ Ψ` commuting with the shifts commutes with the
transport of morphisms along the shift. -/
lemma conj_commShiftIso {Θ : C ⥤ E} [Θ.CommShift A] (τ : Θ ≅ Φ ⋙ Ψ) [NatTrans.CommShift τ.hom A]
    {K M : C} (δ : Φ.obj K ⟶ Φ.obj M) (a : A) :
    τ.hom.app (K⟦a⟧) ≫
        Ψ.map ((Φ.commShiftIso a).hom.app K ≫ δ⟦a⟧' ≫ (Φ.commShiftIso a).inv.app M) ≫
        τ.inv.app (M⟦a⟧) =
      (Θ.commShiftIso a).hom.app K ≫ (τ.hom.app K ≫ Ψ.map δ ≫ τ.inv.app M)⟦a⟧' ≫
        (Θ.commShiftIso a).inv.app M := by
  rw [NatTrans.app_shift τ.hom a K, NatTrans.app_shift τ.inv a M]
  simp only [Category.assoc]
  rw [commShiftIso_comp_inv_app_map_shift_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

set_option maxHeartbeats 1000000 in
-- the gluing manipulates long composites of derived and sheaf-level isomorphisms
/-- **Descent of morphisms of sheaves placed in degree zero along a surjective étale
morphism.** Let `u : U ⟶ T` be surjective and étale, `Z` with `r₁, r₂ : Z ⟶ U` a fibre product
`U ×_T U`, and `K, M ∈ D(T_ét, Λ)` isomorphic to sheaves placed in degree zero. A morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for a morphism `γ : K ⟶ M`. -/
theorem Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback {T U Z : Scheme.{u}}
    {K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (eK : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eM : M ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G)
    (u : U ⟶ T) [Etale u] [Surjective u] {r₁ r₂ : Z ⟶ U} (hZ : IsPullback r₁ r₂ u u)
    (δ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((u)^*[ModuleCat.{u + 1} Λ])).obj M)
    (hδ : (leftDerivedUpperStarComp _ r₁ u).hom.app K ≫ (L((r₁)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₁ u).inv.app M =
        (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).hom.app K ≫ (L((r₂)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).inv.app M) :
    ∃ γ : K ⟶ M, (L((u)^*[ModuleCat.{u + 1} Λ])).map γ = δ := by
  let s := fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) ↦
    ((g)^*[ModuleCat.{u + 1} Λ]).singleFunctorCompLeftDerivedFunctorIso
  have hs : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z)
      {A B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
      (f : A ⟶ B),
      (L((g)^*[ModuleCat.{u + 1} Λ])).map ((_root_.DerivedCategory.singleFunctor _ 0).map f) =
        (s g).hom.app A ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ((g)^*[_].map f) ≫
          (s g).inv.app B := fun {Y Z} g {A B} f ↦ by
    rw [← cancel_mono ((s g).hom.app B), Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact (s g).hom.naturality f
  let φ₀ := (_root_.DerivedCategory.singleFunctor (Sheaf U.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).preimage ((s u).inv.app F ≫ (L((u)^*[_])).map eK.inv ≫ δ ≫
      (L((u)^*[_])).map eM.hom ≫ (s u).hom.app G)
  have hφ₀ : (_root_.DerivedCategory.singleFunctor _ 0).map φ₀ = (s u).inv.app F ≫
      (L((u)^*[_])).map eK.inv ≫ δ ≫ (L((u)^*[_])).map eM.hom ≫ (s u).hom.app G :=
    Functor.map_preimage _ _
  let e : PUnit.{u + 1} → (U ⟶ T) := fun _ ↦ u
  have he : ∀ j, Etale (e j) := fun _ ↦ inferInstance
  have hcov : ⋃ j, Set.range (e j).base = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨⟨⟩, u.surjective x⟩
  obtain ⟨φ', hφ'⟩ := Etale.exists_hom_of_upperStar e he hcov F G (fun _ ↦ φ₀) (by
    intro j k W a b w ha hb _ _ _
    apply (_root_.DerivedCategory.singleFunctor _ 0).map_injective
    have key : ∀ (c : W ⟶ U) (hc : w = c ≫ u),
        (_root_.DerivedCategory.singleFunctor _ 0).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app F ≫
          (c)^*[ModuleCat.{u + 1} Λ].map φ₀ ≫
            (Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.app G) =
        (s w).inv.app F ≫ (L((w)^*[ModuleCat.{u + 1} Λ])).map eK.inv ≫
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app K ≫
            (L((c)^*[ModuleCat.{u + 1} Λ])).map δ ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.app M) ≫
          (L((w)^*[ModuleCat.{u + 1} Λ])).map eM.hom ≫ (s w).hom.app G := by
      intro c hc
      have nK := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.naturality eK.inv
      have nM := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.naturality eM.hom
      have hc' : (_root_.DerivedCategory.singleFunctor _ 0).map
          ((c)^*[ModuleCat.{u + 1} Λ].map φ₀) =
          (s c).inv.app _ ≫ (L((c)^*[ModuleCat.{u + 1} Λ])).map
            ((_root_.DerivedCategory.singleFunctor _ 0).map φ₀) ≫ (s c).hom.app _ := by
        rw [hs]
        simp only [Category.assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
        erw [Category.comp_id]
      have h₁ : ∀ Y, (_root_.DerivedCategory.singleFunctor _ 0).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app Y) =
          (s w).inv.app Y ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app _ ≫
            (L((c)^*[ModuleCat.{u + 1} Λ])).map ((s u).hom.app Y) ≫ (s c).hom.app _ :=
        fun Y ↦ by
          rw [Etale.leftDerivedUpperStarComp_hom_app_singleFunctor_obj c u w hc Y]
          exact (Iso.inv_hom_id_app_assoc (s w) Y _).symm
      have h₂ : (_root_.DerivedCategory.singleFunctor _ 0).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.app G) =
          (s c).inv.app _ ≫ (L((c)^*[ModuleCat.{u + 1} Λ])).map ((s u).inv.app G) ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.app _ ≫
              (s w).hom.app G := by
        rw [← cancel_epi ((_root_.DerivedCategory.singleFunctor _ 0).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app G)),
          ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, h₁ G]
        simp [← Functor.map_comp_assoc]
      rw [Functor.map_comp, Functor.map_comp, h₁ F, hc', h₂]
      simp only [Functor.comp_map] at nK nM
      have M₁ : (s u).hom.app F ≫ (_root_.DerivedCategory.singleFunctor _ 0).map φ₀ ≫
          (s u).inv.app G = (L((u)^*[ModuleCat.{u + 1} Λ])).map eK.inv ≫ δ ≫
            (L((u)^*[ModuleCat.{u + 1} Λ])).map eM.hom := by
        rw [hφ₀]; simp
      have M₂ := congrArg (L((c)^*[ModuleCat.{u + 1} Λ])).map M₁
      simp only [Functor.map_comp] at M₂
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [reassoc_of% M₂, ← reassoc_of% nK, reassoc_of% nM]
    rw [key a ha, key b hb]
    have hab : a ≫ u = b ≫ u := ha.symm.trans hb
    let ℓ := hZ.lift a b hab
    have T₁ := Etale.leftDerivedUpperStarComp_conj_comp ℓ r₁ u a (r₁ ≫ u) w
      (hZ.lift_fst _ _ _).symm rfl ha δ
    have T₂ := Etale.leftDerivedUpperStarComp_conj_comp ℓ r₂ u b (r₁ ≫ u) w
      (hZ.lift_snd _ _ _).symm hZ.w hb δ
    have hτ : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a u w ha).hom.app K ≫
        (L((a)^*[ModuleCat.{u + 1} Λ])).map δ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a u w ha).inv.app M =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) b u w hb).hom.app K ≫
        (L((b)^*[ModuleCat.{u + 1} Λ])).map δ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) b u w hb).inv.app M := by
      rw [T₁, T₂, hδ]
    rw [hτ])
  refine ⟨eK.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map φ' ≫ eM.inv, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hs, hφ' ⟨⟩, hφ₀]
  simp [← Functor.map_comp_assoc]

/-- **Descent of morphisms along a surjective étale morphism, up to a shift.** As
`AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`, for `K, M` whose
shifts `K⟦n⟧, M⟦n⟧` are sheaves placed in degree zero: the derived pullbacks commute with the
shift, compatibly with their composition isomorphisms. -/
theorem Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback_of_shift {T U Z : Scheme.{u}}
    {K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (n : ℤ)
    (eK : K⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eM : M⟦n⟧ ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G)
    (u : U ⟶ T) [Etale u] [Surjective u] {r₁ r₂ : Z ⟶ U} (hZ : IsPullback r₁ r₂ u u)
    (δ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((u)^*[ModuleCat.{u + 1} Λ])).obj M)
    (hδ : (leftDerivedUpperStarComp _ r₁ u).hom.app K ≫ (L((r₁)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₁ u).inv.app M =
        (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).hom.app K ≫ (L((r₂)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).inv.app M) :
    ∃ γ : K ⟶ M, (L((u)^*[ModuleCat.{u + 1} Λ])).map γ = δ := by
  let Φ := L((u)^*[ModuleCat.{u + 1} Λ])
  let δ' := (Φ.commShiftIso n).hom.app K ≫ δ⟦n⟧' ≫ (Φ.commShiftIso n).inv.app M
  obtain ⟨γ', hγ'⟩ := Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback eK eM u hZ δ' (by
    rw [Functor.conj_commShiftIso _ _ (leftDerivedUpperStarComp _ r₁ u) δ n,
      Functor.conj_commShiftIso _ _ (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w) δ n, hδ])
  refine ⟨(shiftFunctor _ n).preimage γ', (shiftFunctor _ n).map_injective ?_⟩
  have h := Φ.commShiftIso_hom_naturality ((shiftFunctor _ n).preimage γ') n
  rw [Functor.map_preimage, hγ'] at h
  rw [← cancel_epi ((Φ.commShiftIso n).hom.app K), ← h]
  simp only [δ', Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end AlgebraicGeometry
