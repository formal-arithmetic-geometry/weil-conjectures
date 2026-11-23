/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriekIso
public import WeilConjectures.TraceFormula.ConstructibleGeneration
public import WeilConjectures.TraceFormula.FieldDualizable
public import WeilConjectures.TraceFormula.Specialization.ConstantFamilySmoothUnit
public import WeilConjectures.TraceFormula.Specialization.ConstantFamilySpecialization
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorGeneric
public import WeilConjectures.TraceFormula.Specialization.SpecializationDualizable

/-!

# Generic invertibility of the specialization map of a constant family

Let `Y` be a smooth, irreducible and reduced separated `k`-scheme of finite type, and
`σ_Y(L) : Lπ_Y^* L ⟶ Ψ_{Y × S}(L)` the specialization map of its constant family
(`ProEtale.CondensedRing.constantFamilySpecialization`). For every bounded constructible
`ℚ̄_ℓ`-complex `L` on `Y`, `σ_Y(L)` is an isomorphism over the inverse image in `Y ⊗ k'` of a
dense open subset of `Y` (`ProEtale.CondensedRing.exists_dense_isIso_constantFamilySpecialization`).
This is the generic part of the proof that `σ_Y(L)` is an isomorphism
(`ProEtale.CondensedRing.isIso_constantFamilySpecialization_app`).

## Proof

The complexes `L` for which `σ_Y(L)` is generically invertible form a triangulated subcategory
(`ProEtale.CondensedRing.isTriangulated_genericallyIsoSpecialization`), since `σ_Y` commutes with
the shifts and two dense opens meet in a dense open. So it suffices to treat the lisse generators
`N ≅ Rg_* j_! L` of `Dᵇc(Y)⟦ℚ̲̄_ℓ⟧`, with `g : Z ⟶ Y` a closed immersion, `j : U ⟶ Z` an open
immersion and `L` dualizable.
* If `g` is not surjective, `N` vanishes on the dense open complement `W` of its image, and so does
  `σ_Y(N)`, by the smooth pullback compatibility along `W ⟶ Y`.
* If `g` is surjective, it is an isomorphism (`Y` is reduced), so `h = j ≫ g` is an open immersion
  with `Lh^* N ≅ L` dualizable. The constant family of the smooth scheme `U` has invertible
  specialization unit (`ProEtale.CondensedRing.isIso_deformationModel_bot_unit_of_smooth`), hence
  invertible specialization map at dualizable objects
  (`ProEtale.CondensedRing.NearbyCyclesModel.isIso_specialization_app_of_isDualizable`), and
  `σ_Y(N)` is invertible over the dense open image of `h`, by the smooth pullback compatibility
  along `h`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If the pullback of a morphism `φ` along an open immersion `f` is an isomorphism, so is its
restriction to every open contained in the image of `f`. -/
lemma isIso_leftDerivedUpperStar_ι_map_of_subset_range {T V : Scheme.{u}} (f : V ⟶ T)
    [IsOpenImmersion f]
    {A B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (φ : A ⟶ B) [IsIso (L((f)^*⟦Λ⟧).map φ)] (W : T.Opens)
    (hW : (W : Set T) ⊆ Set.range f.base) : IsIso (L((W.ι)^*⟦Λ⟧).map φ) := by
  have hr : Set.range W.ι.base ⊆ Set.range f.base := by
    rw [Scheme.Opens.range_ι]
    exact hW
  rw [← IsOpenImmersion.lift_fac f W.ι hr,
    NatIso.isIso_map_iff (leftDerivedUpperStarComp Λ (IsOpenImmersion.lift f W.ι hr) f),
    Functor.comp_map]
  infer_instance

/-- The specialization map of a constant family commutes with the shifts. -/
instance commShift_constantFamilySpecialization (Y : Over (Spec (.of k))) :
    NatTrans.CommShift (constantFamilySpecialization k' Λ Y) ℤ := by
  unfold constantFamilySpecialization
  infer_instance

/-- The specialization map `σ_Y` of the constant family restricted to an open `W` of its special
fibre `Y ⊗ k'`, as a natural transformation `L ↦ σ_Y(L)|_W`. -/
noncomputable def restrictedConstantFamilySpecialization (Y : Over (Spec (.of k)))
    (W : (deformationSpecialFibre Y ⊥ k').left.Opens) :=
  Functor.whiskerRight (constantFamilySpecialization k' Λ Y) L((W.ι)^*⟦Λ⟧)

instance (Y : Over (Spec (.of k))) (W : (deformationSpecialFibre Y ⊥ k').left.Opens) :
    NatTrans.CommShift (restrictedConstantFamilySpecialization k' Λ Y W) ℤ := by
  unfold restrictedConstantFamilySpecialization
  infer_instance

/-- The isomorphism locus of the restricted specialization map. -/
lemma isoLocus_restrictedConstantFamilySpecialization_iff (Y : Over (Spec (.of k)))
    (W : (deformationSpecialFibre Y ⊥ k').left.Opens)
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))) :
    (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus L ↔
      IsIso ((L((W.ι)^*⟦Λ⟧)).map ((constantFamilySpecialization k' Λ Y).app L)) :=
  Iff.rfl

/-- The isomorphism loci of the restricted specialization maps decrease with the open. -/
lemma isoLocus_restrictedConstantFamilySpecialization_mono (Y : Over (Spec (.of k)))
    {W W' : (deformationSpecialFibre Y ⊥ k').left.Opens} (hW : W' ≤ W)
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))}
    (hL : (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus L) :
    (restrictedConstantFamilySpecialization k' Λ Y W').isoLocus L := by
  have : IsIso ((L((W.ι)^*⟦Λ⟧)).map ((constantFamilySpecialization k' Λ Y).app L)) := hL
  exact isIso_leftDerivedUpperStar_ι_map_of_le Λ hW _

/-- The complexes `L` on `Y` whose specialization map `σ_Y(L)` is *generically invertible*: an
isomorphism over the inverse image in `Y ⊗ k'` of some dense open `U ⊆ Y`. -/
def genericallyIsoSpecialization (Y : Over (Spec (.of k))) :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))) :=
  fun L ↦ ∃ U : Y.left.Opens, Dense (U : Set Y.left) ∧
    (restrictedConstantFamilySpecialization k' Λ Y
      ((constantSpecialFibreProj k' Y) ⁻¹ᵁ U)).isoLocus L

/-- Two dense opens of `Y` meet in a dense open whose inverse image in `Y ⊗ k'` is contained in
both inverse images. -/
lemma genericallyIsoSpecialization_of_two (Y : Over (Spec (.of k)))
    {L₁ L₂ L₃ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))}
    (h : ∀ W : (deformationSpecialFibre Y ⊥ k').left.Opens,
      (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus L₁ →
      (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus L₂ →
      (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus L₃)
    (h₁ : genericallyIsoSpecialization k' Λ Y L₁) (h₂ : genericallyIsoSpecialization k' Λ Y L₂) :
    genericallyIsoSpecialization k' Λ Y L₃ := by
  obtain ⟨U₁, hU₁, hL₁⟩ := h₁
  obtain ⟨U₂, hU₂, hL₂⟩ := h₂
  refine ⟨U₁ ⊓ U₂, hU₁.inter_of_isOpen_left hU₂ U₁.isOpen, h _ ?_ ?_⟩
  · exact isoLocus_restrictedConstantFamilySpecialization_mono k' Λ Y
      (Hom.preimage_mono _ inf_le_left) hL₁
  · exact isoLocus_restrictedConstantFamilySpecialization_mono k' Λ Y
      (Hom.preimage_mono _ inf_le_right) hL₂

instance (Y : Over (Spec (.of k))) :
    (genericallyIsoSpecialization k' Λ Y).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨U, hU, hL⟩ ↦
    ⟨U, hU, (restrictedConstantFamilySpecialization k' Λ Y _).isoLocus.prop_of_iso e hL⟩

instance (Y : Over (Spec (.of k))) :
    (genericallyIsoSpecialization k' Λ Y).IsStableUnderRetracts where
  of_retract r := fun ⟨U, hU, hL⟩ ↦
    ⟨U, hU, (restrictedConstantFamilySpecialization k' Λ Y _).isoLocus.prop_of_retract r hL⟩

/-- **The complexes with generically invertible specialization map form a triangulated
subcategory.** -/
instance isTriangulated_genericallyIsoSpecialization (Y : Over (Spec (.of k))) :
    (genericallyIsoSpecialization k' Λ Y).IsTriangulated where
  exists_zero := by
    obtain ⟨Z, hZ, hQ⟩ :=
      (restrictedConstantFamilySpecialization k' Λ Y ⊤).isoLocus.exists_prop_of_containsZero
    exact ⟨Z, hZ, ⊤, dense_univ,
      isoLocus_restrictedConstantFamilySpecialization_mono k' Λ Y le_top hQ⟩
  isStableUnderShiftBy n :=
    { le_shift L hL := by
        rw [ObjectProperty.prop_shift_iff]
        exact genericallyIsoSpecialization_of_two k' Λ Y (L₁ := L) (L₂ := L)
          (fun W h _ ↦ (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus.le_shift n _ h)
          hL hL }
  toIsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ ↦
    genericallyIsoSpecialization_of_two k' Λ Y
      (fun W h₁' h₃' ↦ (restrictedConstantFamilySpecialization k' Λ Y W).isoLocus
        |>.ext_of_isTriangulatedClosed₂ T hT h₁' h₃') h₁ h₃

/-- A complex whose pullback along an open immersion `g : V ⟶ Y` has invertible specialization map
has generically invertible specialization map if the image of `g` is dense. -/
lemma genericallyIsoSpecialization_of_isIso_upperStar {Y V : Over (Spec (.of k))} (g : V ⟶ Y)
    [IsOpenImmersion g.left] (hg : Dense (Set.range g.left.base))
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))}
    (h : IsIso (L(((deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥)
      k').left)^*⟦Λ⟧).map ((constantFamilySpecialization k' Λ Y).app L))) :
    genericallyIsoSpecialization k' Λ Y L := by
  have : IsOpenImmersion (deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥)
      k').left :=
    isOpenImmersion_deformationSpecialFibreMap_of_isOpenImmersion _ _ k'
      (IdealSheafData.comap_bot _).symm
  refine ⟨g.left.opensRange, hg,
    (isoLocus_restrictedConstantFamilySpecialization_iff k' Λ Y _ L).2 ?_⟩
  have := h
  refine isIso_leftDerivedUpperStar_ι_map_of_subset_range Λ
    (deformationSpecialFibreMap g (siteIdeal_bot_map_appLE_le g.left ⊥) k').left _ _ ?_
  rw [Scheme.range_snd_of_isPullback (isPullback_deformationSpecialFibreMap_bot k' g
    (siteIdeal_bot_map_appLE_le g.left ⊥)).flip]
  exact fun _ hx ↦ hx

/-- At a zero object, the specialization map of a constant family is an isomorphism. -/
lemma isIso_constantFamilySpecialization_app_of_isZero (Y : Over (Spec (.of k)))
    {L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left))} (hL : IsZero L) :
    IsIso ((constantFamilySpecialization k' Λ Y).app L) := by
  have h₁ := Functor.map_isZero L((constantSpecialFibreProj k' Y)^*⟦Λ⟧) hL
  have h₂ := (deformationModel Y ⊥ k').isZero_nearbyCycles_obj Λ hL
  rw [h₁.eq_of_src ((constantFamilySpecialization k' Λ Y).app L) 0,
    isIsoZero_iff_source_target_isZero]
  exact ⟨h₁, h₂⟩

variable {ℓ : ℕ} [Fact ℓ.Prime] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **Generic invertibility for a lisse generator.** -/
theorem genericallyIsoSpecialization_of_lisseGenerator [Smooth Y.hom] [IrreducibleSpace Y.left]
    [IsReduced Y.left] (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hN : lisseGenerator ℓ Y N) :
    genericallyIsoSpecialization k' (Profinite.padicAlgClRingObj ℓ) Y N.obj := by
  obtain ⟨Z, _, _, _, g, _, U, _, _, _, _, j, _, L, hL, ⟨e⟩⟩ := hN
  let N' := (boundedConstructibleLowerStar ℓ g).obj
    ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L)
  let e' : N ≅ N' := e ≪≫ (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ g).app _ ≪≫
    (boundedConstructibleLowerStar ℓ g).mapIso
      ((boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ j).app L)
  refine ObjectProperty.prop_of_iso _ ((boundedConstructible _).ι.mapIso e'.symm) ?_
  have hYne : Nonempty Y.left := inferInstance
  by_cases hg : Set.range g.left.base = Set.univ
  · -- `g` is an isomorphism, and `h = j ≫ g` an open immersion
    have : Surjective g.left := ⟨Set.range_eq_univ.1 hg⟩
    have : IsIso g.left := isIso_of_isClosedImmersion_of_surjective g.left
    by_cases hU : IsEmpty U.left
    · have hN' : IsZero N'.obj := (boundedConstructible _).ι.map_isZero
        ((boundedConstructibleLowerStar ℓ g).map_isZero
          ((boundedConstructibleOpenImmersionLowerShriek _ ℓ j).map_isZero
            (isZero_boundedConstructible_of_isEmpty ℓ L)))
      have : IsIso ((constantFamilySpecialization k' _ Y).app
          ((boundedConstructible _).ι.obj N')) :=
        isIso_constantFamilySpecialization_app_of_isZero k' _ Y hN'
      exact ⟨⊤, dense_univ,
        (isoLocus_restrictedConstantFamilySpecialization_iff k' _ Y _ _).2 inferInstance⟩
    rw [not_isEmpty_iff] at hU
    let h : U ⟶ Y := j ≫ g
    have : IsOpenImmersion h.left := inferInstanceAs (IsOpenImmersion (j.left ≫ g.left))
    have : Smooth U.hom := by
      rw [← Over.w h]
      infer_instance
    -- `Lh^* N' ≅ L` is dualizable
    let e₁ : (L((h.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj N'.obj ≅ L.obj :=
      (leftDerivedUpperStarComp _ j.left g.left).app N'.obj ≪≫
        (L((j.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).mapIso
          (asIso ((derivedUpperStarLowerStarAdjunction _ g.left).counit.app _)) ≪≫
        (boundedConstructible _).ι.mapIso (asIso
          ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j).unit.app L)).symm
    have hd : IsDualizable ((L((h.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj N'.obj) :=
      IsDualizable.of_iso e₁.symm ((isDualizable_iff_isDualizable_obj ℓ L).1 hL)
    have := isIso_deformationModel_bot_unit_of_smooth (ℓ := ℓ) U k'
    have hσ : IsIso ((constantFamilySpecialization k' _ U).app
        ((L((h.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj N'.obj)) :=
      (deformationModel U ⊥ k').isIso_specialization_app_of_isDualizable _ _ _ _ hd
    rw [isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth k' h N'] at hσ
    refine genericallyIsoSpecialization_of_isIso_upperStar k' _ h ?_ hσ
    obtain ⟨x⟩ := hU
    exact h.left.isOpenMap.isOpen_range.dense ⟨_, x, rfl⟩
  · -- `N` vanishes on the complement `W` of the image of `g`
    let W : Y.left.Opens := ⟨(Set.range g.left.base)ᶜ,
      g.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hW : (W : Set Y.left).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact hg (compl_eq_bot.1 h)
    let w := overRestrictι Y W
    have hwg : Disjoint (Set.range w.left.base) (Set.range g.left.base) := by
      rw [range_overRestrictι]
      exact disjoint_compl_left
    have hz := isZero_boundedConstructibleUpperStar_obj_lowerStar_obj ℓ w g hwg
      ((boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j).obj L)
    have hz' : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ w).obj
        N').obj :=
      (boundedConstructible _).ι.map_isZero hz
    have h := isIso_constantFamilySpecialization_app_of_isZero k' _ (overRestrict Y W) hz'
    rw [show ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ w).obj N').obj =
      L((w.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj N'.obj from rfl,
      isIso_constantFamilySpecialization_app_upperStar_iff_of_smooth k' w N'] at h
    refine genericallyIsoSpecialization_of_isIso_upperStar k' _ w ?_ h
    rw [range_overRestrictι]
    exact W.isOpen.dense hW

/-- **Generic invertibility of the specialization map of a constant family**: for `Y` smooth,
irreducible and reduced, and `L` bounded constructible on `Y`, the specialization map
`σ_Y(L) : Lπ_Y^* L ⟶ Ψ_{Y × S}(L)` is an isomorphism over the inverse image in `Y ⊗ k'` of a dense
open `U ⊆ Y`. -/
theorem exists_dense_isIso_constantFamilySpecialization [Smooth Y.hom] [IrreducibleSpace Y.left]
    [IsReduced Y.left] (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ∃ U : Y.left.Opens, Dense (U : Set Y.left) ∧
      IsIso ((L((((constantSpecialFibreProj k' Y) ⁻¹ᵁ U).ι)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).map
        ((constantFamilySpecialization k' (Profinite.padicAlgClRingObj ℓ) Y).app L.obj)) := by
  let Q := (genericallyIsoSpecialization k' (Profinite.padicAlgClRingObj ℓ) Y).inverseImage
    (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left)).ι
  have : Q.IsStableUnderRetracts :=
    ⟨fun r hB ↦ (genericallyIsoSpecialization k' _ Y).prop_of_retract
      (r.map (boundedConstructible _).ι) hB⟩
  exact (ObjectProperty.triangEnvelope_le_iff (Q := Q) _).mpr
    (fun N hN ↦ genericallyIsoSpecialization_of_lisseGenerator k' Y N hN) _
    (triangEnvelope_lisseGenerator ℓ Y L)

end AlgebraicGeometry.ProEtale.CondensedRing
