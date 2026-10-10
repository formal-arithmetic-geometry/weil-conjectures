/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.GlobalSections

/-!
# Coherence of the composition isomorphisms of pro-étale pushforwards and pullbacks

The pushforwards `g_*` and pullbacks `g^*` of sheaves on small pro-étale sites form
pseudofunctors up to the composition isomorphisms `ProEtale.lowerStarComp` and
`ProEtale.upperStarComp`. This file proves the coherence laws needed to compare composites of
these isomorphisms, together with their compatibility with the identifications
`(e.hom)^* ≅ (e.inv)_*` for an isomorphism `e` and with global sections.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarComp_assoc` and
  `AlgebraicGeometry.ProEtale.upperStarComp_assoc`: the associativity laws.
- `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv_trans`: the identification
  `(e.hom)^* ≅ (e.inv)_*` is compatible with composition of isomorphisms.
- `AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso_comp_hom_app` and
  `AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso_trans_hom_app`: the identifications
  of global sections of pushforwards and of pullbacks along isomorphisms are compatible with
  composition.

All proofs on pushforwards are computations of restriction maps along the pasting
isomorphisms of base change; those on pullbacks pass to the conjugate isomorphisms of the
right adjoints.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace ProEtale

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for the composition isomorphisms of pushforwards: the two ways of
identifying `f_* ⋙ g_* ⋙ h_*` with `(f ≫ g ≫ h)_*` agree. -/
lemma lowerStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h =
      (f)_*[A].associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) ≪≫
          lowerStarCongr A (Category.assoc f g h).symm := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStar_map_hom_app']
  change _ = M.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map _).op ≫ _
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr]
    · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr]

/-- The composition isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (upperStarComp A h₁ h₂) = lowerStarComp A h₁ h₂ := by
  rw [upperStarComp, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply, Iso.symm_symm_eq]

/-- The congruence isomorphism of pullbacks is conjugate to that of pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A g') (upperStarLowerStarAdjunction A g)
      (upperStarCongr A h) = lowerStarCongr A h.symm := by
  subst h
  ext : 1
  simp [upperStarCongr, lowerStarCongr]

/-- The associativity law for the composition isomorphisms of pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_assoc` by passing to conjugates. -/
lemma upperStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    upperStarComp A (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (h)^*[A] (upperStarComp A f g) =
      upperStarCongr A (Category.assoc f g h) ≪≫ upperStarComp A f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (upperStarComp A g h) (f)^*[A] ≪≫
          ((h)^*[A]).associator (g)^*[A] (f)^*[A] := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A h).comp
    ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f)))
    (upperStarLowerStarAdjunction A ((f ≫ g) ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A (f ≫ g))) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A (f ≫ g ≫ h)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A (g ≫ h)).comp
      (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A g)).comp (upperStarLowerStarAdjunction A f)) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_upperStarCongr]
  simpa only [Iso.trans_assoc] using lowerStarComp_assoc A f g h

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction maps of a pushforward are those of the sheaf along base change. -/
@[simp]
lemma lowerStar_obj_obj_map {Z Y : Scheme.{u}} (g : Z ⟶ Y) (G : Sheaf (ProEt.topology Z) A)
    {V W : Y.ProEtᵒᵖ} (f : V ⟶ W) :
    ((g)_*[A].obj G).obj.map f =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f.unop).op :=
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The left unit law for the composition isomorphisms of pushforwards. -/
lemma lowerStarComp_id_left {S R : Scheme.{u}} (h : S ⟶ R) :
    lowerStarComp A (𝟙 S) h = Functor.isoWhiskerRight (lowerStarId A S) (h)_*[A] ≪≫
      (h)_*[A].leftUnitor ≪≫ lowerStarCongr A (Category.id_comp h).symm := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp_hom_app_hom_app,
    lowerStarCongr_hom_app_hom_app, lowerStar_map_hom_app']
  simp only [lowerStarId, Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
  erw [Category.id_comp (M.obj.map ((MorphismProperty.Over.pullbackCongr _).inv.app (unop b)).op)]
  rw [← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
        MorphismProperty.Over.pullbackId]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The right unit law for the composition isomorphisms of pushforwards. -/
lemma lowerStarComp_id_right {T S : Scheme.{u}} (h : T ⟶ S) :
    lowerStarComp A h (𝟙 S) = Functor.isoWhiskerLeft (h)_*[A] (lowerStarId A S) ≪≫
      (h)_*[A].rightUnitor ≪≫ lowerStarCongr A (Category.comp_id h).symm := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp_hom_app_hom_app,
    lowerStarCongr_hom_app_hom_app]
  simp only [lowerStarId, Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
  rw [lowerStar_obj_obj_map]
  erw [Category.id_comp (M.obj.map ((MorphismProperty.Over.pullbackCongr _).inv.app (unop b)).op)]
  rw [← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
      MorphismProperty.Over.pullbackId] <;>
    simpa using (pullback.condition (f := (unop b).hom) (g := h ≫ 𝟙 S)).symm
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The unit of `lowerStarEquivalence e` is the composite of identity, congruence and
composition isomorphisms it is built from: that composite already satisfies the triangle
identity, so adjointification does not change it. -/
lemma lowerStarEquivalence_unitIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (lowerStarEquivalence A e).unitIso = (lowerStarId A X).symm ≪≫
      lowerStarCongr A e.hom_inv_id.symm ≪≫ (lowerStarComp A e.hom e.inv).symm :=
  Equivalence.adjointifyη_eq _ _ (lowerStar_map_unit_comp_counit A e)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The counit of `lowerStarEquivalence e`. -/
lemma lowerStarEquivalence_counitIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (lowerStarEquivalence A e).counitIso = lowerStarComp A e.inv e.hom ≪≫
      lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y :=
  rfl

/-- The adjunction `(e.inv)_* ⊣ (e.hom)_*` of the equivalence `lowerStarEquivalence e`. -/
noncomputable def lowerStarInvAdjunction {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.inv)_*[A] ⊣ (e.hom)_*[A] :=
  (lowerStarEquivalence A e).symm.toAdjunction

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism of pushforwards along the inverses of isomorphisms
`e₁ : X ≅ Y` and `e₂ : Y ≅ Z` is conjugate to the inverse of the composition isomorphism of
pushforwards along `e₁` and `e₂`. -/
lemma conjugateIsoEquiv_lowerStarComp_inv {X Y Z : Scheme.{u}} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) :
    conjugateIsoEquiv (lowerStarInvAdjunction A (e₁ ≪≫ e₂))
      ((lowerStarInvAdjunction A e₂).comp (lowerStarInvAdjunction A e₁))
      (lowerStarComp A e₂.inv e₁.inv) = (lowerStarComp A e₁.hom e₂.hom).symm := by
  ext M b
  simp only [lowerStarInvAdjunction, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    Adjunction.comp_unit_app,
    Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit, Equivalence.symm_unit,
    Equivalence.symm_counit, Equivalence.unitInv, Equivalence.counitInv,
    Equivalence.symm_inverse, Equivalence.symm_functor,
    lowerStarEquivalence_unitIso, lowerStarEquivalence_counitIso, lowerStarEquivalence_functor,
    lowerStarEquivalence_inverse, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.comp_map, Functor.map_comp,
    ObjectProperty.FullSubcategory.comp_hom, lowerStarComp_hom_app_hom_app,
    lowerStarComp_inv_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStar_map_hom_app']
  simp only [lowerStarId, lowerStarCongr_eq,
    Functor.sheafPushforwardContinuousId'_hom_app_hom_app,
    Functor.sheafPushforwardContinuousId'_inv_app_hom_app,
    Functor.sheafPushforwardContinuousIso_inv, Functor.sheafPushforwardContinuousNatTrans_app_hom,
    Functor.whiskerRight_app, NatTrans.op_app, Functor.sheafPushforwardContinuous_obj_obj_map,
    Quiver.Hom.unop_op, Category.assoc]
  simp only [Functor.comp_obj, lowerStar_obj_obj_map, Quiver.Hom.op_unop, Quiver.Hom.unop_op]
  change M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ ≫
    M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ ≫ M.obj.map _ = _
  rw [← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp,
    ← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp, ← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr] <;>
    exact Category.id_comp _

/-- The identification `(e.hom)^* ≅ (e.inv)_*` is conjugate to the identity of `(e.hom)_*`. -/
lemma conjugateIsoEquiv_upperStarIsoLowerStarInv {X Y : Scheme.{u}} (e : X ≅ Y) :
    conjugateIsoEquiv (lowerStarInvAdjunction A e)
      (upperStarLowerStarAdjunction A e.hom) (upperStarIsoLowerStarInv A e) = Iso.refl _ := by
  change (conjugateIsoEquiv (upperStarLowerStarAdjunction A e.hom)
    (lowerStarEquivalence A e).symm.toAdjunction
    ((conjugateIsoEquiv _ _).symm (Iso.refl _))).symm = _
  exact congrArg Iso.symm (Equiv.apply_symm_apply _ (Iso.refl _))

/-- The identification `(e.hom)^* ≅ (e.inv)_*` of the pullback along an isomorphism with the
pushforward along its inverse is compatible with composition:
`(e₁ ≫ e₂)^* ≅ e₂^* ⋙ e₁^* ≅ (e₂⁻¹)_* ⋙ e₁^* ≅ (e₂⁻¹)_* ⋙ (e₁⁻¹)_* ≅ (e₂⁻¹ ≫ e₁⁻¹)_*`. -/
lemma upperStarIsoLowerStarInv_trans {X Y Z : Scheme.{u}} (e₁ : X ≅ Y) (e₂ : Y ≅ Z) :
    upperStarIsoLowerStarInv A (e₁ ≪≫ e₂) = upperStarComp A e₁.hom e₂.hom ≪≫
      Functor.isoWhiskerRight (upperStarIsoLowerStarInv A e₂) (e₁.hom)^*[A] ≪≫
      Functor.isoWhiskerLeft (e₂.inv)_*[A] (upperStarIsoLowerStarInv A e₁) ≪≫
      lowerStarComp A e₂.inv e₁.inv := by
  refine (conjugateIsoEquiv (lowerStarInvAdjunction A (e₁ ≪≫ e₂))
    (upperStarLowerStarAdjunction A (e₁.hom ≫ e₂.hom))).injective
    ((conjugateIsoEquiv_upperStarIsoLowerStarInv A (e₁ ≪≫ e₂)).trans ?_)
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A e₂.hom).comp
      (upperStarLowerStarAdjunction A e₁.hom)) _,
    conjugateIsoEquiv_trans _ ((lowerStarInvAdjunction A e₂).comp
      (upperStarLowerStarAdjunction A e₁.hom)) _,
    conjugateIsoEquiv_trans _ ((lowerStarInvAdjunction A e₂).comp
      (lowerStarInvAdjunction A e₁)) _]
  rw [conjugateIsoEquiv_lowerStarComp_inv, conjugateIsoEquiv_isoWhiskerLeft,
    conjugateIsoEquiv_upperStarIsoLowerStarInv, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_upperStarIsoLowerStarInv, conjugateIsoEquiv_upperStarComp]
  ext : 2
  simp

/-- The identification `Γ(R, (g₁ ≫ g₂)_* H) ≅ Γ(T, H)` is the composite of the
identifications for `g₂` and for `g₁`. -/
lemma globalSectionsLowerStarIso_comp_hom_app {R S T : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (H : Sheaf (ProEt.topology T) A) :
    (globalSectionsLowerStarIso A (g₁ ≫ g₂)).hom.app H =
      (Sheaf.Γ _ A).map ((lowerStarComp A g₁ g₂).inv.app H) ≫
        (globalSectionsLowerStarIso A g₂).hom.app ((g₁)_*[A].obj H) ≫
          (globalSectionsLowerStarIso A g₁).hom.app H := by
  simp only [globalSectionsLowerStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Iso.symm_hom, Functor.mapIso_inv, Category.id_comp, Category.assoc]
  rw [Iso.inv_hom_id_app_assoc]
  erw [(Sheaf.ΓNatIsoSheafSections (ProEt.topology R) A
    (ProEt.isTerminalMkId R)).hom.naturality_assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  dsimp only [Functor.flip_obj_map, Functor.flip_map_app]
  erw [lowerStarComp_inv_app_hom_app, lowerStar_obj_obj_map, ← H.obj.map_comp]
  erw [← H.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact ((ProEt.isTerminalMkId T).ofIso (overPullbackObjMkIdIso (g₁ ≫ g₂)).symm).hom_ext _ _

/-- The identification `Γ(Z₁, (e₁ ≫ e₂)^* H) ≅ Γ(Z₃, H)` is the composite of the
identifications for `e₁` and for `e₂`. -/
lemma globalSectionsUpperStarIso_trans_hom_app {Z₁ Z₂ Z₃ : Scheme.{u}} (e₁ : Z₁ ≅ Z₂)
    (e₂ : Z₂ ≅ Z₃) (H : Sheaf (ProEt.topology Z₃) A) :
    (globalSectionsUpperStarIso A (e₁ ≪≫ e₂)).hom.app H =
      (Sheaf.Γ _ A).map ((upperStarComp A e₁.hom e₂.hom).hom.app H) ≫
        (globalSectionsUpperStarIso A e₁).hom.app ((e₂.hom)^*[A].obj H) ≫
          (globalSectionsUpperStarIso A e₂).hom.app H := by
  simp only [globalSectionsUpperStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, upperStarIsoLowerStarInv_trans,
    Iso.trans_inv, globalSectionsLowerStarIso_comp_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  congr 1
  rw [← Functor.map_comp_assoc, (upperStarIsoLowerStarInv A e₁).hom.naturality,
    Functor.map_comp_assoc, ← Functor.map_comp_assoc _ ((lowerStarComp A _ _).hom.app H),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  congr 1
  exact (globalSectionsLowerStarIso A e₁.inv).hom.naturality_assoc _ _

end ProEtale

end AlgebraicGeometry
