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

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The right unit law for the composition isomorphisms of pushforwards, at a component and
with `𝟙` replaced by a morphism `g₀` equal to it. -/
lemma lowerStarComp_inv_app_comp_lowerStarId_hom_app {T S : Scheme.{u}} (a : T ⟶ S)
    (g₀ : S ⟶ S) (hg₀ : g₀ = 𝟙 S) {M : Sheaf (Scheme.ProEt.topology T) A}
    {N : Sheaf (Scheme.ProEt.topology S) A} (f : (a)_*[A].obj M ⟶ N) :
    (lowerStarComp A a g₀).inv.app M ≫ (g₀)_*[A].map f ≫ eqToHom (by rw [hg₀]) ≫
      (lowerStarId A S).hom.app N = eqToHom (by rw [hg₀, Category.comp_id]) ≫ f := by
  subst hg₀
  rw [lowerStarComp_id_right]
  simp [lowerStarCongr]
  exact Category.id_comp f

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- Naturality of the inverse of the composition isomorphism of pushforwards `(c ≫ g)_* ≅
c_* ⋙ g_*`, for a morphism `d` equal to `c ≫ g`. -/
@[reassoc]
lemma lowerStar_map_eqToHom_lowerStarComp_inv_app {T S R : Scheme.{u}} (c : T ⟶ S) (g : S ⟶ R)
    (d : T ⟶ R) (hd : d = c ≫ g) {P Q : Sheaf (Scheme.ProEt.topology T) A} (f : P ⟶ Q) :
    (d)_*[A].map f ≫ eqToHom (by rw [hd]) ≫ (lowerStarComp A c g).inv.app Q =
      eqToHom (by rw [hd]) ≫ (lowerStarComp A c g).inv.app P ≫ (g)_*[A].map ((c)_*[A].map f) := by
  subst hd
  simp

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for the inverses of the composition isomorphisms of pushforwards, at a
component and for morphisms `b`, `d`, `e` equal to the composites `a ≫ c`, `c ≫ g`, `b ≫ g`. -/
@[reassoc]
lemma eqToHom_lowerStarComp_inv_app_assoc {T S R Q : Scheme.{u}} (a : T ⟶ S) (c : S ⟶ R)
    (g : R ⟶ Q) (b : T ⟶ R) (hb : b = a ≫ c) (d : S ⟶ Q) (hd : d = c ≫ g) (e : T ⟶ Q)
    (he : e = b ≫ g) (M : Sheaf (Scheme.ProEt.topology T) A) :
    eqToHom (show (e)_*[A].obj M = (b ≫ g)_*[A].obj M by rw [he]) ≫
      (lowerStarComp A b g).inv.app M ≫
        (g)_*[A].map (eqToHom (by rw [hb])) ≫ (g)_*[A].map ((lowerStarComp A a c).inv.app M) =
      eqToHom (show (e)_*[A].obj M = (a ≫ d)_*[A].obj M by rw [he, hb, hd, Category.assoc]) ≫
        (lowerStarComp A a d).inv.app M ≫
        eqToHom (show (d)_*[A].obj ((a)_*[A].obj M) = (c ≫ g)_*[A].obj ((a)_*[A].obj M) by
          rw [hd]) ≫ (lowerStarComp A c g).inv.app ((a)_*[A].obj M) := by
  subst hb hd he
  have := congrArg (fun e ↦ e.inv.app M) (lowerStarComp_assoc A a c g)
  simp [lowerStarCongr] at this
  simp
  exact this

/-- Pulling back along `s` the composite `E^* M ≅ (E⁻¹)_* M ⟶ M` of a map `ψ`, for
`E = e₂ ≫ e₁` and `ψ` the composite of `ψ₁` and `ψ₂`, is the composite of the pullbacks along
`s ≫ e₂` of `ψ₁` and along `s` of `ψ₂`. -/
lemma upperStarComp_hom_app_map_comp_of_eq {P Y : Scheme.{u}} (s : P ⟶ Y) (e₁ e₂ E : Y ≅ Y)
    (hE : E = e₂ ≪≫ e₁) (M : Sheaf (Scheme.ProEt.topology Y) A)
    (ψ₁ : (e₁.inv)_*[A].obj M ⟶ M) (ψ₂ : (e₂.inv)_*[A].obj M ⟶ M) (ψ : (E.inv)_*[A].obj M ⟶ M)
    (hψ : ψ = eqToHom (by rw [hE]; rfl) ≫ (lowerStarComp A e₁.inv e₂.inv).inv.app M ≫
      (e₂.inv)_*[A].map ψ₁ ≫ ψ₂) :
    (upperStarComp A s E.hom).hom.app M ≫
        (s)^*[A].map ((upperStarIsoLowerStarInv A E).hom.app M ≫ ψ) =
      eqToHom (by rw [hE]; rfl) ≫ (upperStarComp A (s ≫ e₂.hom) e₁.hom).hom.app M ≫
        (s ≫ e₂.hom)^*[A].map ((upperStarIsoLowerStarInv A e₁).hom.app M ≫ ψ₁) ≫
        (upperStarComp A s e₂.hom).hom.app M ≫
        (s)^*[A].map ((upperStarIsoLowerStarInv A e₂).hom.app M ≫ ψ₂) := by
  subst hE hψ
  have h₁ := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc A s e₂.hom e₁.hom)
  have h₂ := congrArg (fun e ↦ e.hom.app M) (upperStarIsoLowerStarInv_trans A e₂ e₁)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, upperStarCongr, eqToIso.hom, eqToHom_app, Category.comp_id] at h₁
  simp [upperStarCongr] at h₂
  rw [h₂, (upperStarComp A s e₂.hom).hom.naturality_assoc, reassoc_of% h₁]
  simp only [Functor.comp_map, ← Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [(upperStarIsoLowerStarInv A e₂).hom.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- `AlgebraicGeometry.ProEtale.globalSectionsUpperStarIso_trans_hom_app` for an isomorphism
`E` equal to `e₂ ≪≫ e₁`. -/
lemma globalSectionsUpperStarIso_hom_app_of_eq {P : Scheme.{u}} (e₁ e₂ E : P ≅ P)
    (hE : E = e₂ ≪≫ e₁) (H : Sheaf (Scheme.ProEt.topology P) A) :
    (globalSectionsUpperStarIso A E).hom.app H =
      (Sheaf.Γ _ A).map (eqToHom (by rw [hE]; rfl) ≫ (upperStarComp A e₂.hom e₁.hom).hom.app H) ≫
        (globalSectionsUpperStarIso A e₂).hom.app ((e₁.hom)^*[A].obj H) ≫
        (globalSectionsUpperStarIso A e₁).hom.app H := by
  subst hE
  rw [globalSectionsUpperStarIso_trans_hom_app, eqToHom_refl, Category.id_comp]

/-- The composition isomorphism of pullbacks along equal morphisms. -/
lemma upperStarComp_hom_app_congr {P Q Y : Scheme.{u}} (f f' : P ⟶ Q) (hf : f = f') (t : Q ⟶ Y)
    (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A f t).hom.app M = eqToHom (by rw [hf]) ≫ (upperStarComp A f' t).hom.app M ≫
      eqToHom (by rw [hf]) := by
  subst hf
  simp

/-- The identification `Γ((E ≫ t)^* M) ≅ Γ(t^* M)` for an automorphism `E = e₂ ≪≫ e₁` is the
composite of those for `e₂` and for `e₁`. -/
lemma globalSections_map_upperStarComp_comp_globalSectionsUpperStarIso_of_eq {P Y : Scheme.{u}}
    (t : P ⟶ Y) (e₁ e₂ E : P ≅ P) (hE : E = e₂ ≪≫ e₁) (M : Sheaf (Scheme.ProEt.topology Y) A) :
    (Sheaf.Γ _ A).map ((upperStarComp A E.hom t).hom.app M) ≫
        (globalSectionsUpperStarIso A E).hom.app ((t)^*[A].obj M) =
      eqToHom (by rw [hE, Iso.trans_hom, Category.assoc]) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A e₂.hom (e₁.hom ≫ t)).hom.app M) ≫
        (globalSectionsUpperStarIso A e₂).hom.app ((e₁.hom ≫ t)^*[A].obj M) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A e₁.hom t).hom.app M) ≫
        (globalSectionsUpperStarIso A e₁).hom.app ((t)^*[A].obj M) := by
  have h := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc A e₂.hom e₁.hom t)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, upperStarCongr, eqToIso.hom, eqToHom_app, Category.comp_id] at h
  have hn := (globalSectionsUpperStarIso A e₂).hom.naturality
    (X := (e₁.hom ≫ t)^*[A].obj M) (Y := (e₁.hom)^*[A].obj ((t)^*[A].obj M))
    ((upperStarComp A e₁.hom t).hom.app M)
  simp only [Functor.comp_map] at hn
  rw [globalSectionsUpperStarIso_hom_app_of_eq A e₁ e₂ E hE,
    upperStarComp_hom_app_congr A E.hom (e₂.hom ≫ e₁.hom) (by rw [hE]; rfl)]
  simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [← Functor.map_comp_assoc, h]
  simp only [Functor.map_comp, Category.assoc, eqToHom_map, eqToHom_trans_assoc]
  congr 2
  exact (reassoc_of% hn) _

/-- The identification `Γ((e ≫ t)^* M) ≅ Γ(t^* M)` along an automorphism `e` commutes with the
map `Γ((t ≫ g)^* M) ⟶ Γ(t^* M)` induced by a map `χ : g^* M ⟶ M`. -/
lemma globalSections_map_upperStarComp_comm {P Y : Scheme.{u}} (t : P ⟶ Y) (e : P ≅ P)
    (g : Y ⟶ Y) (M : Sheaf (Scheme.ProEt.topology Y) A) (χ : (g)^*[A].obj M ⟶ M) :
    (Sheaf.Γ _ A).map ((upperStarComp A e.hom (t ≫ g)).hom.app M) ≫
        (globalSectionsUpperStarIso A e).hom.app ((t ≫ g)^*[A].obj M) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A t g).hom.app M ≫ (t)^*[A].map χ) =
      eqToHom (by rw [Category.assoc]) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A (e.hom ≫ t) g).hom.app M ≫ (e.hom ≫ t)^*[A].map χ) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A e.hom t).hom.app M) ≫
        (globalSectionsUpperStarIso A e).hom.app ((t)^*[A].obj M) := by
  have h := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc A e.hom t g)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, upperStarCongr, eqToIso.hom, eqToHom_app, Category.comp_id] at h
  have hn := (globalSectionsUpperStarIso A e).hom.naturality
    ((upperStarComp A t g).hom.app M ≫ (t)^*[A].map χ)
  simp only [Functor.comp_map] at hn
  have key : ((upperStarComp A (e.hom ≫ t) g).hom.app M ≫ (e.hom ≫ t)^*[A].map χ) ≫
      (upperStarComp A e.hom t).hom.app M = eqToHom (by rw [Category.assoc]) ≫
        (upperStarComp A e.hom (t ≫ g)).hom.app M ≫
          (e.hom)^*[A].map ((upperStarComp A t g).hom.app M ≫ (t)^*[A].map χ) := by
    rw [Category.assoc ((upperStarComp A (e.hom ≫ t) g).hom.app M),
      (upperStarComp A e.hom t).hom.naturality, reassoc_of% h]
    simp
  rw [← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, key]
  simp [eqToHom_map]

end ProEtale

end AlgebraicGeometry
