/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# Coherence of the composition isomorphisms of pro-étale pushforwards and pullbacks

The composition isomorphisms `ProEtale.lowerStarComp` and `ProEtale.upperStarComp` satisfy the
associativity law of a pseudofunctor. For pushforwards this is the associativity of the pullback
pasting isomorphisms on the sites; it is transported to pullbacks by conjugation along the
adjunctions `g^* ⊣ g_*`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarComp_assoc` and
  `AlgebraicGeometry.ProEtale.upperStarComp_assoc`: the associativity laws.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for `ProEtale.lowerStarComp`. -/
lemma lowerStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
        lowerStarCongr A (Category.assoc f g h) =
      ((f)_*[A]).associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) := by
  ext M W
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app,
    lowerStar_map_hom_app']
  simp only [lowerStar, Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    ← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]

/-- Under conjugation, the composition isomorphism of pullbacks corresponds to the composition
isomorphism of pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (upperStarComp A h₁ h₂) = lowerStarComp A h₁ h₂ := by
  ext : 1
  exact conjugateEquiv_upperStarComp_hom A h₁ h₂

/-- Under conjugation, the congruence isomorphism of pullbacks corresponds to the congruence
isomorphism of pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g') :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A g) (upperStarLowerStarAdjunction A g')
      (upperStarCongr A h).symm = lowerStarCongr A h := by
  ext : 1
  exact conjugateEquiv_upperStarCongr_inv A h

/-- The associativity law for `ProEtale.upperStarComp`, obtained from
`ProEtale.lowerStarComp_assoc` by conjugation. -/
lemma upperStarComp_assoc {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V) :
    upperStarComp A f (g ≫ h) ≪≫ Functor.isoWhiskerRight (upperStarComp A g h) (f)^*[A] ≪≫
        ((h)^*[A]).associator (g)^*[A] (f)^*[A] =
      (upperStarCongr A (Category.assoc f g h)).symm ≪≫ upperStarComp A (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (h)^*[A] (upperStarComp A f g) := by
  refine (conjugateIsoEquiv ((upperStarLowerStarAdjunction A h).comp
    ((upperStarLowerStarAdjunction A g).comp (upperStarLowerStarAdjunction A f)))
    (upperStarLowerStarAdjunction A (f ≫ g ≫ h))).injective ?_
  rw [conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A (g ≫ h)).comp
      (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A g)).comp (upperStarLowerStarAdjunction A f)) _,
    conjugateIsoEquiv_trans _ (upperStarLowerStarAdjunction A ((f ≫ g) ≫ h)) _,
    conjugateIsoEquiv_trans _ ((upperStarLowerStarAdjunction A h).comp
      (upperStarLowerStarAdjunction A (f ≫ g))) _]
  simp only [conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator, conjugateIsoEquiv_upperStarCongr,
    Iso.trans_assoc]
  exact (lowerStarComp_assoc A f g h).symm

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarId_hom_app_hom_app (X : Scheme.{u}) (M : Sheaf (ProEt.topology X) A)
    (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).hom.app M).hom.app V =
      M.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).inv.app V.unop).op := by
  simp [lowerStarId, Functor.sheafPushforwardContinuousId']
  exact Category.comp_id _

section

variable {C D : Type*} [Category* C] [Category* D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarId_inv_app_hom_app (X : Scheme.{u}) (M : Sheaf (ProEt.topology X) A)
    (V : X.ProEtᵒᵖ) :
    ((lowerStarId A X).inv.app M).hom.app V =
      M.obj.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app V.unop).op := by
  simp [lowerStarId, Functor.sheafPushforwardContinuousId']

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
lemma lowerStarCongr_inv_app_hom_app {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')
    (G : Sheaf (ProEt.topology Z) A) (V : Y.ProEtᵒᵖ) :
    ((lowerStarCongr A h).inv.app G).hom.app V =
      G.obj.map ((MorphismProperty.Over.pullbackCongr h).hom.app V.unop).op := by
  subst h
  simp only [lowerStarCongr_rfl, Iso.refl_inv, NatTrans.id_app]
  rw [show (MorphismProperty.Over.pullbackCongr (rfl : g = g)).hom.app V.unop = 𝟙 _ from
    MorphismProperty.Over.Hom.ext (by simp [MorphismProperty.Over.pullbackCongr]; rfl), op_id,
    G.obj.map_id]
  rfl

/-- A natural transformation `β : R₁ ⟶ R₂` is the conjugate of `α : L₂ ⟶ L₁` as soon as it
satisfies the unit identity of the conjugate, provided the unit and the counit of `adj₁` are
invertible. -/
lemma _root_.CategoryTheory.conjugateEquiv_eq_of_unit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [∀ c, IsIso (adj₁.unit.app c)] [∀ d, IsIso (adj₁.counit.app d)] (α : L₂ ⟶ L₁)
    (β : R₁ ⟶ R₂)
    (h : ∀ c, adj₁.unit.app c ≫ β.app (L₁.obj c) = adj₂.unit.app c ≫ R₂.map (α.app c)) :
    conjugateEquiv adj₁ adj₂ α = β := by
  have key (c : C) : (conjugateEquiv adj₁ adj₂ α).app (L₁.obj c) = β.app (L₁.obj c) := by
    rw [← cancel_epi (adj₁.unit.app c), unit_conjugateEquiv, h]
  ext d
  have n₁ := (conjugateEquiv adj₁ adj₂ α).naturality (adj₁.counit.app d)
  have n₂ := β.naturality (adj₁.counit.app d)
  dsimp only [Functor.id_obj, Functor.comp_obj] at n₁ n₂
  rw [← cancel_epi (R₁.map (adj₁.counit.app d)), n₁, n₂, key]

end

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The unit of the adjunction `(e.inv)_* ⊣ (e.hom)_*` of the pushforward equivalence. -/
lemma lowerStarEquivalence_symm_toAdjunction_unit_app {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : Sheaf (ProEt.topology Y) A) :
    (lowerStarEquivalence A e).symm.toAdjunction.unit.app M =
      (lowerStarComp A e.inv e.hom ≪≫ lowerStarCongr A e.inv_hom_id ≪≫ lowerStarId A Y).inv.app M :=
  by
  simp only [Equivalence.toAdjunction_unit, Equivalence.symm_unit]
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option maxHeartbeats 2000000 in
/-- The units of the pushforward equivalences along `g₁` and `g₂` compose to the unit of the
pushforward equivalence along `g₂ ≫ g₁`. -/
lemma lowerStarComp_unit_aux {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (g₁ : Y ⟶ X) (f₂ : Y ⟶ Z)
    (g₂ : Z ⟶ Y) (h₁ : g₁ ≫ f₁ = 𝟙 Y) (h₂ : g₂ ≫ f₂ = 𝟙 Z) (h₁₂ : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ = 𝟙 Z)
    (M : Sheaf (Scheme.ProEt.topology Z) A) :
    (lowerStarComp A g₂ f₂ ≪≫ lowerStarCongr A h₂ ≪≫ lowerStarId A Z).inv.app M ≫
        (f₂)_*[A].map ((lowerStarComp A g₁ f₁ ≪≫ lowerStarCongr A h₁ ≪≫ lowerStarId A Y).inv.app
          ((g₂)_*[A].obj M)) ≫
        (lowerStarComp A f₁ f₂).hom.app ((g₁)_*[A].obj ((g₂)_*[A].obj M)) =
      (lowerStarComp A (g₂ ≫ g₁) (f₁ ≫ f₂) ≪≫ lowerStarCongr A h₁₂ ≪≫ lowerStarId A Z).inv.app M ≫
        (f₁ ≫ f₂)_*[A].map ((lowerStarComp A g₂ g₁).inv.app M) := by
  ext W
  simp only [Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]


  simp only [lowerStar_map_hom_app', NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarComp_inv_app_hom_app, lowerStarCongr_inv_app_hom_app,
    lowerStarId_inv_app_hom_app]
  simp only [lowerStar, Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
    ← Functor.map_comp, ← op_comp, Category.assoc]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  repeat' apply pullback.hom_ext
  all_goals simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
    MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp,
    MorphismProperty.Over.pullbackId]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
set_option maxHeartbeats 8000000 in
/-- Under conjugation along the adjunctions `(e.inv)_* ⊣ (e.hom)_*` of the pushforward
equivalences, the composition isomorphism of the pushforwards along the inverses corresponds to
the composition isomorphism of the pushforwards along the morphisms. -/
lemma conjugateIsoEquiv_lowerStarComp_symm {X Y Z : Scheme.{u}} (e : X ≅ Y) (e' : Y ≅ Z) :
    conjugateIsoEquiv ((lowerStarEquivalence A e').symm.toAdjunction.comp
        (lowerStarEquivalence A e).symm.toAdjunction)
      (lowerStarEquivalence A (e ≪≫ e')).symm.toAdjunction (lowerStarComp A e'.inv e.inv).symm =
      lowerStarComp A e.hom e'.hom := by
  ext : 1
  refine conjugateEquiv_eq_of_unit _ _ _ _ fun M ↦ ?_
  simp only [Adjunction.comp_unit_app, lowerStarEquivalence_symm_toAdjunction_unit_app]
  exact (Category.assoc _ _ _).trans
    (lowerStarComp_unit_aux A e.hom e.inv e'.hom e'.inv e.inv_hom_id e'.inv_hom_id _ M)

end AlgebraicGeometry.ProEtale
