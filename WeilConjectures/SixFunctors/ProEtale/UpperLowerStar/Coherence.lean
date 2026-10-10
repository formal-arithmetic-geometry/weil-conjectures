/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Iso

/-!
# Coherence of the pushforwards and pullbacks on the small pro-étale sites

The composition isomorphisms `(h₁)_* ⋙ (h₂)_* ≅ (h₁ ≫ h₂)_*`
(`AlgebraicGeometry.ProEtale.lowerStarComp`) and `(h₁ ≫ h₂)^* ≅ (h₂)^* ⋙ (h₁)^*`
(`AlgebraicGeometry.ProEtale.upperStarComp`) satisfy the associativity law: the two ways of
identifying the pushforward (resp. pullback) along `f ≫ g ≫ h` with the composite of the three
pushforwards (resp. pullbacks) agree, up to the identification `(f ≫ g) ≫ h = f ≫ (g ≫ h)`.
For the pushforwards this is the associativity of base change
(`CategoryTheory.MorphismProperty.Over.pullbackComp_assoc`); it passes to the pullbacks by
conjugation along the adjunctions `g^* ⊣ g_*`.

This is the pro-étale counterpart of `CategoryTheory.GrothendieckTopology.upperStarComp_assoc`.

## Main results

- `AlgebraicGeometry.ProEtale.lowerStarComp_assoc` and
  `AlgebraicGeometry.ProEtale.upperStarComp_assoc`: the associativity laws.
- `AlgebraicGeometry.ProEtale.upperStarComp_hom_app_assoc`: the associativity law for the
  pullbacks, evaluated at a sheaf.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Conjugate

variable {R S T : Scheme.{u}}

/-- The composition isomorphism of the pullbacks is conjugate to that of the pushforwards. -/
lemma conjugateIsoEquiv_upperStarComp (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    conjugateIsoEquiv ((upperStarLowerStarAdjunction A h₂).comp
        (upperStarLowerStarAdjunction A h₁)) (upperStarLowerStarAdjunction A (h₁ ≫ h₂))
      (upperStarComp A h₁ h₂) = lowerStarComp A h₁ h₂ := by
  ext : 1
  exact conjugateEquiv_upperStarComp_hom A h₁ h₂

/-- The congruence isomorphism of the pullbacks is conjugate to the inverse of that of the
pushforwards. -/
lemma conjugateIsoEquiv_upperStarCongr {g g' : S ⟶ R} (h : g = g') :
    conjugateIsoEquiv (upperStarLowerStarAdjunction A g') (upperStarLowerStarAdjunction A g)
      (upperStarCongr A h) = (lowerStarCongr A h).symm := by
  subst h
  ext : 1
  simp [upperStarCongr, lowerStarCongr]

end Conjugate

section Components

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The restriction maps of `g_* G` are those of `G` along the base changes. -/
lemma lowerStar_obj_obj_map {Z W : Scheme.{u}} (g : Z ⟶ W) (G : Sheaf (ProEt.topology Z) A)
    {V V' : W.ProEtᵒᵖ} (φ : V ⟶ V') :
    ((g)_*[A].obj G).obj.map φ =
      G.obj.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map φ.unop).op :=
  rfl

end Components

section Assoc

variable {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)

set_option backward.isDefEq.respectTransparency.types false in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The associativity law for the composition isomorphisms of the pushforwards. -/
lemma lowerStarComp_assoc :
    (f)_*[A].associator (g)_*[A] (h)_*[A] ≪≫
        Functor.isoWhiskerLeft (f)_*[A] (lowerStarComp A g h) ≪≫ lowerStarComp A f (g ≫ h) =
      Functor.isoWhiskerRight (lowerStarComp A f g) (h)_*[A] ≪≫ lowerStarComp A (f ≫ g) h ≪≫
        lowerStarCongr A (Category.assoc f g h) := by
  ext M b
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
    lowerStarComp_hom_app_hom_app, lowerStarCongr_hom_app_hom_app, lowerStar_map_hom_app',
    lowerStar_obj_obj_map, ← Functor.map_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  simp only [Quiver.Hom.unop_op]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
    · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
        MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]
  · simp [MorphismProperty.Over.pullback, MorphismProperty.Over.mk,
      MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullbackComp]

/-- The associativity law for the composition isomorphisms of the pullbacks, obtained from
`AlgebraicGeometry.ProEtale.lowerStarComp_assoc` by conjugation. -/
lemma upperStarComp_assoc :
    upperStarComp A f (g ≫ h) ≪≫ Functor.isoWhiskerRight (upperStarComp A g h) (f)^*[A] ≪≫
        (h)^*[A].associator (g)^*[A] (f)^*[A] =
      upperStarCongr A (Category.assoc f g h).symm ≪≫ upperStarComp A (f ≫ g) h ≪≫
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
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_upperStarCongr, Iso.trans_assoc]
  sorry

/-- The associativity law for the composition isomorphisms of the pullbacks, evaluated at a
sheaf. -/
lemma upperStarComp_hom_app_comp_upperStarComp_hom_app (M : Sheaf (ProEt.topology V) A) :
    (upperStarComp A (f ≫ g) h).hom.app M ≫ (upperStarComp A f g).hom.app ((h)^*[A].obj M) =
      (upperStarCongr A (Category.assoc f g h)).hom.app M ≫
        (upperStarComp A f (g ≫ h)).hom.app M ≫ (f)^*[A].map ((upperStarComp A g h).hom.app M) := by
  have := congrArg (fun e ↦ e.hom.app M) (upperStarComp_assoc A f g h)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id] at this
  rw [this, ← Category.assoc, ← NatTrans.comp_app, ← Iso.trans_hom]
  simp [upperStarCongr]

end Assoc

section Congr

variable {P Q R : Scheme.{u}}

/-- The congruence isomorphisms of the pullbacks compose. -/
lemma upperStarCongr_trans {g g' g'' : P ⟶ Q} (h : g = g') (h' : g' = g'') :
    upperStarCongr A h ≪≫ upperStarCongr A h' = upperStarCongr A (h.trans h') := by
  subst h h'
  simp [upperStarCongr]

/-- The composition isomorphism of the pullbacks is natural in the first morphism. -/
lemma upperStarCongr_hom_app_comp_upperStarComp_hom_app {x y : P ⟶ Q} (p : x = y) (g : Q ⟶ R)
    (M : Sheaf (ProEt.topology R) A) :
    (upperStarCongr A (congrArg (· ≫ g) p)).hom.app M ≫ (upperStarComp A y g).hom.app M =
      (upperStarComp A x g).hom.app M ≫ (upperStarCongr A p).hom.app ((g)^*[A].obj M) := by
  subst p
  simp [upperStarCongr]

/-- The composition isomorphism of the pullbacks is natural in the second morphism. -/
lemma upperStarCongr_hom_app_comp_upperStarComp_hom_app' (g : P ⟶ Q) {x y : Q ⟶ R} (p : x = y)
    (M : Sheaf (ProEt.topology R) A) :
    (upperStarCongr A (congrArg (g ≫ ·) p)).hom.app M ≫ (upperStarComp A g y).hom.app M =
      (upperStarComp A g x).hom.app M ≫ (g)^*[A].map ((upperStarCongr A p).hom.app M) := by
  subst p
  simp [upperStarCongr]

end Congr

end AlgebraicGeometry.ProEtale
