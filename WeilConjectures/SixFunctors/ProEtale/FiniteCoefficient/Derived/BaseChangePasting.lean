/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Naturality, identity and pasting for the pro-étale derived base change map

The derived base change map `AlgebraicGeometry.ProEtale.derivedBaseChangeMap sq :
Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on the unbounded derived categories of pro-étale sheaves is the
mate of the square isomorphism `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`. Using
the associativity and unit laws of the composition isomorphisms of derived pullbacks
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence`), we show
(blueprint `lemma-naturality-pasting-comparison--1`, `--2`):

- `AlgebraicGeometry.ProEtale.derivedBaseChangeMap_naturality`: it is natural;
- `AlgebraicGeometry.ProEtale.derivedBaseChangeMap_id`: it is the identity for an identity square;
- `AlgebraicGeometry.ProEtale.derivedBaseChangeMap_paste_horiz`,
  `AlgebraicGeometry.ProEtale.derivedBaseChangeMap_paste_vert`: it is compatible with horizontal
  and vertical pasting of commutative squares, the latter modulo the composition isomorphisms
  `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComp` of derived direct images.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Coherence

variable {W X Y Z : Scheme.{u}}

/-- A consequence of the associativity of the composition isomorphisms of derived pullbacks. -/
@[reassoc]
lemma map_leftDerivedUpperStarComp_hom_app_comp_inv_app (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Z) A)) :
    L((a)^*[A]).map ((leftDerivedUpperStarComp A b c).hom.app K) ≫
        (leftDerivedUpperStarComp A a b).inv.app (L((c)^*[A]).obj K) =
      (leftDerivedUpperStarComp A a (b ≫ c)).inv.app K ≫
        (leftDerivedUpperStarCongr A (Category.assoc a b c).symm).hom.app K ≫
        (leftDerivedUpperStarComp A (a ≫ b) c).hom.app K := by
  have h := leftDerivedUpperStarComp_assoc_app (A := A) a b c K
  rw [← cancel_epi ((leftDerivedUpperStarComp A a (b ≫ c)).hom.app K), Iso.hom_inv_id_app_assoc,
    ← cancel_mono ((leftDerivedUpperStarComp A a b).hom.app (L((c)^*[A]).obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  rw [h, leftDerivedUpperStarCongr_hom_app_trans_assoc, leftDerivedUpperStarCongr_hom_app_self,
    Category.id_comp]

/-- A consequence of the associativity of the composition isomorphisms of derived pullbacks. -/
@[reassoc]
lemma leftDerivedUpperStarComp_hom_app_comp_map_inv_app (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (K : DerivedCategory (Sheaf (ProEt.topology Z) A)) :
    (leftDerivedUpperStarComp A a b).hom.app (L((c)^*[A]).obj K) ≫
        L((a)^*[A]).map ((leftDerivedUpperStarComp A b c).inv.app K) =
      (leftDerivedUpperStarComp A (a ≫ b) c).inv.app K ≫
        (leftDerivedUpperStarCongr A (Category.assoc a b c)).hom.app K ≫
        (leftDerivedUpperStarComp A a (b ≫ c)).hom.app K := by
  rw [← cancel_epi ((leftDerivedUpperStarComp A (a ≫ b) c).hom.app K),
    reassoc_of% (leftDerivedUpperStarComp_assoc_app (A := A) a b c K), Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

end Coherence

section Horizontal

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
  {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

/-- The square isomorphism of two squares pasted horizontally is the composite of the two square
isomorphisms, modulo the composition isomorphisms of the derived pullbacks. -/
lemma leftDerivedUpperStarSquareIso_paste_horiz_hom_app (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g))
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedUpperStarSquareIso A sq).hom.app K =
      L((f'')^*[A]).map ((leftDerivedUpperStarComp A h g).hom.app K) ≫
        (leftDerivedUpperStarSquareIso A sq₂).hom.app (L((g)^*[A]).obj K) ≫
        L((g'')^*[A]).map ((leftDerivedUpperStarSquareIso A sq₁).hom.app K) ≫
        (leftDerivedUpperStarComp A g'' g').inv.app (L((f)^*[A]).obj K) := by
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [map_leftDerivedUpperStarComp_hom_app_comp_inv_app_assoc,
    leftDerivedUpperStarComp_hom_app_congr_left_assoc,
    leftDerivedUpperStarComp_assoc_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.map_comp_assoc, leftDerivedUpperStarComp_hom_app_congr_right_assoc,
    map_leftDerivedUpperStarComp_hom_app_comp_inv_app, Iso.hom_inv_id_app_assoc]
  simp

open scoped TwoSquare in
/-- **Horizontal pasting of the pro-étale derived base change maps**: the base change map of
two squares pasted horizontally is the composite
`(h ≫ g)^* Rf_* ≅ h^* g^* Rf_* ⟶ h^* Rf'_* g'^* ⟶ Rf''_* g''^* g'^* ≅ Rf''_* (g'' ≫ g')^*`
of the base change maps of the two squares. Only commutativity of the squares is required.
(blueprint: `lemma-naturality-pasting-comparison--2`) -/
lemma derivedBaseChangeMap_paste_horiz (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    derivedBaseChangeMap A sq =
      Functor.whiskerLeft R((f)_*[A]) (leftDerivedUpperStarComp A h g).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedBaseChangeMap A sq₁) L((h)^*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L((g')^*[A]) (derivedBaseChangeMap A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarComp A g'' g').inv R((f'')_*[A]) := by
  have h1 : TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom =
      ((TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq₁).hom ≫ₕ
        TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq₂).hom).whiskerTop
          (leftDerivedUpperStarComp A h g).hom).whiskerBottom
            (leftDerivedUpperStarComp A g'' g').inv := by
    refine TwoSquare.ext _ _ fun K => ?_
    simpa only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, TwoSquare.hComp_app,
      Functor.comp_obj, Category.assoc] using
        leftDerivedUpperStarSquareIso_paste_horiz_hom_app A sq₁ sq₂ sq K
  have h2 : derivedBaseChangeMap A sq = (((derivedBaseChangeMap A sq₁ ≫ᵥ
      derivedBaseChangeMap A sq₂).whiskerRight (leftDerivedUpperStarComp A h g).hom).whiskerLeft
        (leftDerivedUpperStarComp A g'' g').inv) := by
    change mateEquiv _ _ (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom) = _
    rw [h1,
      mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp]
    rfl
  rw [h2]
  ext K
  simp

end Horizontal

section Vertical

variable {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z}

/-- The composition isomorphism `Rf_* ⋙ Re_* ≅ R(f ≫ e)_*` of derived direct images on the
unbounded derived categories of pro-étale sheaves: the conjugate, along the derived adjunctions,
of the composition isomorphism `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp` of the
derived pullbacks. -/
noncomputable def rightDerivedLowerStarComp (f : X ⟶ Y) (e : Y ⟶ Z) :
    R((f)_*[A]) ⋙ R((e)_*[A]) ≅ R((f ≫ e)_*[A]) :=
  conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction A e).comp
      (derivedUpperStarLowerStarAdjunction A f))
    (derivedUpperStarLowerStarAdjunction A (f ≫ e)) (leftDerivedUpperStarComp A f e)

/-- The square isomorphism of two squares pasted vertically is the composite of the two square
isomorphisms, modulo the composition isomorphisms of the derived pullbacks. -/
lemma leftDerivedUpperStarSquareIso_paste_vert_hom_app (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k)
    (K : DerivedCategory (Sheaf (ProEt.topology Z) A)) :
    (leftDerivedUpperStarSquareIso A sq).hom.app K =
      (leftDerivedUpperStarComp A f' e').hom.app (L((k)^*[A]).obj K) ≫
        L((f')^*[A]).map ((leftDerivedUpperStarSquareIso A sq₂).hom.app K) ≫
        (leftDerivedUpperStarSquareIso A sq₁).hom.app (L((e)^*[A]).obj K) ≫
        L((g')^*[A]).map ((leftDerivedUpperStarComp A f e).inv.app K) := by
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_hom_app_comp_map_inv_app_assoc,
    leftDerivedUpperStarComp_hom_app_congr_right_assoc,
    map_leftDerivedUpperStarComp_hom_app_comp_inv_app_assoc, Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarComp_hom_app_congr_left_assoc,
    leftDerivedUpperStarComp_assoc_app_assoc]
  simp

open scoped TwoSquare in
/-- **Vertical pasting of the pro-étale derived base change maps**: the base change map of two
squares pasted vertically is the composite
`k^* R(f ≫ e)_* ≅ k^* Re_* Rf_* ⟶ Re'_* g^* Rf_* ⟶ Re'_* Rf'_* g'^* ≅ R(f' ≫ e')_* g'^*`
of the base change maps of the two squares. Only commutativity of the squares is required.
(blueprint: `lemma-naturality-pasting-comparison--2`) -/
lemma derivedBaseChangeMap_paste_vert (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k) :
    derivedBaseChangeMap A sq =
      Functor.whiskerRight (rightDerivedLowerStarComp A f e).inv L((k)^*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft R((f)_*[A]) (derivedBaseChangeMap A sq₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedBaseChangeMap A sq₁) R((e')_*[A]) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L((g')^*[A]) (rightDerivedLowerStarComp A f' e').hom := by
  have h1 : TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom =
      ((TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq₂).hom ≫ᵥ
        TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq₁).hom).whiskerRight
          (leftDerivedUpperStarComp A f' e').hom).whiskerLeft
            (leftDerivedUpperStarComp A f e).inv := by
    refine TwoSquare.ext _ _ fun K => ?_
    simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
      Functor.comp_obj, Category.assoc] using
        leftDerivedUpperStarSquareIso_paste_vert_hom_app A sq₁ sq₂ sq K
  have h2 : derivedBaseChangeMap A sq = ((derivedBaseChangeMap A sq₁ ≫ₕ
      derivedBaseChangeMap A sq₂).whiskerBottom (rightDerivedLowerStarComp A f' e').hom).whiskerTop
        (rightDerivedLowerStarComp A f e).inv := by
    change mateEquiv _ _ (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom) = _
    rw [h1, conjugateEquiv_mateEquiv_vcomp _ ((derivedUpperStarLowerStarAdjunction A e).comp
      (derivedUpperStarLowerStarAdjunction A f)),
      mateEquiv_conjugateEquiv_vcomp _ ((derivedUpperStarLowerStarAdjunction A e').comp
      (derivedUpperStarLowerStarAdjunction A f')), mateEquiv_hcomp]
    rfl
  rw [h2]
  ext K
  simp

end Vertical

section Identity

variable {X Y : Scheme.{u}}

/-- The square isomorphism of the identity square on `f` is built from the identity
isomorphisms `L(𝟙 _)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarSquareIso_id_hom_app (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y))
    (K : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    (leftDerivedUpperStarSquareIso A sq).hom.app K =
      L((f)^*[A]).map ((leftDerivedUpperStarId A Y).hom.app K) ≫
        (leftDerivedUpperStarId A X).inv.app (L((f)^*[A]).obj K) := by
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj]
  rw [← cancel_epi ((leftDerivedUpperStarComp A f (𝟙 Y)).hom.app K), Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarComp_id_right_app_assoc,
    ← cancel_mono ((leftDerivedUpperStarId A X).hom.app (L((f)^*[A]).obj K))]
  simp [leftDerivedUpperStarComp_id_left_app]
  rfl

open scoped TwoSquare in
/-- **The pro-étale derived base change map of the identity square** is the identity, modulo the
identity isomorphisms `L(𝟙 _)^* ≅ 𝟭` of the derived pullbacks.
(blueprint: `lemma-naturality-pasting-comparison--2`) -/
lemma derivedBaseChangeMap_id (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)) :
    derivedBaseChangeMap A sq =
      Functor.whiskerLeft R((f)_*[A]) (leftDerivedUpperStarId A Y).hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (leftDerivedUpperStarId A X).inv R((f)_*[A]) := by
  have h1 : TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom =
      ((TwoSquare.mk (𝟭 _) L((f)^*[A]) L((f)^*[A]) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (leftDerivedUpperStarId A Y).hom).whiskerBottom (leftDerivedUpperStarId A X).inv := by
    refine TwoSquare.ext _ _ fun K => ?_
    simpa [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app] using
      leftDerivedUpperStarSquareIso_id_hom_app A f sq K
  change mateEquiv _ _ (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarSquareIso A sq).hom) = _
  rw [h1, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]
  ext K
  simp

end Identity

section Naturality

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Blueprint `lemma-naturality-pasting-comparison--1`: for every commutative square, the
pro-étale derived base change maps `Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` form a natural transformation
on the unbounded derived categories. -/
@[reassoc]
lemma derivedBaseChangeMap_naturality (sq : CommSq g' f' f g)
    {K K' : DerivedCategory (Sheaf (ProEt.topology X) A)} (φ : K ⟶ K') :
    L((g)^*[A]).map (R((f)_*[A]).map φ) ≫ (derivedBaseChangeMap A sq).app K' =
      (derivedBaseChangeMap A sq).app K ≫ R((f')_*[A]).map (L((g')^*[A]).map φ) :=
  (derivedBaseChangeMap A sq).naturality φ

end Naturality

/-- Blueprint `lemma-naturality-pasting-comparison--2`: the pro-étale derived base change map is
the identity for an identity square, and the base change map of a horizontally or vertically
pasted square is the composite of the base change maps of the two squares, in the form of
blueprint `lemma-identity-pasting`. -/
theorem derivedBaseChangeMap_id_and_paste :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (sq : CommSq (𝟙 X) f f (𝟙 Y)),
      derivedBaseChangeMap A sq =
        Functor.whiskerLeft R((f)_*[A]) (leftDerivedUpperStarId A Y).hom ≫
          (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
          Functor.whiskerRight (leftDerivedUpperStarId A X).inv R((f)_*[A])) ∧
    (∀ {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X} {f'' : X'' ⟶ Y''}
      {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)),
      derivedBaseChangeMap A sq =
        Functor.whiskerLeft R((f)_*[A]) (leftDerivedUpperStarComp A h g).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedBaseChangeMap A sq₁) L((h)^*[A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L((g')^*[A]) (derivedBaseChangeMap A sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (leftDerivedUpperStarComp A g'' g').inv R((f'')_*[A])) ∧
    (∀ {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z} (sq₁ : CommSq g' f' f g)
      (sq₂ : CommSq g e' e k) (sq : CommSq g' (f' ≫ e') (f ≫ e) k),
      derivedBaseChangeMap A sq =
        Functor.whiskerRight (rightDerivedLowerStarComp A f e).inv L((k)^*[A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft R((f)_*[A]) (derivedBaseChangeMap A sq₂) ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (derivedBaseChangeMap A sq₁) R((e')_*[A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L((g')^*[A]) (rightDerivedLowerStarComp A f' e').hom) :=
  ⟨fun f sq ↦ derivedBaseChangeMap_id A f sq,
    fun sq₁ sq₂ sq ↦ derivedBaseChangeMap_paste_horiz A sq₁ sq₂ sq,
    fun sq₁ sq₂ sq ↦ derivedBaseChangeMap_paste_vert A sq₁ sq₂ sq⟩

end AlgebraicGeometry.ProEtale
