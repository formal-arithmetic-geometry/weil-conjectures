/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-!
# Exchange on normalized global generators

Source: blueprint main-20261015, sk-prop-a1-kummer,
prop-pur-gm-relative-kummer.proof.md, Step 3; Stacks Tags 0736 and 072W
(blueprint: lem-pur-relative-kummer-exchange-generators).

Global classes are derived morphisms out of the constant free rank-one module sheaf.
Sections are sheaf morphisms out of that same sheaf, equivalently their value on 1.
All comparisons below are the canonical single, constant, shift and adjunction comparisons.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical derived pullback of a constant object in degree zero.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable def genericConstantIso (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (L(upperStar C f)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology C).obj M)) ≅
    (_root_.DerivedCategory.singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology C).obj M) :=
  (singleFunctorCompLeftDerivedUpperStarIso C f).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso C f).app M)

section Generic
variable (C : Type u') [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  (M : C)

/-- Pullback of a derived class with general coefficients, using canonical comparisons. -/
noncomputable def genericPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) (q : ℕ)
    (x : (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf Y.smallEtaleTopology C).obj M) ⟶ K⟦(q : ℤ)⟧) :
    (DerivedCategory.singleFunctor _ 0).obj ((constantSheaf X.smallEtaleTopology C).obj M) ⟶
      (L(upperStar C f)).obj K⟦(q : ℤ)⟧ :=
  (genericConstantIso C M f).inv ≫
    (L(upperStar C f)).map x ≫ ((L(upperStar C f)).commShiftIso (q : ℤ)).hom.app K

/-- Leray edge section with general coefficients, using the canonical derived adjunction. -/
noncomputable def genericEdge {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (q : ℕ)
    (x : (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology C).obj M) ⟶ K⟦(q : ℤ)⟧) :
    ((constantSheaf Y.smallEtaleTopology C).obj M) ⟶
      (DerivedCategory.homologyFunctor _ (q : ℤ)).obj ((R(lowerStar C f)).obj K) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction C f).homEquiv _ _
        ((genericConstantIso C M f).hom ≫ x) ≫
        ((R(lowerStar C f)).commShiftIso (q : ℤ)).hom.app K) ≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso
      (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app _
end Generic

/-- The existing exact derived inverse image, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeUpper (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (_M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) :=
  L(upperStar C f)

/-- The existing total derived direct image, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeLower (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (_M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    _root_.DerivedCategory (Sheaf X.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C) :=
  R(lowerStar C f)

/-- The canonical shift structure on exact derived inverse image, transported from
termwise inverse image using the existing comparison, as in Etale.Derived.Shift.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeUpperCommShift
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (generic_kummerExchangeUpper C M f).CommShift ℤ :=
  commShiftLeftDerivedUpperStar C f

/-- The canonical adjoint shift structure on derived direct image, as in
Etale.Derived.Shift; no choice of a shift comparison is made.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeLowerCommShift
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (generic_kummerExchangeLower C M f).CommShift ℤ :=
  commShiftRightDerivedLowerStar C f

/-- The existing canonical derived adjunction, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeAdjunction (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    generic_kummerExchangeUpper C M f ⊣ generic_kummerExchangeLower C M f :=
  derivedUpperStarLowerStarAdjunction C f

/-- The specified module exchange, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable def generic_kummerExchangeArrow (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (generic_kummerExchangeUpper C M g).obj ((generic_kummerExchangeLower C M a).obj K) ⟶
      (generic_kummerExchangeLower C M a').obj ((generic_kummerExchangeUpper C M v).obj K) :=
  (derivedBaseChangeMap C sq.toCommSq).app K

/-- The constant free rank-one coefficient sheaf used to represent sections.
Source: Stacks Tag 072W and blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeConstant (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    (T : Scheme.{u}) : Sheaf T.smallEtaleTopology C :=
  (constantSheaf T.smallEtaleTopology C).obj M

/-- Exact pullback of a global class, with the canonical constant and shift comparisons.
This is the module-derived realization of cohomology pullback, without changing scalars.
Source: Stacks Tag 0736, resolution construction; blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeClassPullback
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  genericPullback C M f

/-- Leray edge section: transpose the class under the actual derived adjunction, then
apply H⁰ and the canonical H⁰(K[q]) = H^q(K) comparison. On an injective representative
this sends a global cocycle to its class in the direct-image cohomology sheaf.
Source: Stacks Tag 072W, cycle-quotient proof; blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev generic_kummerExchangeEdge (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  genericEdge C M f

/-- Pullback of an edge section, including the canonical identification f* A_Y = A_X.
Source: blueprint Step 3; Stacks Tag 0736
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable def generic_kummerExchangeSectionPullback
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology C}
    (s : generic_kummerExchangeConstant C M Y ⟶ G) :
    generic_kummerExchangeConstant C M X ⟶ (upperStar C f).obj G :=
  (Scheme.upperStarConstantSheafIso C f).inv.app
    M ≫ (upperStar C f).map s

/-- H^q of the specified module-derived exchange, with exact inverse-image comparison.
Source: Stacks Tag 0736; blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable def generic_kummerExchangeHigherMap (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (q : ℤ) :
    (upperStar C g).obj
      ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((generic_kummerExchangeLower C M a).obj K)) ⟶
    (_root_.DerivedCategory.homologyFunctor _ q).obj
      ((generic_kummerExchangeLower C M a').obj
        ((generic_kummerExchangeUpper C M v).obj K)) :=
  (leftDerivedUpperStarHomologyFunctorIso C g q).hom.app _ ≫
    (_root_.DerivedCategory.homologyFunctor _ q).map
      (generic_kummerExchangeArrow C M sq K)

/-- The direct image Ra_*a*L, with L placed in degree zero.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable def generic_kummerExchangeImage (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X B : Scheme.{u}} (a : X ⟶ B)
    (L₀ : Sheaf B.smallEtaleTopology C) :
    _root_.DerivedCategory (Sheaf B.smallEtaleTopology C) :=
  (generic_kummerExchangeLower C M a).obj
    ((generic_kummerExchangeUpper C M a).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))

/-- The specified exchange preserves units after the canonical square identification.
Source: blueprint Step 3; Stacks Tag 0736
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: transpose both sides under a'^* ⊣ Ra'_*. Naturality of the square comparison
and the triangle identity turn the left transpose into theta_L; the right transpose
is theta_L by the other triangle identity. Injectivity of the adjunction gives equality. -/
theorem generic_relativeKummerExchange_unit (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology C) :
    (generic_kummerExchangeUpper C M g).map
        ((generic_kummerExchangeAdjunction C M a).unit.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) ≫
      generic_kummerExchangeArrow C M sq
        ((generic_kummerExchangeUpper C M a).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) =
    (generic_kummerExchangeAdjunction C M a').unit.app
        ((generic_kummerExchangeUpper C M g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) ≫
      (generic_kummerExchangeLower C M a').map
        ((derivedSquareUpperStarIso C sq.toCommSq).hom.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)) := by
  exact map_unit_derivedBaseChangeMap_app C sq.toCommSq _

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory upperStar lowerStar

private theorem exact_homology_class
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (A : C) (K : _root_.DerivedCategory C) (K' : _root_.DerivedCategory D) (q : ℕ)
    (h : (_root_.DerivedCategory.singleFunctor C 0).obj A ⟶ K⟦(q : ℤ)⟧)
    (t : G.mapDerivedCategory.obj K ⟶ K') :
    G.map ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app A ≫
        (_root_.DerivedCategory.homologyFunctor C 0).map h ≫
        ((_root_.DerivedCategory.homologyFunctor C 0).shiftIso
          (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K) ≫
      (G.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).hom.app K ≫
      (_root_.DerivedCategory.homologyFunctor D (q : ℤ)).map t =
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app (G.obj A) ≫
      (_root_.DerivedCategory.homologyFunctor D 0).map
        ((G.mapDerivedCategorySingleFunctor 0).inv.app A ≫
          G.mapDerivedCategory.map h ≫
          (G.mapDerivedCategory.commShiftIso (q : ℤ)).hom.app K ≫
          (shiftFunctor _ (q : ℤ)).map t) ≫
      ((_root_.DerivedCategory.homologyFunctor D 0).shiftIso
        (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K' := by
  let H₀ := _root_.DerivedCategory.homologyFunctor C 0
  let H₀' := _root_.DerivedCategory.homologyFunctor D 0
  let ν := G.mapDerivedCategoryHomologyFunctorIso 0
  let c := G.mapDerivedCategorySingleFunctor 0
  let s := _root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C 0
  let s' := _root_.DerivedCategory.singleFunctorCompHomologyFunctorIso D 0
  have hsingle : G.map (s.inv.app A) ≫ ν.hom.app
        ((_root_.DerivedCategory.singleFunctor C 0).obj A) =
      s'.inv.app (G.obj A) ≫ H₀'.map (c.inv.app A) := by
    apply (cancel_mono (H₀'.map (c.hom.app A) ≫ s'.hom.app (G.obj A))).1
    have hc := G.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor 0 A
    change ν.hom.app _ ≫ H₀'.map (c.hom.app A) ≫ s'.hom.app _ =
      G.map (s.hom.app A) at hc
    simp only [Category.assoc]
    rw [hc]
    simp only [← G.map_comp, Iso.inv_hom_id_app, ← H₀'.map_comp_assoc]
    erw [G.map_id, H₀'.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id_app]
    rfl
  have hn := ν.hom.naturality h
  simp only [Functor.comp_map] at hn
  have hs := G.mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso
    (q : ℤ) 0 (q : ℤ) (add_zero _) K
  have ht := ((H₀'.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _)).hom).naturality t
  simp only [Functor.comp_map] at ht
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs, reassoc_of% hn, reassoc_of% hsingle]
  erw [← ht]
  rfl

private theorem iso_homology_class
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D) [LF.CommShift ℤ]
    (e : LF ≅ G.mapDerivedCategory) [NatTrans.CommShift e.inv ℤ]
    (A : C) (K : _root_.DerivedCategory C) (K' : _root_.DerivedCategory D) (q : ℕ)
    (h : (_root_.DerivedCategory.singleFunctor C 0).obj A ⟶ K⟦(q : ℤ)⟧)
    (t : LF.obj K ⟶ K') :
    G.map ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
        (_root_.DerivedCategory.homologyFunctor C 0).map h ≫
        ((_root_.DerivedCategory.homologyFunctor C 0).shiftIso
          (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K) ≫
      (G.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).hom.app K ≫
      (_root_.DerivedCategory.homologyFunctor D (q : ℤ)).map (e.inv.app K ≫ t) =
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app (G.obj A) ≫
      (_root_.DerivedCategory.homologyFunctor D 0).map
        ((G.mapDerivedCategorySingleFunctor 0).inv.app A ≫
          e.inv.app _ ≫ LF.map h ≫
          (LF.commShiftIso (q : ℤ)).hom.app K ≫ (shiftFunctor _ (q : ℤ)).map t) ≫
      ((_root_.DerivedCategory.homologyFunctor D 0).shiftIso
        (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K' := by
  rw [exact_homology_class G A K K' q h (e.inv.app K ≫ t)]
  have hs := NatTrans.shift_app_comm e.inv (q : ℤ) K
  have hn := e.inv.naturality h
  have he : (G.mapDerivedCategorySingleFunctor 0).inv.app A ≫
      G.mapDerivedCategory.map h ≫
      (G.mapDerivedCategory.commShiftIso (q : ℤ)).hom.app K ≫
      (shiftFunctor _ (q : ℤ)).map (e.inv.app K ≫ t) =
      (G.mapDerivedCategorySingleFunctor 0).inv.app A ≫ e.inv.app _ ≫
      LF.map h ≫ (LF.commShiftIso (q : ℤ)).hom.app K ≫
      (shiftFunctor _ (q : ℤ)).map t := by
    simp only [Functor.map_comp]
    rw [reassoc_of% hs, reassoc_of% hn]
  rw [he]

private theorem adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {A : C} {K : D} (z : L.obj A ⟶ K) :
    G.map (adj.homEquiv A K z) ≫ (mateEquiv adj adj' θ).natTrans.app K =
      adj'.homEquiv (G.obj A) (H.obj K) (θ.natTrans.app A ≫ H.map z) := by
  rw [adj.homEquiv_unit, G.map_comp, Category.assoc]
  have hn := (mateEquiv adj adj' θ).natTrans.naturality z
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [← Category.assoc, unit_mateEquiv, Category.assoc, ← R'.map_comp,
    adj'.homEquiv_unit]
  rfl

private theorem shifted_adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ).natTrans ℤ]
    {A : C} {K : D} (q : ℤ) (z : L.obj A ⟶ K⟦q⟧) :
    G.map (adj.homEquiv A (K⟦q⟧) z ≫ (R.commShiftIso q).hom.app K) ≫
        (G.commShiftIso q).hom.app (R.obj K) ≫
        (shiftFunctor E q).map ((mateEquiv adj adj' θ).natTrans.app K) =
      adj'.homEquiv (G.obj A) ((H.obj K)⟦q⟧)
        (θ.natTrans.app A ≫ H.map z ≫ (H.commShiftIso q).hom.app K) ≫
          (R'.commShiftIso q).hom.app (H.obj K) := by
  have hs := NatTrans.shift_app_comm (mateEquiv adj adj' θ).natTrans q K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hs
  rw [Functor.map_comp, Category.assoc, hs]
  rw [← Category.assoc, adjunct_mate]
  rw [← Category.assoc, ← adj'.homEquiv_naturality_right, Category.assoc]

set_option backward.isDefEq.respectTransparency true

private theorem constant_square_of_comp
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (La : C ⥤ D) (Lg : C ⥤ E) (Lv : D ⥤ F) (La' : E ⥤ F) (Ldiag : C ⥤ F)
    (α : Ldiag ≅ La ⋙ Lv) (γ : Ldiag ≅ Lg ⋙ La')
    (P : C) (Q : D) (P' : E) (Q' : F)
    (ca : La.obj P ≅ Q) (cg : Lg.obj P ≅ P') (cv : Lv.obj Q ≅ Q')
    (ca' : La'.obj P' ≅ Q') (cd : Ldiag.obj P ≅ Q')
    (hv : Lv.map ca.hom ≫ cv.hom = α.inv.app P ≫ cd.hom)
    (hg : La'.map cg.hom ≫ ca'.hom = γ.inv.app P ≫ cd.hom) :
    La'.map cg.inv ≫ (γ.inv.app P ≫ α.hom.app P) ≫ Lv.map ca.hom =
      ca'.hom ≫ cv.inv := by
  apply (cancel_mono cv.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hv, Iso.hom_inv_id_app_assoc, ← hg]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false

private theorem iso_homology_class_constant
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D) [LF.CommShift ℤ]
    (e : LF ≅ G.mapDerivedCategory) [NatTrans.CommShift e.inv ℤ]
    (A : C) (A' : D) (e₀ : A' ⟶ G.obj A)
    (K : _root_.DerivedCategory C) (K' : _root_.DerivedCategory D) (q : ℕ)
    (h : (_root_.DerivedCategory.singleFunctor C 0).obj A ⟶ K⟦(q : ℤ)⟧)
    (h' : (_root_.DerivedCategory.singleFunctor D 0).obj A' ⟶ K'⟦(q : ℤ)⟧)
    (t : LF.obj K ⟶ K')
    (hh : (_root_.DerivedCategory.singleFunctor D 0).map e₀ ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app A ≫ e.inv.app _ ≫
        LF.map h ≫ (LF.commShiftIso (q : ℤ)).hom.app K ≫
        (shiftFunctor _ (q : ℤ)).map t = h') :
    e₀ ≫ G.map
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
          (_root_.DerivedCategory.homologyFunctor C 0).map h ≫
          ((_root_.DerivedCategory.homologyFunctor C 0).shiftIso
            (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K) ≫
      (G.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).hom.app K ≫
      (_root_.DerivedCategory.homologyFunctor D (q : ℤ)).map (e.inv.app K ≫ t) =
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.app A' ≫
      (_root_.DerivedCategory.homologyFunctor D 0).map h' ≫
      ((_root_.DerivedCategory.homologyFunctor D 0).shiftIso
        (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app K' := by
  rw [iso_homology_class G LF e A K K' q h t]
  have hf := (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).inv.naturality e₀
  simp only [Functor.id_map, Functor.comp_map] at hf
  rw [← Category.assoc e₀, hf]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hh]

private theorem shifted_constant_adjunct_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    [G.CommShift ℤ] [H.CommShift ℤ] (θ : TwoSquare G L L' H)
    [NatTrans.CommShift (mateEquiv adj adj' θ).natTrans ℤ]
    (P : C) (Q : D) (P' : E) (Q' : F)
    (ca : L.obj P ⟶ Q) (cg : P' ⟶ G.obj P) (cv : Q' ⟶ H.obj Q)
    (ca' : L'.obj P' ⟶ Q')
    (hs : L'.map cg ≫ θ.natTrans.app P ≫ H.map ca = ca' ≫ cv)
    {K : D} (q : ℤ) (x : Q ⟶ K⟦q⟧) :
    cg ≫ G.map (adj.homEquiv _ _ (ca ≫ x) ≫ (R.commShiftIso q).hom.app K) ≫
      (G.commShiftIso q).hom.app _ ≫
        (shiftFunctor _ q).map ((mateEquiv adj adj' θ).natTrans.app K) =
      adj'.homEquiv _ _ (ca' ≫ (cv ≫ H.map x ≫ (H.commShiftIso q).hom.app K)) ≫
        (R'.commShiftIso q).hom.app _ := by
  rw [shifted_adjunct_mate adj adj' G H θ q (ca ≫ x)]
  rw [← Category.assoc, ← Adjunction.homEquiv_naturality_left]
  congr 2
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]

set_option backward.isDefEq.respectTransparency true

private theorem isoWhiskerRight_map
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F F' : C ⥤ D) (G : C ⥤ E) (H : D ⥤ E)
    (e : F ≅ F') (ν : G ≅ F' ⋙ H) (K : C) (K' : D) (t : F.obj K ⟶ K') :
    (ν ≪≫ Functor.isoWhiskerRight e.symm H).hom.app K ≫ H.map t =
      ν.hom.app K ≫ H.map (e.inv.app K ≫ t) := by
  dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, NatTrans.comp_app]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z ↦ _ ≫ z) (Functor.map_comp _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem kummer_edge_naturality (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : CommSq v a' a g)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (q : ℕ)
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology C).obj M) ⟶ K⟦(q : ℤ)⟧) :
    (Scheme.upperStarConstantSheafIso C g).inv.app M ≫
      (upperStar C g).map
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
          (_root_.DerivedCategory.homologyFunctor _ 0).map
            ((derivedUpperStarLowerStarAdjunction C a).homEquiv _ _
              ((genericConstantIso C M a).hom ≫ x) ≫
              ((R(lowerStar C a)).commShiftIso (q : ℤ)).hom.app K) ≫
          ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso
            (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app _) ≫
      (leftDerivedUpperStarHomologyFunctorIso C g (q : ℤ)).hom.app _ ≫
      (_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((derivedBaseChangeMap C sq).app K) =
    (_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
      (_root_.DerivedCategory.homologyFunctor _ 0).map
        ((derivedUpperStarLowerStarAdjunction C a').homEquiv _ _
          ((genericConstantIso C M a').hom ≫ (genericConstantIso C M v).inv ≫
            (L(upperStar C v)).map x ≫
            ((L(upperStar C v)).commShiftIso (q : ℤ)).hom.app K) ≫
          ((R(lowerStar C a')).commShiftIso (q : ℤ)).hom.app _) ≫
      ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso
        (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app _ := by
  have kummerSingle_inv (C : Type u') [Category.{u + 1} C] [Abelian C]
      [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
      [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
      (M : C) {X Y : Scheme.{u}} (f : X ⟶ Y) :
      (genericConstantIso C M f).inv =
        (_root_.DerivedCategory.singleFunctor _ 0).map
            ((Scheme.upperStarConstantSheafIso C f).inv.app M) ≫
          ((upperStar C f).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
          (leftDerivedUpperStarIsoMapDerivedCategory C f).inv.app _ := by
    rfl
  have genericConstantIso_square (C : Type u') [Category.{u + 1} C] [Abelian C]
      [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
      [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
      (M : C)
      {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
      {a : X ⟶ B} {g : B' ⟶ B} (sq : CommSq v a' a g) :
      (L(upperStar C a')).map (genericConstantIso C M g).inv ≫
        (derivedSquareUpperStarIso C sq).hom.app _ ≫
        (L(upperStar C v)).map (genericConstantIso C M a).hom =
      (genericConstantIso C M a').hom ≫ (genericConstantIso C M v).inv := by
    have hcomp {T S R : Scheme.{u}} (f : T ⟶ S) (h : S ⟶ R)
        (fh : T ⟶ R) (hh : fh = f ≫ h) :
        (L(upperStar C f)).map (genericConstantIso C M h).hom ≫
          (genericConstantIso C M f).hom =
        (leftDerivedUpperStarComp C f h fh hh).inv.app _ ≫
          (genericConstantIso C M fh).hom := by
      have hc : (upperStarComp C f h fh hh).hom.app _ ≫
          (upperStar C f).map ((Scheme.upperStarConstantSheafIso C h).hom.app M) ≫
          (Scheme.upperStarConstantSheafIso C f).hom.app M =
          (Scheme.upperStarConstantSheafIso C fh).hom.app M := by
        subst fh
        exact Scheme.upperStarConstantSheafIso_comp C f h M
      exact leftDerivedUpperStar_map_singleFunctor_comp C f h fh hh
        ((constantSheaf R.smallEtaleTopology C).obj M)
        ((Scheme.upperStarConstantSheafIso C h).hom.app M)
        ((Scheme.upperStarConstantSheafIso C fh).hom.app M)
        ((Scheme.upperStarConstantSheafIso C f).hom.app M) hc
    exact constant_square_of_comp (L(upperStar C a)) (L(upperStar C g))
      (L(upperStar C v)) (L(upperStar C a')) (L(upperStar C (v ≫ a)))
      (leftDerivedUpperStarComp C v a) (leftDerivedUpperStarComp C a' g (v ≫ a) sq.w)
      _ _ _ _ (genericConstantIso C M a) (genericConstantIso C M g)
      (genericConstantIso C M v) (genericConstantIso C M a')
      (genericConstantIso C M (v ≫ a)) (hcomp v a _ rfl) (hcomp a' g _ sq.w)
  have kummer_adjunct_class (C : Type u') [Category.{u + 1} C] [Abelian C]
      [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
      [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
      (M : C)
      {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
      {a : X ⟶ B} {g : B' ⟶ B} (sq : CommSq v a' a g)
      (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) (q : ℕ)
      (x : (_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology C).obj M) ⟶
        K⟦(q : ℤ)⟧) :
      (genericConstantIso C M g).inv ≫
        (L(upperStar C g)).map
          ((derivedUpperStarLowerStarAdjunction C a).homEquiv _ _
            ((genericConstantIso C M a).hom ≫ x) ≫
            ((R(lowerStar C a)).commShiftIso (q : ℤ)).hom.app K) ≫
        ((L(upperStar C g)).commShiftIso (q : ℤ)).hom.app _ ≫
        (shiftFunctor _ (q : ℤ)).map ((derivedBaseChangeMap C sq).app K) =
      (derivedUpperStarLowerStarAdjunction C a').homEquiv _ _
          ((genericConstantIso C M a').hom ≫ ((genericConstantIso C M v).inv ≫
            (L(upperStar C v)).map x ≫
            ((L(upperStar C v)).commShiftIso (q : ℤ)).hom.app K)) ≫
        ((R(lowerStar C a')).commShiftIso (q : ℤ)).hom.app _ := by
    let θ := TwoSquare.mk _ _ _ _
      (derivedSquareUpperStarIso C sq).hom
    let : NatTrans.CommShift
        (mateEquiv (derivedUpperStarLowerStarAdjunction C a)
          (derivedUpperStarLowerStarAdjunction C a') θ).natTrans ℤ := by
      change NatTrans.CommShift (derivedBaseChangeMap C sq) ℤ
      exact commShift_derivedBaseChangeMap C sq
    exact shifted_constant_adjunct_mate (derivedUpperStarLowerStarAdjunction C a)
      (derivedUpperStarLowerStarAdjunction C a') (L(upperStar C g)) (L(upperStar C v))
      θ _ _ _ _ (genericConstantIso C M a).hom (genericConstantIso C M g).inv
      (genericConstantIso C M v).inv (genericConstantIso C M a').hom
      (genericConstantIso_square C M sq) (q : ℤ) x
  let h := (derivedUpperStarLowerStarAdjunction C a).homEquiv _ _
      ((genericConstantIso C M a).hom ≫ x) ≫
    ((R(lowerStar C a)).commShiftIso (q : ℤ)).hom.app K
  let h' := (derivedUpperStarLowerStarAdjunction C a').homEquiv _ _
      ((genericConstantIso C M a').hom ≫ (genericConstantIso C M v).inv ≫
        (L(upperStar C v)).map x ≫
        ((L(upperStar C v)).commShiftIso (q : ℤ)).hom.app K) ≫
    ((R(lowerStar C a')).commShiftIso (q : ℤ)).hom.app _
  have hh := kummer_adjunct_class C M sq K q x
  let : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory C g).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ ℤ
  have hc := iso_homology_class_constant (upperStar C g) (L(upperStar C g))
    (leftDerivedUpperStarIsoMapDerivedCategory C g)
    ((constantSheaf B.smallEtaleTopology C).obj M)
    ((constantSheaf B'.smallEtaleTopology C).obj M)
    ((Scheme.upperStarConstantSheafIso C g).inv.app M)
    ((R(lowerStar C a)).obj K)
    ((R(lowerStar C a')).obj ((L(upperStar C v)).obj K)) q h h'
    ((derivedBaseChangeMap C sq).app K) (by
      rw [kummerSingle_inv C M g] at hh
      simpa only [Category.assoc, h, h'] using hh)
  have higher_eq := isoWhiskerRight_map _ _ _
    (_root_.DerivedCategory.homologyFunctor _ (q : ℤ))
    (leftDerivedUpperStarIsoMapDerivedCategory C g)
    ((upperStar C g).mapDerivedCategoryHomologyFunctorIso (q : ℤ))
    ((R(lowerStar C a)).obj K) _ ((derivedBaseChangeMap C sq).app K)
  exact (congrArg
    (fun z ↦ (Scheme.upperStarConstantSheafIso C g).inv.app M ≫
      (upperStar C g).map
        ((_root_.DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app _ ≫
          (_root_.DerivedCategory.homologyFunctor _ 0).map h ≫
          ((_root_.DerivedCategory.homologyFunctor _ 0).shiftIso
            (q : ℤ) 0 (q : ℤ) (add_zero _)).hom.app _) ≫ z) higher_eq).trans hc

set_option backward.isDefEq.respectTransparency false

/-- Exchange preserves every normalized global edge section for the actual module map.
Source: blueprint Step 3; Stacks Tags 0736 and 072W
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: the exact pullback g^* commutes with H^0, with single-degree objects and with
shifts through its canonical comparisons, so g^* of the edge section of x is H^0 of the
pulled-back adjoint class (iso_homology_class_constant). The exchange is the mate of the
square comparison and commutes with shifts, so the pulled-back adjoint class followed by
the exchange is the a'-adjoint of the square comparison applied to the class
(shifted_adjunct_mate). The constant comparisons of g, a, v and a' are compatible with
the square comparison, since each is compatible with composition; hence that adjoint is
the a'-adjoint of v^*x. Applying H^0 and the shift comparison gives the edge section of
v^*x. No coefficients are forgotten. -/
theorem generic_relativeKummerExchange_edge (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology C) (q : ℕ)
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj (generic_kummerExchangeConstant C M X) ⟶
      (generic_kummerExchangeUpper C M a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)⟦(q : ℤ)⟧) :
    generic_kummerExchangeSectionPullback C M g (generic_kummerExchangeEdge C M a _ q x) ≫
        generic_kummerExchangeHigherMap C M sq _ (q : ℤ) =
      generic_kummerExchangeEdge C M a' _ q (generic_kummerExchangeClassPullback C M v _ q x)  := by
  let K := (L(upperStar C a)).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)
  have h := kummer_edge_naturality C M sq.toCommSq K q x
  exact (Category.assoc _ _ _).trans h

set_option backward.isDefEq.respectTransparency false

/-- The target Ra'_*v*a*L of the exchange, in the ordinary module-derived category.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable def generic_kummerExchangeTarget (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} (v : X' ⟶ X) (a' : X' ⟶ B') (a : X ⟶ B)
    (L₀ : Sheaf B.smallEtaleTopology C) :
    _root_.DerivedCategory (Sheaf B'.smallEtaleTopology C) :=
  (generic_kummerExchangeLower C M a').obj
    ((generic_kummerExchangeUpper C M v).obj
      ((generic_kummerExchangeUpper C M a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))

private theorem generic_kummerExchange_isIso_zero (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology C)
    (h₀ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((generic_kummerExchangeAdjunction C M a).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))))
    (h₀' : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((generic_kummerExchangeAdjunction C M a').unit.app
        ((generic_kummerExchangeUpper C M g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      (generic_kummerExchangeArrow C M sq
        ((generic_kummerExchangeUpper C M a).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))) := by
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf B'.smallEtaleTopology C) 0
  let η := (generic_kummerExchangeAdjunction C M a).unit.app
    ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)
  have hp : IsIso (H.map ((generic_kummerExchangeUpper C M g).map η)) :=
    (NatIso.isIso_map_iff
      (leftDerivedUpperStarHomologyFunctorIso C g 0) η).mp
      (by change IsIso ((upperStar C g).map _); infer_instance)
  have hu := congrArg H.map (generic_relativeKummerExchange_unit C M sq L₀)
  simp only [Functor.map_comp] at hu
  have : IsIso (H.map ((generic_kummerExchangeUpper C M g).map η) ≫
      H.map (generic_kummerExchangeArrow C M sq
        ((generic_kummerExchangeUpper C M a).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))) := by
    rw [hu]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map ((generic_kummerExchangeUpper C M g).map η)) _

private theorem generic_kummerExchange_isIso_vanishing
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology C) (i : ℤ)
    (h : IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (generic_kummerExchangeImage C M a L₀)) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (generic_kummerExchangeTarget C M v a' a L₀))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ i).map
      (generic_kummerExchangeArrow C M sq
        ((generic_kummerExchangeUpper C M a).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))) := by
  have hs := (Functor.map_isZero (upperStar C g) h.1).of_iso
    ((leftDerivedUpperStarHomologyFunctorIso C g i).app
      (generic_kummerExchangeImage C M a L₀)).symm
  exact ⟨⟨0, hs.eq_of_src _ _, h.2.eq_of_src _ _⟩⟩

/-- Two-degree criterion: normalized global generators and invertible degree-zero units
make the specified exchange invertible. No condition of finite type on g is imposed.
Source: blueprint Step 3; Stacks Tags 0736 and 072W
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: exact constant-ring pullback gives H^q(g*Ra_*F) = g*R^qa_*F. The unit identity
gives an invertible H^0 of exchange. The edge identity gives H^1(b) g*s = s' for the
two normalized generators s and s'. Equality of sections is equality of maps from the
constant rank-one module: evaluate on 1, use A-linearity for constant sections, and glue
locally constant sections. Consequently
H^1(b) = s' (g*s)^{-1}. Every other cohomology map is between zero objects. Apply
DerivedCategory.isIso_iff in the ordinary derived category. This uses no finiteness,
properness or torsion assumption on g. -/
theorem generic_relativeKummerExchange_generators
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology C)
    (h₀ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((generic_kummerExchangeAdjunction C M a).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))))
    (h₀' : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((generic_kummerExchangeAdjunction C M a').unit.app
        ((generic_kummerExchangeUpper C M g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))))
    (hvan : ∀ i : ℤ, i ≠ 0 → i ≠ 1 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (generic_kummerExchangeImage C M a L₀)) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (generic_kummerExchangeTarget C M v a' a L₀)))
    (x : (_root_.DerivedCategory.singleFunctor _ 0).obj (generic_kummerExchangeConstant C M X) ⟶
      (generic_kummerExchangeUpper C M a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)⟦(1 : ℤ)⟧)
    (hx : IsIso (generic_kummerExchangeEdge C M a _ 1 x))
    (hx' : IsIso (generic_kummerExchangeEdge C M a' _ 1
      (generic_kummerExchangeClassPullback C M v _ 1 x))) :
    IsIso (generic_kummerExchangeArrow C M sq
      ((generic_kummerExchangeUpper C M a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))) := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro i
  by_cases h0 : i = 0
  · subst i
    exact generic_kummerExchange_isIso_zero C M sq L₀ h₀ h₀'
  by_cases h1 : i = 1
  · subst i
    have he := generic_relativeKummerExchange_edge C M sq L₀ 1 x
    have : IsIso (generic_kummerExchangeSectionPullback C M g
        (generic_kummerExchangeEdge C M a _ 1 x)) := by
      dsimp only [generic_kummerExchangeSectionPullback]
      infer_instance
    have : IsIso (generic_kummerExchangeSectionPullback C M g
        (generic_kummerExchangeEdge C M a _ 1 x) ≫
        generic_kummerExchangeHigherMap C M sq _ (1 : ℤ)) := by
      exact he.symm ▸ hx'
    have : IsIso (generic_kummerExchangeHigherMap C M sq _ (1 : ℤ)) :=
      IsIso.of_isIso_comp_left
        (generic_kummerExchangeSectionPullback C M g (generic_kummerExchangeEdge C M a _ 1 x)) _
    dsimp only [generic_kummerExchangeHigherMap] at this
    exact IsIso.of_isIso_comp_left
      ((leftDerivedUpperStarHomologyFunctorIso C g 1).hom.app _) _
  · exact generic_kummerExchange_isIso_vanishing C M sq L₀ i (hvan i h0 h1)

/-- Degree-zero-only variant, without any degree-one class or generator hypothesis.
Source: blueprint Step 3; Stacks Tag 0736
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: the mate-unit identity and the two invertible degree-zero units identify H^0(b)
with their composite. Exact pullback preserves the vanishing of all other cohomology
sheaves. Thus every H^i(b) is invertible. The cohomological isomorphism
criterion DerivedCategory.isIso_iff in the ordinary derived category proves the claim. -/
theorem generic_relativeKummerExchange_degreeZero
    (C : Type u') [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (M : C)
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g)
    (L₀ : Sheaf B.smallEtaleTopology C)
    (h₀ : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((generic_kummerExchangeAdjunction C M a).unit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))))
    (h₀' : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((generic_kummerExchangeAdjunction C M a').unit.app
        ((generic_kummerExchangeUpper C M g).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀)))))
    (hvan : ∀ i : ℤ, i ≠ 0 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (generic_kummerExchangeImage C M a L₀)) ∧
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj
        (generic_kummerExchangeTarget C M v a' a L₀))) :
    IsIso (generic_kummerExchangeArrow C M sq
      ((generic_kummerExchangeUpper C M a).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L₀))) := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro i
  by_cases h0 : i = 0
  · subst i
    exact generic_kummerExchange_isIso_zero C M sq L₀ h₀ h₀'
  · exact generic_kummerExchange_isIso_vanishing C M sq L₀ i (hvan i h0)

set_option backward.isDefEq.respectTransparency true

/-- The existing exact derived inverse image, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeUpper (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeUpper (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The existing total derived direct image, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeLower (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeLower (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The canonical shift structure on exact derived inverse image, transported from
termwise inverse image using the existing comparison, as in Etale.Derived.Shift.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable instance kummerExchangeUpperCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeUpper A f).CommShift ℤ :=
  generic_kummerExchangeUpperCommShift (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The canonical adjoint shift structure on derived direct image, as in
Etale.Derived.Shift; no choice of a shift comparison is made.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable instance kummerExchangeLowerCommShift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (kummerExchangeLower A f).CommShift ℤ :=
  generic_kummerExchangeLowerCommShift (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The existing canonical derived adjunction, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeAdjunction (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeAdjunction (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- The specified module exchange, with its arguments fixed once.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeArrow (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_kummerExchangeArrow (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

/-- The constant free rank-one coefficient sheaf used to represent sections.
Source: Stacks Tag 072W and blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeConstant (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :=
  generic_kummerExchangeConstant (ModuleCat.{u + 1} A) (ModuleCat.of A A) T

/-- Exact pullback of a global class, with the canonical constant and shift comparisons.
This is the module-derived realization of cohomology pullback, without changing scalars.
Source: Stacks Tag 0736, resolution construction; blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeClassPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeClassPullback (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- Leray edge section: transpose the class under the actual derived adjunction, then
apply H⁰ and the canonical H⁰(K[q]) = H^q(K) comparison. On an injective representative
this sends a global cocycle to its class in the direct-image cohomology sheaf.
Source: Stacks Tag 072W, cycle-quotient proof; blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeEdge (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  generic_kummerExchangeEdge (ModuleCat.{u + 1} A) (ModuleCat.of A A) f

/-- Pullback of an edge section, including the canonical identification f* A_Y = A_X.
Source: blueprint Step 3; Stacks Tag 0736
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeSectionPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} :=
  generic_kummerExchangeSectionPullback (ModuleCat.{u + 1} A) (ModuleCat.of A A) f (G := G)

/-- H^q of the specified module-derived exchange, with exact inverse-image comparison.
Source: Stacks Tag 0736; blueprint Step 3
(blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeHigherMap (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_kummerExchangeHigherMap (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

/-- The direct image Ra_*a*L, with L placed in degree zero.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeImage (A : Type (u + 1)) [CommRing A]
    {X B : Scheme.{u}} (a : X ⟶ B) :=
  generic_kummerExchangeImage (ModuleCat.{u + 1} A) (ModuleCat.of A A) a

/-- The specified exchange preserves units after the canonical square identification.
Source: blueprint Step 3; Stacks Tag 0736
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: transpose both sides under a'^* ⊣ Ra'_*. Naturality of the square comparison
and the triangle identity turn the left transpose into theta_L; the right transpose
is theta_L by the other triangle identity. Injectivity of the adjunction gives equality. -/
noncomputable abbrev relativeKummerExchange_unit (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_unit (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

/-- Exchange preserves every normalized global edge section for the actual module map.
Source: blueprint Step 3; Stacks Tags 0736 and 072W
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: the exact pullback g^* commutes with H^0, with single-degree objects and with
shifts through its canonical comparisons, so g^* of the edge section of x is H^0 of the
pulled-back adjoint class (iso_homology_class_constant). The exchange is the mate of the
square comparison and commutes with shifts, so the pulled-back adjoint class followed by
the exchange is the a'-adjoint of the square comparison applied to the class
(shifted_adjunct_mate). The constant comparisons of g, a, v and a' are compatible with
the square comparison, since each is compatible with composition; hence that adjoint is
the a'-adjoint of v^*x. Applying H^0 and the shift comparison gives the edge section of
v^*x. No coefficients are forgotten. -/
noncomputable abbrev relativeKummerExchange_edge (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_edge (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

/-- The target Ra'_*v*a*L of the exchange, in the ordinary module-derived category.
Source: blueprint Step 3 (blueprint: lem-pur-relative-kummer-exchange-generators). -/
noncomputable abbrev kummerExchangeTarget (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} (v : X' ⟶ X) (a' : X' ⟶ B') (a : X ⟶ B) :=
  generic_kummerExchangeTarget (ModuleCat.{u + 1} A) (ModuleCat.of A A) v a' a

/-- Two-degree criterion: normalized global generators and invertible degree-zero units
make the specified exchange invertible. No condition of finite type on g is imposed.
Source: blueprint Step 3; Stacks Tags 0736 and 072W
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: exact constant-ring pullback gives H^q(g*Ra_*F) = g*R^qa_*F. The unit identity
gives an invertible H^0 of exchange. The edge identity gives H^1(b) g*s = s' for the
two normalized generators s and s'. Equality of sections is equality of maps from the
constant rank-one module: evaluate on 1, use A-linearity for constant sections, and glue
locally constant sections. Consequently
H^1(b) = s' (g*s)^{-1}. Every other cohomology map is between zero objects. Apply
DerivedCategory.isIso_iff in the ordinary derived category. This uses no finiteness,
properness or torsion assumption on g. -/
noncomputable abbrev relativeKummerExchange_generators (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_generators (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

/-- Degree-zero-only variant, without any degree-one class or generator hypothesis.
Source: blueprint Step 3; Stacks Tag 0736
(blueprint: lem-pur-relative-kummer-exchange-generators).
Proof: the mate-unit identity and the two invertible degree-zero units identify H^0(b)
with their composite. Exact pullback preserves the vanishing of all other cohomology
sheaves. Thus every H^i(b) is invertible. The cohomological isomorphism
criterion DerivedCategory.isIso_iff in the ordinary derived category proves the claim. -/
noncomputable abbrev relativeKummerExchange_degreeZero (A : Type (u + 1)) [CommRing A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {a' : X' ⟶ B'}
    {a : X ⟶ B} {g : B' ⟶ B} (sq : ChosenCartesianSquare v a' a g) :=
  generic_relativeKummerExchange_degreeZero (ModuleCat.{u + 1} A) (ModuleCat.of A A) sq

end AlgebraicGeometry.Etale
