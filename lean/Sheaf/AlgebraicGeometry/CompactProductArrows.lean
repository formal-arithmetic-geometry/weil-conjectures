/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-! # Compact exterior-product arrows

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section GenericPullback

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]

/-- Derived sections of extension by zero on the specified compactification.
Source: blueprint Step 1, compact-support convention
(blueprint: def-pur-compact-product-arrows). -/
abbrev compactProductSections {X B : Scheme.{u}} {f : X ⟶ B}
    (c : Compactification f) :=
  (openImmersionLowerShriek C c.i).mapDerivedCategory ⋙
    rightDerivedGlobalSections C c.Z

/-- Exact inverse image in fixed-coefficient coordinates.
Source: blueprint Step 1, projection pullbacks
(blueprint: def-pur-compact-product-arrows). -/
abbrev compactProductPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar C f).mapDerivedCategory

/-- The canonical composition comparison of exact inverse images.
Source: blueprint Step 1, projection pullbacks
(blueprint: def-pur-compact-product-arrows). -/
def compactProductPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z := f ≫ g) (w : h = f ≫ g := by cat_disch) :
    compactProductPullback C h ≅ compactProductPullback C g ⋙ compactProductPullback C f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp C f g h w) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end GenericPullback

/-- The product of the two compactifying open maps, using the specified structure maps.
Source: blueprint Step 1, product compactification
(blueprint: def-pur-compact-product-arrows). -/
def compactProductOpenMap {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g) : pullback f g ⟶ pullback c.g d.g :=
  pullback.map f g c.g d.g c.i d.i (𝟙 B) (by simp [c.comm]) (by simp [d.comm])

/-- First projection of the product open map.
Source: blueprint Step 1, product compactification
(blueprint: def-pur-compact-product-arrows).
Proof: this is the first projection identity of the pullback lift defining the map. -/
theorem compactProductOpenMap_fst {B X Y : Scheme.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} (c : Compactification f) (d : Compactification g) :
    compactProductOpenMap c d ≫ pullback.fst c.g d.g = pullback.fst f g ≫ c.i := by
  sorry

/-- Second projection of the product open map.
Source: blueprint Step 1, product compactification
(blueprint: def-pur-compact-product-arrows).
Proof: this is the second projection identity of the pullback lift defining the map. -/
theorem compactProductOpenMap_snd {B X Y : Scheme.{u}}
    {f : X ⟶ B} {g : Y ⟶ B} (c : Compactification f) (d : Compactification g) :
    compactProductOpenMap c d ≫ pullback.snd c.g d.g = pullback.snd f g ≫ d.i := by
  sorry

/-- The product of the two compactifying open immersions is open.
Source: blueprint Step 1, product compactification
(blueprint: def-pur-compact-product-arrows).
Proof: factor the product map as the two base changes of the open immersions.
Open immersions are stable under base change and composition. -/
@[instance]
theorem compactProductOpen {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g) :
    IsOpenImmersion (compactProductOpenMap c d) := by
  sorry

/-- The actual product compactification, with its literal fibre-product middle scheme.
Source: blueprint Step 1, product compactification
(blueprint: def-pur-compact-product-arrows). -/
def compactProductCompactification {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g) :
    Compactification (pullback.toBase f g) where
  Z := pullback c.g d.g
  g := pullback.toBase c.g d.g
  i := compactProductOpenMap c d
  comm := by
    dsimp only [pullback.toBase]
    simp only [compactProductOpenMap, pullback.map, pullback.lift_fst_assoc,
      Category.assoc, ← c.comm]
  isProper := by
    change IsProper (pullback.fst c.g d.g ≫ c.g)
    infer_instance
  isOpenImmersion := compactProductOpen c d

section GenericPullback

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]

/-- Canonical restriction of one pulled-back extended factor to the product open.
Source: blueprint Step 1, extension-by-zero exterior comparison
(blueprint: def-pur-compact-product-arrows). -/
def compactProductProjectionRestriction {X Y U V : Scheme.{u}}
    (p : U ⟶ X) (q : V ⟶ Y) (j : X ⟶ Y) [IsOpenImmersion j]
    (v : U ⟶ V) (w : v ≫ q = p ≫ j)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (compactProductPullback C v).obj
        ((upperStar C q).leftDerivedFunctor.obj
          ((openImmersionLowerShriek C j).mapDerivedCategory.obj K)) ≅
      (upperStar C p).leftDerivedFunctor.obj K :=
  (compactProductPullback C v).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory C q).app _) ≪≫
    (compactProductPullbackComp C v q).symm.app _ ≪≫
    (compactProductPullbackComp C p j (v ≫ q) w).app _ ≪≫
    (compactProductPullback C p).mapIso
      (asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        C j).unit.app K)).symm ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory C p).symm.app K

/-- The canonical tensor comparison for exact inverse image.
Source: blueprint Step 1, K-flat tensor comparison
(blueprint: def-pur-compact-product-arrows). -/
def compactProductPullbackTensor {X Y : Scheme.{u}} (p : X ⟶ Y)
    (K L : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (compactProductPullback C p).obj
        (((derivedTensor C Y).obj K).obj L) ≅
      ((derivedTensor C X).obj
        ((compactProductPullback C p).obj K)).obj ((compactProductPullback C p).obj L) :=
  (leftDerivedUpperStarIsoMapDerivedCategory C p).symm.app _ ≪≫
    leftDerivedUpperStarTensorIso C p K L ≪≫
    ProEtale.supportBifunctorIso (derivedTensor C X)
      ((leftDerivedUpperStarIsoMapDerivedCategory C p).app K)
      ((leftDerivedUpperStarIsoMapDerivedCategory C p).app L)

/-- Restriction of a tensor of two zero extensions through two commuting projection
squares, with the schemes kept as variables so the derived tensor instances stay shared.
Source: blueprint Step 1, extension-by-zero exterior comparison
(blueprint: def-pur-compact-product-arrows). -/
def compactProductRestrictionCore {X Y Xbar Ybar U V : Scheme.{u}}
    (j : X ⟶ Xbar) (k : Y ⟶ Ybar) [IsOpenImmersion j] [IsOpenImmersion k]
    (a : U ⟶ X) (b : U ⟶ Y) (p : V ⟶ Xbar) (q : V ⟶ Ybar) (v : U ⟶ V)
    (wa : v ≫ p = a ≫ j) (wb : v ≫ q = b ≫ k)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :=
  compactProductPullbackTensor C v
    ((upperStar C p).leftDerivedFunctor.obj
      ((openImmersionLowerShriek C j).mapDerivedCategory.obj K))
    ((upperStar C q).leftDerivedFunctor.obj
      ((openImmersionLowerShriek C k).mapDerivedCategory.obj L)) ≪≫
    ProEtale.supportBifunctorIso (derivedTensor C U)
      (compactProductProjectionRestriction C a p j v wa K)
      (compactProductProjectionRestriction C b q k v wb L)

/-- Type of the whole canonical restriction family. Keeping this type atomic
shares the coefficient structures when the family is instantiated at product schemes.
Source: blueprint Step 1, extension-by-zero exterior comparison
(blueprint: def-pur-compact-product-arrows). -/
def CompactProductRestrictionFamily : Type (max v (u + 1)) :=
  ∀ {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)),
    (compactProductPullback C (compactProductOpenMap c d)).obj
        (externalProduct C c.g d.g
          ((openImmersionLowerShriek C c.i).mapDerivedCategory.obj K)
          ((openImmersionLowerShriek C d.i).mapDerivedCategory.obj L)) ≅
      externalProduct C f g K L

/-- Existence and uniqueness of the canonical restriction family with its explicit
pullback-tensor normalization. Source: blueprint Step 1, exterior comparison
(blueprint: def-pur-compact-product-arrows).
Proof: the displayed canonical pullback-tensor composite gives each component.
Equality with those components determines the entire family by function extensionality. -/
structure CompactProductRestrictionFamilyData where
  map : CompactProductRestrictionFamily C
  normalization :
      ∀ {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
        (c : Compactification f) (d : Compactification g)
        (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
        (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)),
        map c d K L =
          compactProductRestrictionCore C c.i d.i (pullback.fst f g) (pullback.snd f g)
            (pullback.fst c.g d.g) (pullback.snd c.g d.g) (compactProductOpenMap c d)
            (compactProductOpenMap_fst c d) (compactProductOpenMap_snd c d) K L

/-- The normalized comparison data exist and determine their map by equality
with every displayed canonical component. Source: blueprint Step 1, compact arrows
(blueprint: def-pur-compact-product-arrows).
Proof: assemble the explicit canonical components, whose equalities are reflexive.
Every possible choice has those same components, so its map is uniquely determined. -/
theorem compactProductRestriction_exists_normalized :
    Nonempty (CompactProductRestrictionFamilyData C) := by
  sorry

/-- The unique canonical zero-extension restriction family, determined by the
explicit pullback-tensor comparison. Source: blueprint Step 1, exterior comparison
(blueprint: def-pur-compact-product-arrows). -/
def compactProductRestriction : CompactProductRestrictionFamily C :=
  (Classical.choice (compactProductRestriction_exists_normalized C)).map

/-- The zero-extension exterior comparison, defined by the open-adjunction mate of
`compactProductRestriction`. It is therefore fixed by the ordinary section construction.
Source: blueprint Step 1, extension-by-zero exterior comparison
(blueprint: def-pur-compact-product-arrows). -/
def compactProductExtension {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction C
    (compactProductOpenMap c d)).homEquiv _ _).symm
      (compactProductRestriction C c d K L).inv

/-- The canonical zero-extension exterior comparison is invertible.
Source: blueprint Step 1, extension-by-zero exterior comparison
(blueprint: def-pur-compact-product-arrows).
Proof: on the product open it is the identity under the open-adjunction unit.
Outside that open at least one factor stalk vanishes. The K-flat stalk tensor formula
therefore makes the comparison an isomorphism on all geometric stalks. Exact conservative
geometric stalks detect its invertibility after localization. -/
@[instance]
theorem compactProductExtension_isIso {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    IsIso (compactProductExtension C c d K L) := by
  sorry

/-- Compose the global exterior-product arrow with the inverse of the specified
zero-extension comparison, keeping its middle schemes abstract.
Source: blueprint Step 1, compact Kunneth construction
(blueprint: def-pur-compact-product-arrows). -/
def compactProductMapCore {X Y Z U : Scheme.{u}}
    (p : Z ⟶ X) (q : Z ⟶ Y) (j : U ⟶ Z) [IsOpenImmersion j]
    [(constantSheaf Z.smallEtaleTopology C).Monoidal]
    [(constantSheaf Z.smallEtaleTopology C).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (F : DerivedCategory (Sheaf U.smallEtaleTopology C))
    (e : (openImmersionLowerShriek C j).mapDerivedCategory.obj F ⟶
      ((derivedTensor C Z).obj ((upperStar C p).leftDerivedFunctor.obj K)).obj
        ((upperStar C q).leftDerivedFunctor.obj L)) [IsIso e] :=
  ordinaryGlobalKunnethMap C p q K L ≫ (rightDerivedGlobalSections C Z).map (inv e)

/-- Type of compact exterior-product families on specified compactifications.
Source: blueprint Step 1, compact Kunneth construction
(blueprint: def-pur-compact-product-arrows). -/
def CompactProductMapFamily : Type (max v (u + 1)) :=
  ∀ {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (c : Compactification f) (d : Compactification g)
    [(constantSheaf (pullback c.g d.g).smallEtaleTopology C).Monoidal]
    [(constantSheaf (pullback c.g d.g).smallEtaleTopology C).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)),
    (compactProductSections C c).obj K ⊗ (compactProductSections C d).obj L ⟶
      (compactProductSections C (compactProductCompactification c d)).obj
        (externalProduct C f g K L)

/-- The compact exterior family is uniquely normalized by the ordinary exterior
arrow on the zero extensions and the inverse of their canonical comparison.
Source: blueprint Step 1, compact Kunneth construction
(blueprint: def-pur-compact-product-arrows).
Proof: use the displayed ordinary exterior composite at every pair of inputs.
Equality with each component determines the family by function extensionality. -/
structure CompactProductMapFamilyData where
  map : CompactProductMapFamily C
  normalization :
      ∀ {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
        (c : Compactification f) (d : Compactification g)
        [(constantSheaf (pullback c.g d.g).smallEtaleTopology C).Monoidal]
        [(constantSheaf (pullback c.g d.g).smallEtaleTopology C).PreservesFlat]
        (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
        (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)),
        map c d K L =
          compactProductMapCore C (pullback.fst c.g d.g) (pullback.snd c.g d.g)
            (compactProductOpenMap c d)
            ((openImmersionLowerShriek C c.i).mapDerivedCategory.obj K)
            ((openImmersionLowerShriek C d.i).mapDerivedCategory.obj L)
            (externalProduct C f g K L) (compactProductExtension C c d K L)

/-- The normalized comparison data exist and determine their map by equality
with every displayed canonical component. Source: blueprint Step 1, compact arrows
(blueprint: def-pur-compact-product-arrows).
Proof: assemble the explicit canonical components, whose equalities are reflexive.
Every possible choice has those same components, so its map is uniquely determined. -/
theorem compactProductMap_exists_normalized : Nonempty (CompactProductMapFamilyData C) := by
  sorry

/-- The compact exterior arrow with its uniquely specified ordinary-arrow
normalization. Source: blueprint Step 1, compact Kunneth construction
(blueprint: def-pur-compact-product-arrows). -/
def compactProductMap : CompactProductMapFamily C :=
  (Classical.choice (compactProductMap_exists_normalized C)).map

end GenericPullback

section GenericPullback

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]

/-- The map of exterior products induced by two morphisms of complexes.
Source: blueprint Step 1, naturality in the two inputs
(blueprint: def-pur-compact-product-arrows). -/
def compactProductExternalMap {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology C)}
    {L L' : DerivedCategory (Sheaf Y.smallEtaleTopology C)}
    (α : K ⟶ K') (β : L ⟶ L') :
    externalProduct C f g K L ⟶
      externalProduct C f g K' L' :=
  ((derivedTensor C (pullback f g)).map
    ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map α)).app _ ≫
    ((derivedTensor C (pullback f g)).obj _).map
      ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map β)

end GenericPullback

end AlgebraicGeometry.Etale
