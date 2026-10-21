/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalBicomplex

/-! # Coherent module-valued Čech direct-image models

Source: Stacks Project, sites-cohomology.tex, Tag 03FC; sites-modules.tex,
Tags 04IE and 04J4 (blueprint: def-sfb-coherent-cech-image-model).

The adjunction equations specify actual restrictions, including all simplicial operators.
The module categories and element-site restrictions are the recorded existing constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u vB uB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The canonical Čech nerve of the map from a sheaf to the terminal sheaf.
Source: Stacks 03FC (blueprint: def-sfb-coherent-cech-image-model). -/
def sheafCoverNerve {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (V : Sheaf J (Type u)) : SimplicialObject (Sheaf J (Type u)) :=
  (Arrow.mk (terminal.from V)).cechNerve

/-- A coherent presentation of `A ↦ j_A* j_A^*`, with every arrow fixed by adjunction.
The equation `restriction` transposes the indicated arrow to literal element-site
restriction of the first counit. The equation `unit` fixes the augmentation to the
localization unit, hence to restriction of sections. No arbitrary comparison map is used.

Source: Stacks 03FC, 04IE and 04J4 (blueprint: def-sfb-coherent-cech-image-model). -/
structure CoherentCechImageModel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) where
  /-- The actual module direct image of each element-site localization. -/
  push : ∀ A : Sheaf J (Type u),
    ringedSiteModules.{u} (elementRing R A) ⥤ ringedSiteModules.{u} R
  /-- Additivity of the module direct images. -/
  pushAdditive : ∀ A : Sheaf J (Type u), (push A).Additive
  /-- Its defining adjunction fixes the direct image up to unique isomorphism. -/
  adj : ∀ A : Sheaf J (Type u), elementModulePullback R A ⊣ push A
  /-- Continuity needed for the existing canonical relocalization functor. -/
  continuous : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    Functor.IsContinuous (elementMap b) (elementTopology B) (elementTopology A)
  /-- Simultaneous, contravariant functoriality in the sheaf being localized at. -/
  image : (Sheaf J (Type u))ᵒᵖ ⥤ ringedSiteModules.{u} R ⥤ ringedSiteModules.{u} R
  /-- Identification of each endofunctor with the actual localization composite. -/
  imageIso : ∀ A : Sheaf J (Type u),
    image.obj (op A) ≅ elementModulePullback R A ⋙ push A
  /-- The restriction map is the transpose of restriction of the localization counit. -/
  restriction : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A) (M : ringedSiteModules.{u} R),
    ((adj B).homEquiv _ _).symm
        ((image.map b.op).app M ≫ (imageIso B).hom.app M) =
      (elementModulePullbackOver R b (continuous b)).map
        (((adj A).homEquiv _ _).symm ((imageIso A).hom.app M))
  /-- The augmentation in every localization. -/
  augmentation : ∀ A : Sheaf J (Type u), 𝟭 _ ⟶ image.obj (op A)
  /-- Its adjoint is the identity, fixing the unit and the counit normalization. -/
  unit : ∀ (A : Sheaf J (Type u)) (M : ringedSiteModules.{u} R),
    ((adj A).homEquiv _ _).symm
      ((augmentation A).app M ≫ (imageIso A).hom.app M) = 𝟙 _
  /-- Compatibility of units with all restrictions, including refinements. -/
  augmentation_naturality : ∀ {A B : Sheaf J (Type u)} (b : B ⟶ A),
    augmentation A ≫ image.map b.op = augmentation B
  /-- Additivity of the actual Čech cochain functor, needed to apply it to resolutions. -/
  additive : ∀ V : Sheaf J (Type u),
    (((sheafCoverNerve V).rightOp ⋙ image).flip ⋙
      AlgebraicTopology.alternatingCofaceMapComplex (ringedSiteModules.{u} R)).Additive

attribute [instance] CoherentCechImageModel.pushAdditive

namespace CoherentCechImageModel

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (D : CoherentCechImageModel R)

/-- The alternating coface complex of the coherent localization diagram.
Source: Stacks 03FC (blueprint: def-sfb-coherent-cech-image-model). -/
def cochains (V : Sheaf J (Type u)) :
    ringedSiteModules.{u} R ⥤ CochainComplex (ringedSiteModules.{u} R) ℕ :=
  ((sheafCoverNerve V).rightOp ⋙ D.image).flip ⋙
    AlgebraicTopology.alternatingCofaceMapComplex (ringedSiteModules.{u} R)

/-- Additivity is part of the coherent presentation of this canonical construction.
Source: Stacks 03FC (blueprint: def-sfb-coherent-cech-image-model). -/
instance cochains_additive (V : Sheaf J (Type u)) : (D.cochains V).Additive :=
  D.additive V

/-- The actual covering-refinement map on Čech cochains, contravariant in the cover.
Source: Stacks 03FC (blueprint: def-sfb-coherent-cech-image-model). -/
def refinement {V W : Sheaf J (Type u)} (r : W ⟶ V) : D.cochains V ⟶ D.cochains W :=
  Functor.whiskerRight
    ((flipFunctor _ _ _).map (Functor.whiskerRight
      (Arrow.mapCechNerve
        (show Arrow.mk (terminal.from W) ⟶ Arrow.mk (terminal.from V) from
          Arrow.homMk r (𝟙 _) (terminal.hom_ext _ _))).rightOp D.image))
    (AlgebraicTopology.alternatingCofaceMapComplex (ringedSiteModules.{u} R))

/-- Apply direct image and exact inverse image to a single compatible resolution;
Čech degree is first, resolution degree second. Source: Stacks 03FC and Homology
Tag 0133 (blueprint: def-sfb-coherent-cech-image-model). -/
def bicomplex {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : ringedSiteModules.{u} R ⥤ B) [G.Additive] (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    HomologicalComplex₂ B (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.flip
    (((D.cochains V ⋙ G.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I)

/-- Functorial signed total on coherent resolutions, before extension by zero.
Source: Stacks 03FC, 0133 (blueprint: def-sfb-coherent-cech-image-model). -/
def totalFunctor {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : ringedSiteModules.{u} R ⥤ B) [G.Additive] (V : Sheaf J (Type u)) :
    CochainComplex (ringedSiteModules.{u} R) ℕ ⥤ CochainComplex B ℕ :=
  (D.cochains V ⋙ G.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
      (ComplexShape.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor B (ComplexShape.up ℕ) (ComplexShape.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor B (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)

/-- Total of the canonical covering-refinement map on one coherent resolution.
Source: Stacks 03FC (blueprint: def-sfb-coherent-cech-image-model). -/
def totalRefinement {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : ringedSiteModules.{u} R ⥤ B) [G.Additive]
    {V W : Sheaf J (Type u)} (r : W ⟶ V)
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ) :
    (D.totalFunctor G V).obj I ⟶ (D.totalFunctor G W).obj I :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor B (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map
      ((NatTrans.mapHomologicalComplex
        (Functor.whiskerRight (D.refinement r)
          (G.mapHomologicalComplex (ComplexShape.up ℕ))) (ComplexShape.up ℕ)).app I))
    (ComplexShape.up ℕ)

/-- The finite-diagonal total, extended by zero to an unbounded complex. Its total
sign is `d_Cech + (-1)^n d_res` in Čech degree `n`.
Source: Stacks 03FC and 0133 (blueprint: def-sfb-coherent-cech-image-model). -/
def total {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : ringedSiteModules.{u} R ⥤ B) [G.Additive] (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ) : CochainComplex B ℤ :=
  ((D.bicomplex G V I).total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat

/-- The normalization predicate fixes the entire chain augmentation, not only its
cohomology class: the localization unit is inserted in Čech degree zero.
Source: Stacks 03FC, 0133 (blueprint: def-sfb-coherent-cech-image-model). -/
def IsAugmentation {B : Type uB} [Category.{vB} B] [Abelian B]
    (G : ringedSiteModules.{u} R ⥤ B) [G.Additive] (V : Sheaf J (Type u))
    (I : CochainComplex (ringedSiteModules.{u} R) ℕ)
    (b : (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ⟶
      (D.bicomplex G V I).total (ComplexShape.up ℕ)) : Prop :=
  ∀ q : ℕ, b.f q = G.map
    ((D.augmentation ((sheafCoverNerve V).obj (op (SimplexCategory.mk 0)))).app (I.X q)) ≫
      (D.bicomplex G V I).ιTotal (ComplexShape.up ℕ) 0 q q (zero_add q)

end CoherentCechImageModel
end CategoryTheory
