/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.CategoryTheory.RingedPresentationData
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.SixFunctors.OpenTensorNormalizationData
public import Mathlib.CategoryTheory.Subterminal

/-! # Scalar balancing for an arbitrary open subtopos, with its actual unit

Source: Stacks Project, sites-cohomology.tex, Tag 0GL1, and sites-modules.tex,
Tags 0E8I and 04IE (blueprint: def-pur-topos-open-scalar-section-data).
The statement is the coefficient-linear, unit-normalized refinement of 0GL1.
A fixed small presentation identifies the topos with sheaves; the subterminal need
not be represented on that site. Its slice is the existing category-of-elements site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace SheafOfModules.ToposOpenScalar

attribute [local instance 0] hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize

/-- The coefficient map on the same element site.
Source: Stacks 04IE (blueprint: def-pur-topos-open-scalar-section-data). -/
def sliceMap {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J (Type u)) {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S) :
    presentationElementRing R A ⟶ presentationElementRing S A :=
  ObjectProperty.homMk (Functor.whiskerLeft (elementProjection A).op a.hom)

/-- The recorded restriction, with its definitionally equal commutative-ring endpoint exposed.
Source: Stacks 04IE (blueprint: def-pur-topos-open-scalar-section-data). -/
abbrev restriction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R) ⥤
      ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients
        (elementTopology A) (presentationElementRing R A)) :=
  elementModulePullback.{u, u} (derivedChangeRingIndependentCoefficients J R) A

/-- The recorded sheafified extension, with the same normalized ring endpoint.
Source: Stacks 04IE (blueprint: def-pur-topos-open-scalar-section-data). -/
abbrev extension {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients
        (elementTopology A) (presentationElementRing R A)) ⥤
      ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R) :=
  elementModuleExtension.{u} (derivedChangeRingIndependentCoefficients J R) A

/-- The actual extension/restriction adjunction of the element-site construction.
Source: Stacks 04IE (blueprint: def-pur-topos-open-scalar-section-data). -/
abbrev adjunction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :=
  SheafOfModules.pullbackPushforwardAdjunction.{u, u, u, u, u, u}
    (R := derivedChangeRingIndependentCoefficients J R)
    (S := elementRing (derivedChangeRingIndependentCoefficients J R) A)
    (F := elementProjection A)
    (𝟙 (elementRing (derivedChangeRingIndependentCoefficients J R) A))

/-- The same fixed adjunction, with the ringed-site endpoints explicitly normalized.
Source: Stacks 04IE (blueprint: def-pur-topos-open-scalar-section-data). -/
def normalizedAdjunction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u)) :
    extension R A ⊣ restriction R A := adjunction R A

/-- A pure tensor in the sheafified scalar extension, transported by its prescribed object
identification. The scalar is written first because Mathlib uses the left S-action.
Source: Stacks 03EK (blueprint: def-pur-topos-open-scalar-section-data). -/
def tensorSection {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u}} (a : R ⟶ S)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients J S))]
    (E : DerivedChangeOfRingsCochainModel.{u, u, u, w, w} a)
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))
    (U : Cᵒᵖ) (m : M.val.obj U) (s : S.obj.obj U) : (E.E.obj M).val.obj U :=
  (eqToHom (E.obj_eq M).symm).val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} a M)).app U
      (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m))

/-- The original extension summand, expressed by the actual extension-adjunction unit.
Source: Stacks 04IE (blueprint: def-pur-topos-open-scalar-section-data). -/
def extensionSection {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (M : ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients
      (elementTopology A) (presentationElementRing R A)))
    (U : Cᵒᵖ) (f : A.obj.obj U) (m : M.val.obj (elementObj A U f)) :
    ((extension R A).obj M).val.obj U :=
  ((normalizedAdjunction R A).unit.app M).val.app (elementObj A U f) m

end SheafOfModules.ToposOpenScalar
