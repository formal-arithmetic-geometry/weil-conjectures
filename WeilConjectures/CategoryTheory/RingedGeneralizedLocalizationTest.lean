/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedPresentationData

/-! # A derived localization test at a generalized ring section

Source: Stacks Project, Tags 04IE, 08JB and 0999.
(blueprint: def-weil-pbc-generalized-localization-test). -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- A generalized section gives an actual compatible ring section on its element site.
Source: Stacks Project, Tags 04IE and 0999.
(blueprint: def-weil-pbc-generalized-localization-test). -/
def presentationGeneralizedSection
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R))) :
    ((presentationElementRing R A).obj ⋙ forget CommRingCat).sections where
  val X := a.hom.app X.unop.unop.1 X.unop.unop.2
  property {X Y} f := by
    change R.obj.map f.unop.unop.1 (a.hom.app X.unop.unop.1 X.unop.unop.2) =
      a.hom.app Y.unop.unop.1 Y.unop.unop.2
    exact (NatTrans.naturality_apply a.hom f.unop.unop.1 X.unop.unop.2).symm.trans
      (congrArg (a.hom.app Y.unop.unop.1) f.unop.unop.2)

/-- Restrict a derived object to an arbitrary sheaf slice and test against localization
at its generalized ring section.
Source: Stacks Project, Tags 04IE, 08JB and 0999.
(blueprint: def-weil-pbc-generalized-localization-test). -/
def presentationGeneralizedTest
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (A : Sheaf J (Type u))
    (a : A ⟶ (presentationForget R).obj (SheafOfModules.unit (localCoefficientRings R)))
    (N : PresentationDerived R) : PresentationDerived (presentationElementRing R A) :=
  letI := HasDerivedCategory.standard (PresentationModules R)
  letI := HasDerivedCategory.standard (PresentationModules (presentationElementRing R A))
  (presentationRHom (presentationElementRing R A)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalizationOfUniverses (presentationElementRing R A)
        (presentationGeneralizedSection R A a))),
      (presentationDerivedMap (R := R) (S := presentationElementRing R A)
        (elementModulePullback.{u, u} (localCoefficientRings R) A)
        (presentationElementRestriction_additive R A)
        (presentationElementRestriction_exact R A).1
        (presentationElementRestriction_exact R A).2.1).obj N)

end CategoryTheory
