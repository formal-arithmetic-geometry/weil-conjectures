/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Localization and multiplication by a section on a slice ringed site

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af;
Modules on Sites, Tags 03DI and 03DJ
(blueprint: def-weil-pbc-local-coefficient-localization).
-/

@[expose] public noncomputable section

universe u w wSlice

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The ring sheaf underlying the given commutative ring sheaf.
Source: Stacks Project, Modules on Sites, ringed sites
(blueprint: def-weil-pbc-local-coefficient-localization). -/
abbrev localCoefficientRings {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

/-- Forgetting commutativity commutes definitionally with restriction. This instance
exposes that equality to typeclass search for the derived category of the slice.
Source: Stacks Project, localized ringed sites
(blueprint: def-weil-pbc-local-coefficient-localization). -/
instance localCoefficientOver_hasDerivedCategory {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    [h : HasDerivedCategory.{w} (ringedSiteModules.{u} ((localCoefficientRings R).over U))] :
    HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings (R.over U))) := h

/-- Multiplication by the restrictions of `f` on an arbitrary module on the slice.
Source: Stacks Project, Tag 0997, lemma-hom-from-Af
(blueprint: def-weil-pbc-local-coefficient-localization). -/
def localSectionMultiplication {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U))
    (M : ringedSiteModules.{u} ((localCoefficientRings R).over U)) : M ⟶ M where
  val := PresheafOfModules.sectionsSMul
    (S := (Over.forget U).op ⋙ R.obj) M.val
    (PresheafOfModules.overSections (R := R.obj) U f)

/-- The localized coefficient module, constructed as the colimit of repeated multiplication
by `f` on the unit module. Sectionwise before sheafification this colimit sends the class of
`a` at stage `n` to `a/f^n`, hence is precisely the sheafification of sectionwise localization.
Source: Stacks Project, Tag 0997, lemma-hom-from-Af
(blueprint: def-weil-pbc-local-coefficient-localization). -/
def localCoefficientLocalization {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    ringedSiteModules.{u} ((localCoefficientRings R).over U) :=
  colimit (Functor.ofSequence
    (X := fun _ : ℕ ↦ SheafOfModules.unit ((localCoefficientRings R).over U))
    (fun _ ↦ localSectionMultiplication R U f _))

/-- Restriction of module sheaves to the slice is additive and exact.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(blueprint: def-weil-pbc-local-coefficient-localization).
Proof: restrictions are sectionwise, so preserve addition and kernels. A locally surjective
map remains locally surjective on the induced slice topology, so restriction preserves
cokernels as well. Additivity and preservation of kernels and cokernels imply preservation
of finite limits and finite colimits. -/
theorem localCoefficientRestriction_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C) :
    (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).Additive ∧
      PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U) ∧
      PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U) := by
  sorry

/-- Restriction on the derived categories, induced by exact module restriction.
Source: Stacks Project, Modules on Sites, Tags 03DI and 03DJ
(blueprint: def-weil-pbc-local-coefficient-localization). -/
def localCoefficientDerivedRestriction {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))] :
    DerivedCategory (ringedSiteModules.{u} (localCoefficientRings R)) ⥤
      DerivedCategory (ringedSiteModules.{u} ((localCoefficientRings R).over U)) :=
  haveI := (localCoefficientRestriction_exact R U).1
  haveI := (localCoefficientRestriction_exact R U).2.1
  haveI := (localCoefficientRestriction_exact R U).2.2
  (SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).mapDerivedCategory

/-- Naturality of multiplication by a section on localized module sheaves.
Source: Stacks Project, Tag 0997, lemma-hom-from-Af
(blueprint: def-weil-pbc-local-coefficient-localization).
Proof: on each object of the slice both composites take `x` to `f` times its image;
linearity of the component map gives the equality. -/
theorem localSectionMultiplication_naturality {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U))
    {M N : ringedSiteModules.{u} ((localCoefficientRings R).over U)} (g : M ⟶ N) :
    g ≫ localSectionMultiplication R U f N = localSectionMultiplication R U f M ≫ g := by
  sorry

/-- Multiplication by `f` as a natural endomorphism of slice restriction.
Source: Stacks Project, Tag 0997, lemma-hom-from-Af
(blueprint: def-weil-pbc-local-coefficient-localization). -/
def localSectionMultiplicationNatTrans {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U)) :
    SheafOfModules.overFunctor.{u} (localCoefficientRings R) U ⟶
      SheafOfModules.overFunctor.{u} (localCoefficientRings R) U where
  app M := localSectionMultiplication R U f
    ((SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).obj M)
  naturality {_M _N} g := localSectionMultiplication_naturality R U f
    ((SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).map g)

/-- Multiplication by `f` after localization of the category of complexes.
Source: Stacks Project, Tag 0997, lemma-hom-from-Af
(blueprint: def-weil-pbc-local-coefficient-localization). -/
def localSectionDerivedMultiplication {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) (U : C)
    (f : R.obj.obj (op U))
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{wSlice} (ringedSiteModules.{u} ((localCoefficientRings R).over U))] :
    localCoefficientDerivedRestriction R U ⟶ localCoefficientDerivedRestriction R U :=
  haveI := (localCoefficientRestriction_exact R U).1
  haveI := (localCoefficientRestriction_exact R U).2.1
  haveI := (localCoefficientRestriction_exact R U).2.2
  haveI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      ((SheafOfModules.overFunctor.{u} (localCoefficientRings R) U).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) (localCoefficientDerivedRestriction R U) :=
    ⟨(SheafOfModules.overFunctor.{u}
      (localCoefficientRings R) U).mapDerivedCategoryFactors⟩
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (localSectionMultiplicationNatTrans R U f) (ComplexShape.up ℤ)) DerivedCategory.Q)

end CategoryTheory
