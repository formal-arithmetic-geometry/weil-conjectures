/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.DerivedSectionsScalarCoherence
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-! # Global module cohomology and underlying abelian cohomology

Source: Stacks Project, sites-cohomology.tex, Tag 03FD, global equality in
lemma-cohomology-modules-abelian-agree
(blueprint: lem-sfb-ringed-site-global-module-abelian-cohomology).

The right derived functor and its unit are explicit parameters, so the comparison
applies to any presentation of the unbounded derived global sections functor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u w z
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.CoefficientDerivedSections

/-- Global module cohomology agrees naturally and additively with global cohomology
of the underlying abelian sheaf. The augmentation equation normalizes degree zero
as the identity on compatible section families. The final equation expresses
linearity for the action of global ring sections on both sides. The resolution
formula characterizes the canonical comparison on every compatible resolution lift.

Source: Stacks Project, sites-cohomology.tex, Tag 03FD, global equality
(blueprint: lem-sfb-ringed-site-global-module-abelian-cohomology).

Proof:
1. Modules over the constant integer sheaf are abelian sheaves. Locally integer
sections are represented by integers, by lem-weil-pbc-site-sheafification-sections-local.
Their action glues uniquely, including over objects with an empty covering. This
constructs the equivalence, whose inverse forgets the integer action.
2. Apply lem-coef-derived-sections-scalar-coherence to the constant-integer map to R.
It identifies module-derived sections with integer-module-derived sections after
restriction. Its unit equation normalizes the underived compatible families.
3. Resolve the underlying abelian sheaf by injectives, using
lem-weil-pbc-site-sheaves-enough-injectives and def-sp-injective-resolutions.
The integer-module equivalence preserves injectivity by
lem-weil-pbc-equivalence-injective-resolutions. The resulting bounded below complex
is K-injective by lem-weil-pbc-bounded-below-injectives-kinjective. Thus it computes
both integer-module-derived sections and abelian right derived sections, as in
def-pur-ringed-site-zeroth-hypercohomology. Resolution lifts from
lem-weil-pbc-injective-resolution-lift-exists and their map formula from
lem-weil-pbc-derived-functor-map-via-lift give naturality and independence of choices.
4. Take homology of the normalized comparison of step 2 and compose with step 3.
In degree zero the augmentation identifies the cycles with the original compatible
families, and the unit equation gives the displayed identity. Naturality for the
module endomorphism multiplying by a global ring section gives the final equation.
No flatness or injectivity of the forgotten module is used. -/
theorem global_module_abelian_cohomology
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (coefficientModules R)]
    [HasDerivedCategory.{z} AddCommGrpCat.{u}]
    (H : DerivedCategory (coefficientModules R) ⥤ DerivedCategory AddCommGrpCat.{u})
    (η : coefficientComplexSections R ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ H)
    [H.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (coefficientModules R) (ComplexShape.up ℤ))] :
    ∃ e : ∀ n : ℕ,
      DerivedCategory.singleFunctor (coefficientModules R) 0 ⋙ H ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ) ≅
        SheafOfModules.toSheaf _ ⋙ (Sheaf.Γ J AddCommGrpCat.{u}).rightDerived n,
      (∀ F : coefficientModules R,
        (HomologicalComplex.homologyFunctorSingleIso AddCommGrpCat.{u}
            (ComplexShape.up ℤ) 0).inv.app ((coefficientSections R).obj F) ≫
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).map
            ((HomologicalComplex.singleMapHomologicalComplex (coefficientSections R)
              (ComplexShape.up ℤ) 0).inv.app F) ≫
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).inv.app
            ((coefficientComplexSections R).obj
              ((CochainComplex.singleFunctor (coefficientModules R) 0).obj F)) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            (η.app ((CochainComplex.singleFunctor (coefficientModules R) 0).obj F)) ≫
          (e 0).hom.app F =
            (Sheaf.Γ J AddCommGrpCat.{u}).toRightDerivedZero.app
              ((SheafOfModules.toSheaf _).obj F)) ∧
      (∀ (n : ℕ) (F : coefficientModules R)
        (a : RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)),
        (DerivedCategory.singleFunctor (coefficientModules R) 0 ⋙ H ⋙
            DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).map
              (SheafOfModules.Hom.mk (PresheafOfModules.sectionsSMul F.val a)) ≫
          (e n).hom.app F =
        (e n).hom.app F ≫
          ((Sheaf.Γ J AddCommGrpCat.{u}).rightDerived n).map
            ((SheafOfModules.toSheaf _).map
              (SheafOfModules.Hom.mk (PresheafOfModules.sectionsSMul F.val a)))) ∧
      ∀ (F : coefficientModules R) (I : InjectiveResolution F)
        (K : InjectiveResolution ((SheafOfModules.toSheaf _).obj F))
        (φ : ((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.cochainComplex ⟶ K.cochainComplex),
        (HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.toSheaf _)
            (ComplexShape.up ℤ) 0).inv.app F ≫
          ((SheafOfModules.toSheaf _).mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι' ≫
            φ = K.ι' → ∀ n : ℕ,
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).map
            (η.app I.cochainComplex) ≫
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).map
            (H.map (inv (DerivedCategory.Q.map I.ι'))) ≫
          (e n).hom.app F ≫
          (K.isoRightDerivedObjCochainComplex (Sheaf.Γ J AddCommGrpCat.{u}) n).hom =
        (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} (n : ℤ)).hom.app
            ((coefficientComplexSections R).obj I.cochainComplex) ≫
          HomologicalComplex.homologyMap
            (((Sheaf.Γ J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map φ)
            (n : ℤ) := by
  sorry

end CategoryTheory.CoefficientDerivedSections
