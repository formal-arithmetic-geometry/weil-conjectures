/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.DerivedSectionsScalarCoherence

/-! # Ringed-site sections and forgetting to abelian sheaves

Source: Stacks Project, Cohomology on Sites, Tag 0D6J,
lemma-modules-abelian-unbounded (1),(2), and Tag 0D6F
(blueprint: lem-sfb-ringed-sections-forget-abelian).

The comparison is a natural isomorphism of total unbounded derived functors,
normalized on every module K-injective and every abelian K-injective replacement.
The restriction square uses the derived actual presheaf restriction maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w z t

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSectionsForgetAbelian

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Evaluation of the underlying abelian sheaf at an object.
Source: Stacks, Tags 01FT and 0D6J
(blueprint: lem-sfb-ringed-sections-forget-abelian). -/
abbrev abelianEvaluation (U : C) : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- Actual restriction of sections along a site arrow, natural in the abelian sheaf.
Source: Stacks, Tag 0D6J, naturality of the displayed Gamma(U,a) maps
(blueprint: lem-sfb-ringed-sections-forget-abelian). -/
def abelianRestriction {V U : C} (f : V ⟶ U) :
    abelianEvaluation J U ⟶ abelianEvaluation J V :=
  Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{u})
    ((evaluation Cᵒᵖ AddCommGrpCat.{u}).map f.op)

variable {J} (B : Sheaf J CommRingCat.{u})

/-- The given commutative ring sheaf regarded as a ring sheaf; no coefficient change.
Source: Stacks, Tag 0D6J
(blueprint: lem-sfb-ringed-sections-forget-abelian). -/
abbrev rings : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B

/-- Sections of a module sheaf at an object with the module action forgotten: termwise
forgetting to the underlying abelian sheaf, followed by evaluation at the object.
Source: Stacks, Tags 01FT and 0D6J, the functor Gamma(U,-) on modules
(blueprint: lem-sfb-ringed-sections-forget-abelian). -/
abbrev moduleEvaluation (U : C) : ringedSiteModules.{u} (rings B) ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (rings B) ⋙ abelianEvaluation J U

/-- Actual restriction on module sections, with only the module action forgotten.
Source: Stacks, Tags 01FT and 0D6J
(blueprint: lem-sfb-ringed-sections-forget-abelian). -/
def moduleRestriction {V U : C} (f : V ⟶ U) :
    moduleEvaluation B U ⟶ moduleEvaluation B V :=
  Functor.whiskerLeft (SheafOfModules.toSheaf (rings B)) (abelianRestriction J f)

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} (rings B))]
  [HasDerivedCategory.{z} (Sheaf J AddCommGrpCat.{u})]
  [HasDerivedCategory.{t} AddCommGrpCat.{u}]

/-- Unbounded derived sections agree with those of the underlying abelian complex,
naturally in the derived argument and compatibly with the actual site restrictions.
For every module K-injective I and every quasi-isomorphism a from its underlying
abelian complex to an abelian K-injective A, the comparison is Gamma(U,a).

Source: Stacks Project, Tag 0D6J, lemma-modules-abelian-unbounded (1),(2)
(blueprint: lem-sfb-ringed-sections-forget-abelian).

Proof: (1) On C/U identify abelian sheaves with modules over the integer sheaf.
Integer multiples of one define its canonical map to B restricted to C/U, so
restriction of scalars is precisely forgetting the B-action. Localization is exact:
kernels restrict sectionwise and locally represented cokernel sections use the same covers.
(2) Choose a module K-injective I and an abelian K-injective replacement a: I_ab -> A
using prop-pur-kinjective-resolutions-exist. Both I and A restrict to K-injectives on
C/U by lem-pur-kinjective-restrict-localized; no K-injectivity of I_ab is asserted.
(3) Apply lem-coef-derived-sections-scalar-coherence on C/U with integer coefficients.
Its normalized comparison is represented by sections of a restricted to C/U and is
invertible. By lem-sfb-unbounded-sections-localization, evaluation at id_U is literally
evaluation at U, including the differentials. This gives the displayed formula for
every I, A and a. Quasi-isomorphisms become isomorphisms in the derived category.
(4) Naturality in K follows from the scalar and localization comparisons. For V -> U,
use the same I, a and A: a being a complex of sheaf maps makes the square with actual
restriction maps commute degreewise. Localization is sectionwise the identity, so
this is exactly the stated derived restriction square, independently of all choices. -/
theorem ringedSectionsForgetAbelian :
    ∃ e : ∀ U : C,
        (moduleEvaluation B U).rightDerivedFunctor ≅
          (SheafOfModules.toSheaf (rings B)).mapDerivedCategory ⋙
            (abelianEvaluation J U).rightDerivedFunctor,
      (∀ (U : C) (I : CochainComplex (ringedSiteModules.{u} (rings B)) ℤ)
          [I.IsKInjective] (A : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ)
          [A.IsKInjective]
          (a : ((SheafOfModules.toSheaf (rings B)).mapHomologicalComplex (.up ℤ)).obj I ⟶ A)
          [QuasiIso a],
        (e U).hom.app (DerivedCategory.Q.obj I) ≫
            (abelianEvaluation J U).rightDerivedFunctor.map
              ((SheafOfModules.toSheaf (rings B)).mapDerivedCategoryFactors.hom.app I) ≫
            (abelianEvaluation J U).rightDerivedFunctor.map (DerivedCategory.Q.map a) ≫
            ((abelianEvaluation J U).rightDerivedFunctorObjQIso A).hom =
          ((moduleEvaluation B U).rightDerivedFunctorObjQIso I).hom ≫
              DerivedCategory.Q.map
                (((abelianEvaluation J U).mapHomologicalComplex (.up ℤ)).map a)) ∧
      (∀ (V U : C) (f : V ⟶ U) (K : DerivedCategory (ringedSiteModules.{u} (rings B))),
        (Functor.rightDerivedFunctorNatTrans (moduleRestriction B f)).app K ≫
            (e V).hom.app K =
          (e U).hom.app K ≫
            (Functor.rightDerivedFunctorNatTrans (abelianRestriction J f)).app
              ((SheafOfModules.toSheaf (rings B)).mapDerivedCategory.obj K)) := by
  sorry

end CategoryTheory.RingedSectionsForgetAbelian
