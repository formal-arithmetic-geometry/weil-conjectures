module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Topology.OpenModuleDerivedSections
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Hypercohomology presheaves on a ringed space

Source: Stacks Project, Cohomology, Tags 0D5V and 0D66
(blueprint: def-trf-ringed-space-hypercohomology-presheaf).

Derive the underlying abelian presheaf functor, then take presheaf cohomology.
This retains the restriction maps from a single global K-injective representative.
The last definition is the ordinary-to-derived unit on a module in degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The underlying abelian presheaf of a module sheaf. Source: Stacks, Modules,
Section 01AF (blueprint: def-trf-ringed-space-hypercohomology-presheaf). -/
abbrev moduleAbelianPresheaf (X : RingedSpace.{u}) :
    CategoryTheory.ringedSiteModules.{u} (moduleRings X) ⥤
      ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  SheafOfModules.forget (moduleRings X) ⋙
    PresheafOfModules.toPresheaf (moduleRings X).obj

variable (X : RingedSpace.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]

/-- Unbounded derived underlying abelian presheaves, using the universal right-derived
pair of def-sfb-right-derived-functor. The target localization uses the standard size.
Source: Stacks, Tag 0D5V
(blueprint: def-trf-ringed-space-hypercohomology-presheaf). -/
def derivedModuleAbelianPresheaf :
    DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      @DerivedCategory ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) _ _
        (HasDerivedCategory.standard _) :=
  letI := HasDerivedCategory.standard ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (moduleAbelianPresheaf X).rightDerivedFunctorOfQuasiIsoResolutions
    (fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K,
      (CochainComplex.toKInjectiveResolution.{u} _).app K, inferInstance,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2⟩)

/-- The abelian presheaf V ↦ Hⁿ(RΓ(V,E)); restriction and derived morphisms are induced
by the termwise section maps on K-injectives. Evaluation is exact on presheaves, so
cohomology here is the cohomology of derived evaluation, including on the empty open.
Source: Stacks, Tags 0D5V and 0D66
(blueprint: def-trf-ringed-space-hypercohomology-presheaf). -/
def ringedSpaceHypercohomologyPresheaf (n : ℤ) :
    DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  letI := HasDerivedCategory.standard ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  derivedModuleAbelianPresheaf X ⋙ DerivedCategory.homologyFunctor _ n

/-- The chain-level unit of derived underlying presheaves, transported from the
homotopy-category unit by the canonical quotient comparisons. Source: Stacks, Tag 070K
(blueprint: def-trf-ringed-space-hypercohomology-presheaf). -/
def derivedModuleAbelianPresheafUnit :
    (moduleAbelianPresheaf X).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        @DerivedCategory.Q ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) _ _
          (HasDerivedCategory.standard _) ⟶
      DerivedCategory.Q ⋙ derivedModuleAbelianPresheaf X :=
  letI := HasDerivedCategory.standard ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  Functor.whiskerLeft ((moduleAbelianPresheaf X).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso _).inv ≫
    Functor.whiskerRight
      ((moduleAbelianPresheaf X).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      ((moduleAbelianPresheaf X).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K,
      (CochainComplex.toKInjectiveResolution.{u} _).app K, inferInstance,
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2⟩)) ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom
      (derivedModuleAbelianPresheaf X)

/-- The canonical map Γ(-,M) → H⁰(RΓ(-,M[0])), before asserting invertibility.
It is the derived unit, with both ordinary single-complex cohomology comparisons.
Source: Stacks, Tags 070K and 0D66
(blueprint: def-trf-ringed-space-hypercohomology-presheaf). -/
def hypercohomologyPresheafSingleUnit (M : SheafOfModules.{u} (moduleRings X)) :
    (moduleAbelianPresheaf X).obj M ⟶
      (ringedSpaceHypercohomologyPresheaf X 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) :=
  letI := HasDerivedCategory.standard ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
    ((moduleAbelianPresheaf X).obj M)).inv ≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) 0).map
      ((HomologicalComplex.singleMapHomologicalComplex (moduleAbelianPresheaf X)
        (ComplexShape.up ℤ) 0).inv.app M) ≫
    (DerivedCategory.homologyFunctorFactors _ 0).inv.app
      (((moduleAbelianPresheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj M)) ≫
    (DerivedCategory.homologyFunctor _ 0).map
      ((derivedModuleAbelianPresheafUnit X).app
        ((CochainComplex.singleFunctor _ 0).obj M))

end AlgebraicGeometry.RingedSpace
