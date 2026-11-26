/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology

/-!
# Module cohomology and open module cohomology at the whole space

Forgetting global scalars identifies the cohomology of a sheaf of modules on a ringed space with
its open module cohomology at the whole space.

## Implementation details

Both derived functors are computed with the same injective resolution; forgetting scalars is
exact, so it commutes with taking homology of the global-sections complex.

## References

* [Stacks Project, Tag 01DZ](https://stacks.math.columbia.edu/tag/01DZ)
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.RingedSpace

/-- Forgetting global scalars identifies module cohomology with open module cohomology
at the whole space, naturally in the module sheaf. -/
theorem nonempty_moduleCohomology_top_iso (X : RingedSpace.{u}) (p : ℕ) :
    Nonempty ((moduleCohomology X p ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤))) AddCommGrpCat.{u}) ≅
      openModuleCohomology X p ⊤) := by
  let : EnoughInjectives (SheafOfModules.{u} (moduleRings X)) :=
    (moduleSheaves_abelian_enoughInjectives X).2
  let M := ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤))
  let U : M ⥤ AddCommGrpCat.{u} := forget₂ M AddCommGrpCat.{u}
  let c := ComplexShape.up ℕ
  let h : U.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor _ c p ≅
      HomologicalComplex.homologyFunctor M c p ⋙ U :=
    Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor M c p)
      (ShortComplex.homologyFunctorIso U)
  let k : U.mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor _ c p ≅
      HomotopyCategory.homologyFunctor M c p ⋙ U :=
    Quotient.natIsoLift _
      (Functor.isoWhiskerRight (U.mapHomotopyCategoryFactors c) _ ≪≫
        Functor.isoWhiskerLeft (U.mapHomologicalComplex c)
          (HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{u} c p) ≪≫
        h ≪≫ Functor.isoWhiskerRight (HomotopyCategory.homologyFunctorFactors M c p).symm U)
  let G := globalSectionsFunctor X
  let s : G ⋙ U ≅ openModuleSections X ⊤ := Iso.refl _
  exact ⟨Functor.isoWhiskerLeft (injectiveResolutions _) (Functor.isoWhiskerLeft
      (G.mapHomotopyCategory c) k.symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso s c) _)⟩

end AlgebraicGeometry.RingedSpace
