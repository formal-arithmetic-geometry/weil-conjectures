/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange

/-! # Restricting native projective-line cohomology to an open base -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Cohomology of pullback followed by direct image restricts to the relative
projective-line calculation on an open base.
Source: current blueprint, `thm-amb-p1-decomposition.proof.md`, locality on the base.
(blueprint: lem-pur-native-projective-line-open-restriction).

Proof: exact restriction commutes with cohomology. Apply ordinary derived open base
change, identify the two composite pullbacks by the cartesian square, and commute
exact pullback with the degree-zero single functor. Every comparison is an existing
natural isomorphism, so this works in every integer degree.
-/
theorem native_projectiveLine_open_cohomology_comparison
    (l : ℕ) [Fact l.Prime] {P S U : Scheme.{u}} (q : P ⟶ S) (j : U ⟶ S)
    (a : ProjectiveLine U ⟶ P) [IsOpenImmersion j] [IsOpenImmersion a]
    (hsq : IsPullback (ProjectiveLine U ↘ U) a j q)
    (M : AdicSheaf l S) (n : ℤ) :
    Nonempty ((adicUpperStar l j).obj ((DerivedCategory.homologyFunctor _ n).obj
      ((adicLowerStar l q).rightDerivedFunctor.obj
        ((adicUpperStar l q).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        ((adicLowerStar l (ProjectiveLine U ↘ U)).rightDerivedFunctor.obj
          ((adicUpperStar l (ProjectiveLine U ↘ U)).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj ((adicUpperStar l j).obj M))))) := by
  let qU := ProjectiveLine U ↘ U
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let c : (adicUpperStar l q).mapDerivedCategory ⋙
        (adicUpperStar l a).mapDerivedCategory ≅
      (adicUpperStar l j).mapDerivedCategory ⋙
        (adicUpperStar l qU).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l hsq.w.symm) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  exact ⟨((adicUpperStar l j).mapDerivedCategoryHomologyFunctorIso n).app _ ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((adicDerivedBaseChangeIso l hsq).app _ ≪≫
        (adicLowerStar l qU).rightDerivedFunctor.mapIso
          (c.app K ≪≫ (adicUpperStar l qU).mapDerivedCategory.mapIso
            (((adicUpperStar l j).mapDerivedCategorySingleFunctor 0).app M)))⟩

end AlgebraicGeometry.ProEtale
