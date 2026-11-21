/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses

/-!
# Sectionwise invariance of Hom complexes into K-injectives

## References

* Stacks Project, Lemmas 0A94 and 0A95
-/

@[expose] public section

universe u v r

open CategoryTheory Opposite

namespace CategoryTheory

/-- The map of Hom complexes induces a quasi-isomorphism on sections over every site object. -/
theorem homComplex_sections_quasiIsoOfUniverses
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    {R : Sheaf J CommRingCat.{max u v r}}
    {I' I L' L : CochainComplex
      (SheafOfModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)) ℤ}
    (s : I' ⟶ I) (t : L' ⟶ L) [I'.IsKInjective] [I.IsKInjective]
    [QuasiIso s] [QuasiIso t] (U : C) :
    let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
    QuasiIso (((SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj (op U) ⋙
      forget₂ (ModuleCat.{max u v r} (R₀.obj.obj (op U))) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((homComplexFunctor (R := R)).map t.op).app I' ≫
      ((homComplexFunctor (R := R)).obj (op L')).map s)) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R
  let := module_overFunctor_preservesZero R₀ U
  let res := (SheafOfModules.overFunctor.{max u v r} R₀ U).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let := HasDerivedCategory.standard (SheafOfModules.{max u v r} (R₀.over U))
  let Q := DerivedCategory.Q (C := SheafOfModules.{max u v r} (R₀.over U))
  have : QuasiIso (res.map t) :=
    localizedModule_restriction_quasiIsoOfUniverses.{u, v, r} R₀ U inferInstance t
  have : QuasiIso (res.map s) :=
    localizedModule_restriction_quasiIsoOfUniverses.{u, v, r} R₀ U inferInstance s
  refine ⟨fun n ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := homComplex_sections_derived_naturalityOfUniverses.{u, v, r} R U s t n
  dsimp only [homComplex] at a b hab
  let f := Q.map (res.map t)
  let g := Q.map ((shiftFunctor _ n).map (res.map s))
  have : IsIso f := by dsimp [f]; infer_instance
  have : IsIso g := by dsimp [g]; infer_instance
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rw [ConcreteCategory.isIso_iff_bijective]
  have hc : Function.Bijective
      (fun h : Q.obj (res.obj L) ⟶ Q.obj ((res.obj I')⟦n⟧) ↦ f ≫ h ≫ g) := by
    refine ⟨?_, ?_⟩
    · intro h k he
      have he' := congrArg (fun z ↦ inv f ≫ z ≫ inv g) he
      simpa [Category.assoc] using he'
    · intro h
      refine ⟨inv f ≫ h ≫ inv g, ?_⟩
      simp [Category.assoc]
  apply (Function.Bijective.of_comp_iff' b.bijective _).mp
  convert hc.comp a.bijective using 1
  exact funext hab

end CategoryTheory
