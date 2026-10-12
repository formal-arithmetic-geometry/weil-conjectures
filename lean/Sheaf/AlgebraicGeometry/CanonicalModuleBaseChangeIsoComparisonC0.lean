/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap

/-! # Existence of a module pullback comparison

Source: Stacks Project, Tags 06YJ, 08HY, 0D5T and 08IB.
(blueprint: stage3-canonicalModuleBaseChange_iso_comparison_c0).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Transport the derived module pullback comparison to the chosen pullback square.
Source: Stacks Project, Tag 08HY, counit construction; Tag 0D5T, derived composition;
Tag 08IB, first proof paragraph, coordinate transport.
(blueprint: stage3-canonicalModuleBaseChange_iso_comparison_c0).

Proof: Apply exists_derivedPullback to the first projection of the chosen
pullback. The specification of the chosen derived functor supplies an additive
underived functor E, identified on objects and maps with tensorPullback, and a
left-derived counit epsilon. Functor extensionality identifies E with the
recorded tensorPullback. Evaluate epsilon at the single module G in the
homotopy category, and compose with the localization of the canonical
single-complex tensor-pullback identification. This composite c0 and epsilon
satisfy IsDerivedModulePullbackComparison by its definition. No property of
the original square or comparison c is needed for this existence assertion.
-/
theorem canonicalModuleBaseChange_iso_comparison_c0
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (_sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (_hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) G c0 := by
  let p := pullback.fst (f ≫ eS.hom) (eT.inv ≫ g ≫ eS.hom)
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hε, htri, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback p)
  have h : E = Scheme.Modules.tensorPullback p :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  refine ⟨ε.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback p) (ComplexShape.up ℤ) 0).hom.app G)), ?_⟩
  exact ⟨ε, hε, rfl⟩

end AlgebraicGeometry
