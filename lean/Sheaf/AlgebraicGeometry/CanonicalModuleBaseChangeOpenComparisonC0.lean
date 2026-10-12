/-
Copyright (c) 2026 The SHEAF contributors.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

/-- Restricted canonical comparison, isolated from the coherence isomorphisms.
Source: Stacks Project, Tags 08HY and 0D5U.
(blueprint: lem-pc-canonical-module-base-change-open-comparison-c0) -/
theorem exists_restricted_module_pullback_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let H := (schemeOpenRestriction X U).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) H c0
 := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  have _ := sq
  have _ := hc
  let p := pullback.fst (f ∣_ V) (g.resLE V W hWV)
  let H := (schemeOpenRestriction X (f ⁻¹ᵁ V)).obj G
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      Classical.choose_spec (exists_derivedPullback.{u, w} p)
  have h : E = Scheme.Modules.tensorPullback p :=
    CategoryTheory.Functor.ext (F := E) (G := Scheme.Modules.tensorPullback p)
      hE (fun M N a ↦ hEmap a)
  clear hK htri hE hEmap hIres hIcolim hIlim hIadd hImap hI I
  subst E
  change DerivedCategory.Qh.{w} ⋙ derivedPullback.{u, w} p ⟶
    (Scheme.Modules.tensorPullback p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
        (moduleRings (pullback (f ∣_ V) (g.resLE V W hWV)).toRingedSpace)) at ε
  let c0 : (derivedPullback.{u, w} p).obj ((DerivedCategory.singleFunctor.{w}
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace)) 0).obj H) ⟶
      (DerivedCategory.singleFunctor.{w}
        (SheafOfModules.{u} (moduleRings (pullback (f ∣_ V)
          (g.resLE V W hWV)).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback p).obj H) := ε.app ((HomotopyCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace)) 0).obj H) ≫
    DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback p) (ComplexShape.up ℤ) 0).hom.app H))
  have hc0 : IsDerivedModulePullbackComparison p H c0 := ⟨ε, hL, rfl⟩
  exact ⟨c0, hc0⟩

end AlgebraicGeometry
