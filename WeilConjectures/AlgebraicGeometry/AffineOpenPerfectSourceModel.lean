/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel

import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.PerfectAffineBoundedProjective
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.LocallySmall

/-! # Perfect source models on affine opens

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-perfect-source-model).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exact realization of open pullback preserves perfectness. -/
private theorem perfect_exact_pullback {Y X : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (θ : F ≅ Modules.tensorPullback g)
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    IsPerfect Y (F.mapDerivedCategory.obj E) := by
  classical
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let T : B ⥤ SheafOfModules.{u} (moduleRings Y.toRingedSpace) := Modules.tensorPullback g
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    G, hG, hGmap, hGadd, ε, hL, htri, hK⟩ :=
    derivedPullback_spec g
  have h : G = T := CategoryTheory.Functor.ext hG (fun M N a ↦ hGmap a)
  subst G
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  have : (derivedPullback g).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let i : derivedPullback g ≅ T.mapDerivedCategory :=
    Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback g) ε
      T.mapDerivedCategoryFactorsh.hom W
  let c := (Functor.mapDerivedCategoryNatIso θ).app E ≪≫ i.symm.app E
  have hp := derivedPullback_preserve_perfect g E hE
  intro y
  obtain ⟨V, hy, K, hK, ⟨iK⟩⟩ := hp y
  exact ⟨V, hy, K, hK, ⟨(SheafOfModules.overFunctor.{u}
    (moduleRings Y.toRingedSpace) V).mapDerivedCategory.mapIso c ≪≫ iK⟩⟩

/-- An exact equivalence transfers the size of a chosen derived localization. -/
private theorem localization_on_source {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{w} D] : Nonempty (HasDerivedCategory.{w} C) := by
  let : HasDerivedCategory.{u + 1} C := HasDerivedCategory.standard C
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let d := e.mapDerivedCategory
  let : LocallySmall.{w} (DerivedCategory C) :=
    (locallySmall_congr d).mpr inferInstance
  exact ⟨(HomologicalComplex.quasiIso C (.up ℤ)).hasLocalizationOfLocallySmall
    DerivedCategory.Q⟩

end AlgebraicGeometry.Scheme
