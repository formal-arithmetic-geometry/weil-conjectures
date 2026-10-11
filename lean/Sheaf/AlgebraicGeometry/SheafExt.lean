/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Paper.DerivedHomMayerVietoris
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Sheaf Ext on a scheme

Source: Stacks Project, Cohomology of Sheaves, Sections 0BQP and 08DH
(blueprint: def-weil-pbc-sheaf-ext).

Sheaf Ext is the cohomology sheaf of the derived internal Hom. For modules, both arguments
are embedded in the derived category in degree zero. The bifunctors retain contravariance
in the first argument and covariance in the second.
-/

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The sheaf Ext bifunctor in integer degree `i`, obtained by composing the derived
internal Hom with the cohomology-sheaf functor. Source: Stacks Project, Sections 0BQP
and 08DH (blueprint: def-weil-pbc-sheaf-ext). -/
noncomputable def sheafExtFunctor (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] (i : ℤ) :
    (DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
  derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf ⋙
    DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i

/-- The `i`-th sheaf Ext of derived objects `K, L` is `Hⁱ(R𝓗om(K,L))`, an `𝒪_X`-module.
Source: Stacks Project, Section 0BQP (blueprint: def-weil-pbc-sheaf-ext). -/
noncomputable def sheafExt (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (i : ℤ) (K L : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
  (sheafExtFunctor X i).obj (op K, L)

/-- Sheaf Ext of modules as a bifunctor: embed both modules in degree zero, then take
sheaf Ext. This is contravariant in the first module and covariant in the second.
Source: Stacks Project, Sections 0BQP and 08DH
(blueprint: def-weil-pbc-sheaf-ext). -/
noncomputable def moduleSheafExtFunctor (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] (i : ℤ) :
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))ᵒᵖ ×
      SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).op.prod
    (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0) ⋙
      sheafExtFunctor X i

/-- For modules `F, G`, sheaf Ext means sheaf Ext of `F[0], G[0]`.
Source: Stacks Project, Section 0BQP (blueprint: def-weil-pbc-sheaf-ext). -/
noncomputable def moduleSheafExt (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (i : ℤ) (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
  (moduleSheafExtFunctor X i).obj (op F, G)

end AlgebraicGeometry
