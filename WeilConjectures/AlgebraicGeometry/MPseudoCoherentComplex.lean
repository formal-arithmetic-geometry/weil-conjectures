/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback

/-! # Degreewise pseudo-coherence on a scheme

Source: Stacks Project, Cohomology of Sheaves, Tags 08CB (1), (3), 08CC (1), and 08C4
(blueprint: def-sfb-m-pseudo-coherent-complex).

Strictly perfect complexes use the recorded over-site model. The canonical equivalence
`Scheme.Modules.overEquiv` transports each such complex to modules on the open subscheme,
where its derived image maps to the derived pullback of the given object.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An object of `D(𝒪_Y)` is `m`-pseudo-coherent if locally a strictly perfect complex
maps to it in the derived category, inducing cohomology isomorphisms above `m` and a
surjection in degree `m`. Pointwise open neighbourhoods express an arbitrary open cover;
they and their approximating complexes can depend on `m`. The complex on the over-site
is transported by the canonical equivalence to modules on the open subscheme.
Source: Stacks Project, Cohomology of Sheaves, Tags 08CB (1), (3), 08CC (1), and 08C4
(blueprint: def-sfb-m-pseudo-coherent-complex). -/
def IsMPseudoCoherent (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (m : ℤ) (L : schemeDerivedCategory Y) : Prop :=
  ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧
    ∃ P : CochainComplex
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect Y U P ∧
      ∃ α : DerivedCategory.Q.obj
          (((Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
          (derivedPullback U.ι).obj L,
        (∀ j : ℤ, m < j →
          IsIso ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) j).map α)) ∧
        Epi ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) m).map α)

end AlgebraicGeometry.Scheme
