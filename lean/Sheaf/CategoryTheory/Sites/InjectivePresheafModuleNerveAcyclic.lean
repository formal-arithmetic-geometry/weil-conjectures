/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution

/-!
# Čech nerve acyclicity for injective module presheaves

Source: Stacks Project, Cohomology on Sites, Tags 03FC, 03F5, 03AT.
(blueprint: lem-sc-injective-presheaf-module-nerve-acyclic)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The Čech nerve of any map of small-valued presheaves is acyclic in positive
cochain degrees against an injective module presheaf. No covering condition is needed.
Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC, using Tags 03F5,
03AS and 03AT; Hypercoverings, Tag 01GC, fibrewise nerve formulation.
(blueprint: lem-sc-injective-presheaf-module-nerve-acyclic)

Proof: apply the free `R`-module presheaf functor to the simplicial nerve of `f`.
At each object, split its basis by the value of `f`. A fibre with no elements
contributes zero in every nerve degree. In every nonempty fibre, prefix a chosen
lift to the tuple. The alternating deletion formula gives a contracting homotopy,
so the free module chain complex is exact in every positive degree. Exactness
of module presheaves is objectwise. All free modules are small-valued, since the
ring and both presheaves have values in the same universe. Thus injectivity of
`M` applies to the image inclusions in this complex. A cocycle factors through
the image of the outgoing boundary, and injectivity extends that factor to the
preceding chain term. Free-module adjunction followed by free-abelian adjunction
identifies these Hom groups with the terms of `presheafCechComplex f M.presheaf`;
the identifications commute with the alternating boundaries. Hence each cocycle
is a coboundary and positive cohomology is zero. -/
theorem injective_presheaf_module_nerve_acyclic
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (M : PresheafOfModules.{v} R) [Injective M]
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (q : ℕ) (hq : 0 < q) :
    IsZero ((presheafCechComplex f M.presheaf).homology q) := by
  sorry

end CategoryTheory
