/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution

/-!
# Exactness of the free module presheaf nerve

Source: Stacks Project, Cohomology on Sites, Tags 03F5, 03AT; Hypercoverings, 01GC.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The alternating chain complex of free module presheaves on the Čech nerve.
Source: Stacks Project, Tags 03AS and 01GC.
(blueprint: lem-sc-presheaf-free-nerve-exact) -/
noncomputable def presheafFreeNerveComplex
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) : ChainComplex (PresheafOfModules.{v} R) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj
    (f.cechNerve ⋙ PresheafOfModules.free R)

/-- The free module presheaf nerve is exact in positive degrees, for every map.
Source: Stacks Project, Cohomology on Sites, Tags 03F5 and 03AT; Hypercoverings, 01GC.
(blueprint: lem-sc-presheaf-free-nerve-exact)

Proof: evaluate at any object X. Finite limits in the presheaf category are
objectwise, so a basis element in degree n is an (n+1)-tuple of elements of
P(X) with common image under f(X). Partition these tuples by that image.
Replace the target of f(X) by its range, which leaves all these tuples and
their deletion maps unchanged. The induced map to the range is surjective.
Apply setCechNerve_free_resolution over R(X); its last conjunct gives exactness
in every positive degree. Equivalently each nonempty fibre contracts by prefixing
a chosen vertex; an empty fibre contributes the zero module. The identification
commutes with the alternating deletion boundaries. Evaluation jointly reflects
exactness in module presheaves (kernels and cokernels are computed objectwise),
so the presheaf chain complex is exact in degree n+1. No natural choice of a
vertex across X is needed, and all free modules have values in universe v. -/
theorem presheafFreeNerveComplex_exactAt
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (n : ℕ) :
    (presheafFreeNerveComplex R f).ExactAt (n + 1) := by
  sorry

end CategoryTheory
