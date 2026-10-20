/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D6
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy

/-! # Right Ore squares

Source: Stacks Project, Derived Categories, Tags 05RG and 05S1.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CochainComplex

/-- Right Ore squares for graded quasi-isomorphisms of finite filtered complexes.

Source: Stacks Project, Derived Categories, Tag 05RG, right MS2 (the dual of MS2 in
`lemma-construct-multiplicative-system`), and Tag 05S1, `lemma-filtered-acyclic`.
Proof: choose filtered chain representatives of `f` and `s`. On
`Tⁿ = Xⁿ ⊕ Yⁿ ⊕ Zⁿ⁻¹` put
`D(x,y,z) = (dx,dy,-dz+f(x)-s(y))`. The chain-map equations imply `D² = 0`.
Give this complex the componentwise filtration. The projections `t` to X and `g` to Y
are filtered chain maps, and the filtered degree -1 map `(x,y,z) ↦ z` satisfies
`dh+hD = ft-sg`. Thus the square commutes in the filtered homotopy quotient.
In each grade the kernel of the projection to X is the shifted cone of the graded s.
Grading commutes with the finite direct sums, shifts and cone differentials by the
componentwise quotient map. The ordinary acyclic-cone criterion makes this kernel
acyclic. The graded projection is surjective in every degree. To prove its induced
cohomology map surjective, lift a cocycle and correct its differential by a boundary
in the kernel. To prove injectivity, subtract a lift of a boundary and then use
acyclicity of the kernel. Consequently t is a graded quasi-isomorphism.
The minimum lower bound and maximum upper bound of X,Y,Z bound the filtration of T
in every degree. This includes zero objects and unbounded cochain complexes.
(blueprint: lem-kun-filtered-quasi-isomorphism-right-ore). -/
theorem finiteFilteredModuleQuasiIso_rightOre (R : Type u) [CommRing R]
    {X Y Z : FiniteFilteredModuleHomotopy R} (f : X ⟶ Z) (s : Y ⟶ Z)
    (hs : finiteFilteredModuleQuasiIso R s) :
    ∃ (T : FiniteFilteredModuleHomotopy R) (t : T ⟶ X) (g : T ⟶ Y),
      finiteFilteredModuleQuasiIso R t ∧ t ≫ f = g ≫ s := by
  sorry

end CochainComplex
