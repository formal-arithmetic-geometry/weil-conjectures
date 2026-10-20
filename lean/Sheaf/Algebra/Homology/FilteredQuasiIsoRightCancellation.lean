/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D6
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Right cancellation

Source: Stacks Project, Derived Categories, Tags 05RG and 05S1.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CochainComplex

/-- Right cancellation for graded quasi-isomorphisms of finite filtered complexes.

Source: Stacks Project, Derived Categories, Tag 05RG, right MS3 (the dual of MS3 in
`lemma-construct-multiplicative-system`), and Tag 05S1, `lemma-filtered-acyclic`.
Proof: filtered homotopies form a congruence: zero, negation and addition give
reflexivity, symmetry and transitivity, and restriction factorizations compose with
filtered chain maps. Hence equality in the quotient is a filtered homotopy. Choose
chain representatives and write a=f₁-f₂ and `sa=dH+Hd` for that homotopy.
Set `Cⁿ=Yⁿ ⊕ Zⁿ⁻¹` and `dC(y,z)=(dy,-dz-s(y))`. The map
`u(x)=(a(x),-H(x))` is a filtered chain map by the displayed homotopy identity;
the projection q to Y satisfies qu=a. Every graded C is an acyclic shifted cone
of the corresponding graded s, by the ordinary acyclic-cone criterion.
Now put `Tⁿ=Xⁿ ⊕ Cⁿ⁻¹`, `D(x,c)=(dx,-dC(c)-u(x))`, and `t(x,c)=x`.
Its differential squares to zero since u is a chain map. In every grade t is
surjective with kernel the shifted graded C, which is acyclic. Lifting cycles
and boundaries and correcting by kernel boundaries proves that t is a graded
quasi-isomorphism. The filtered degree -1 map `k(x,c)=-c` satisfies
`dC k+kD=ut`, so qk is a filtered null-homotopy of at. This gives the asserted
equality in the quotient. All filtrations are componentwise; the minimum lower
and maximum upper bounds of X,Y,Z work for C,T in every cochain degree.
(blueprint: lem-kun-filtered-quasi-isomorphism-right-cancellation). -/
theorem finiteFilteredModuleQuasiIso_rightCancellation (R : Type u) [CommRing R]
    {X Y Z : FiniteFilteredModuleHomotopy R} (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Z)
    (hs : finiteFilteredModuleQuasiIso R s) (h : f₁ ≫ s = f₂ ≫ s) :
    ∃ (T : FiniteFilteredModuleHomotopy R) (t : T ⟶ X),
      finiteFilteredModuleQuasiIso R t ∧ t ≫ f₁ = t ≫ f₂ := by
  sorry

end CochainComplex
