/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Right fractions for finite filtered module complexes

Source: Stacks Project, Derived Categories, Tags 05S1 and 05RM, using the cone construction
of Tag 05RG, restricted to globally finite filtrations
(blueprint: lem-kun-filtered-quasi-isomorphism-fractions).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CochainComplex

/-- Graded quasi-isomorphisms of globally finite filtered complexes contain identities,
are closed under composition, satisfy two-out-of-three, and admit right fractions.
The right-fraction structure asserts both the Ore square and cancellation in the filtered
homotopy category; every witnessing object still has a globally finite filtration.
Source: Stacks, Tags 05S1, 05RM and 05RG
(blueprint: lem-kun-filtered-quasi-isomorphism-fractions).

Proof (the seven steps of the DAG node):
1. Filtered maps and filtered homotopies descend to each quotient F^i/F^(i+1).
   Homotopic maps induce equal cohomology maps, since their difference on a cocycle
   is d(hx). Grading and cohomology preserve identities and compositions. Apply
   two-out-of-three for invertible module maps in every filtration and cochain degree.
2. Give finite sums and cones the componentwise filtration and shifts the unchanged
   filtration index. The graded cone of v is the cone of the graded map, by sending
   [(b,a)] to ([b],[a]); the quotient relation and differential agree componentwise.
   Grading also commutes with sums and shifts. Shifts preserve acyclicity.
3. A degreewise surjection p with acyclic kernel is a quasi-isomorphism: lift a cycle
   and subtract a kernel element with the same differential to make its lift closed.
   For injectivity, subtract a lifted boundary and then use acyclicity of the kernel.
4. For f:X to Z and s:Y to Z, take T^n=X^n+Y^n+Z^(n-1), with differential
   D(x,y,z)=(dx,dy,-dz+f(x)-s(y)). The projections t and g are filtered chain maps;
   h(x,y,z)=z gives dh+hD=ft-sg. Each graded kernel of t is the shifted cone of
   the graded s. The cone criterion lem-pur-quasi-iso-cone-acyclic makes it acyclic;
   the graded projection is surjective, so step 3 puts t in W.
5. For cancellation put a=f-g and choose a filtered H with sa=dH+Hd.
   Set C^n=Y^n+Z^(n-1), d_C(y,z)=(dy,-dz-s(y)), u(x)=(a(x),-H(x)),
   and q(y,z)=y. The homotopy identity makes u a chain map, and qu=a.
   Each graded C is an acyclic shifted cone by the same cone criterion.
6. Set T^n=X^n+C^(n-1), D(x,c)=(dx,-d_C(c)-u(x)), and t(x,c)=x.
   Its graded kernel is the acyclic shifted graded C, so step 3 gives t in W.
   The filtered degree -1 map k(x,c)=-c satisfies d_C k+kD=ut. Thus qk is
   a filtered null-homotopy of (f-g)t, proving the required cancellation.
7. The minimum of the input lower bounds and maximum of their upper bounds work
   for all these sums, cones and shifts. They are independent of cochain degree.
   Thus the Ore and cancellation objects belong to the same globally finite category.
   No truncation or infinite sum occurs, including for zero or unbounded complexes.
   Steps 1, 4 and 6 are exactly the multiplicativity and right fraction axioms. -/
theorem finiteFilteredModuleQuasiIso_fractions (R : Type u) [CommRing R] :
    (finiteFilteredModuleQuasiIso R).HasRightCalculusOfFractions ∧
      (finiteFilteredModuleQuasiIso R).HasTwoOutOfThreeProperty := by
  sorry

end CochainComplex
