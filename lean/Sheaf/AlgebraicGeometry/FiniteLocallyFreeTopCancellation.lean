/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NZ
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
import WeilConjectures.AlgebraicGeometry.SingleFiniteRetractSheafAffineTrivialization

/-! # Local cancellation of the acyclic top degree of a finite locally free complex

Source: Stacks Project, Tag 08DN, proof of (1), also used in (2); Tag 08C6 for
local splitting and Tag 0BCI for the finite locally free kernel.
(blueprint: lem-sfb-finite-locally-free-top-cancellation)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free complex with zero top cohomology can locally be shortened
by one degree, with no lower bound on its terms.

Source: Stacks Project, Tag 08DN (`lemma-finite-cohomology`), proof of (1), the
one-degree cancellation also used in (2); Tag 08C6 (`lemma-local-lift-map`);
Tag 0BCI (`lemma-direct-summand-of-locally-free-is-locally-free`).
(blueprint: lem-sfb-finite-locally-free-top-cancellation)

Proof:
1. Put δ = d^(r-1). Since P^(r+1) is zero, H^r(P) is the cokernel of δ.
   Its vanishing makes δ an epimorphism, by
   `RingedSpace.module_exactness_local_lifting`, clause (1). This is local
   surjectivity of sheaves, rather than surjectivity on every open's sections.
2. At x, apply `exists_local_section_of_epi` to the finite locally free target
   P^r. On some neighbourhood U it gives a section s of δ. Shrink U further
   to trivialize the finite locally free sheaf P^(r-1). Let K be the kernel
   of the restricted δ; it is the subsheaf of sections killed by δ, by the
   kernel clause of `RingedSpace.module_exactness_local_lifting`.
3. The formula a ↦ a - s(δ(a)) defines a projection onto K. It is linear,
   commutes with restriction, and restricts to the identity on K. Thus K is
   a retract of the finite free sheaf P^(r-1)|_U. Apply
   `Scheme.exists_affine_trivialization_of_finite_retract` at x to obtain
   a smaller neighbourhood V on which K is finite free. Scheme stalks are
   local rings, as required by Tag 0BCI.
4. On V, keep P^j for j ≤ r-2, replace P^(r-1) by K, and put zero in degrees
   j ≥ r. Factor d^(r-2) through K using δ d^(r-2) = 0. The square-zero
   relation follows through the kernel inclusion; all other relations are
   unchanged or zero. Identities below r-1, the kernel inclusion at r-1,
   and zero above define a chain map Q → P|_V. The unchanged terms remain
   finite locally free after restriction, the new term is finite free, and
   the zero terms have rank zero.
5. Below r-2, cycles and boundaries are unchanged. At r-2 the outgoing
   differential has the same kernel after its codomain is restricted to K.
   At r-1 the cycles of P|_V are K and both complexes have the same boundaries.
   These boundary identifications follow also from clause (2) of
   `RingedSpace.module_exactness_local_lifting`, since sections lift locally
   through the same incoming map. At r both cohomologies vanish, using the
   restricted section s for P|_V. Above r both complexes are zero. Hence the
   chain map induces isomorphisms on every cohomology sheaf. Only the top two
   terms changed, so the argument uses no lower bound and applies to every
   integer r, including negative r and rank-zero terms. -/
theorem exists_local_finiteLocallyFree_top_cancellation
    (X : Scheme.{u}) (r : ℤ) (P : CochainComplex X.Modules ℤ)
    (hfree : ∀ i : ℤ, (P.X i).IsFiniteLocallyFree)
    (hzero : ∀ i : ℤ, r < i → IsZero (P.X i))
    (hcohomology : IsZero (P.homology r)) :
    ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      ∃ Q : CochainComplex V.toScheme.Modules ℤ,
        (∀ i : ℤ, (Q.X i).IsFiniteLocallyFree) ∧
        (∀ i : ℤ, r - 1 < i → IsZero (Q.X i)) ∧
        ∃ f : Q ⟶ ((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
          QuasiIso f := by
  sorry

end AlgebraicGeometry.Scheme.Modules
