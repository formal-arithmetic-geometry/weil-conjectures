/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import WeilConjectures.ZetaSeries
import WeilConjectures.AlgebraicGeometry.SpecFieldPointResidueField
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg

/-!
# Strict drop of residue transcendence degree under specialization

Source: Stacks Project, Morphisms, Tag 06RU, assertion (3), over the spectrum of a field;
Algebra, Tag 06RP (blueprint: lem-sfb-field-specialization-trdeg-drop).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A nontrivial specialization in a scheme locally of finite type over a field strictly
lowers the residue transcendence degree, with both scalar structures induced by `f`.
Source: Stacks Project, Morphisms, Tag 06RU (3), and Algebra, Tag 06RP
(blueprint: lem-sfb-field-specialization-trdeg-drop).

Proof:
1. Choose a finite-type affine chart `U = Spec A` containing `x'`, using
   `def-weil-finite-type-morphism`. The closure hypothesis puts `x` in `U` too.
   `lem-weil-pbc-affine-open-spec-points` identifies these distinct points with distinct primes.
2. The Zariski topology of `def-weil-affine-spectrum` gives primes `p < q` representing
   `x` and `x'`. The quotients `B = A/p` and `C = A/q` are nonzero domains and finite-type
   algebras over `k`, by `def-weil-pbc-finite-type-algebra`.
3. `lem-weil-pbc-spec-field-point-residue-field`, clauses (1) and (2), identifies the two
   scheme residue fields with fraction fields of `B` and `C`, compatibly with the maps
   from `A`, hence with `k` through `f`. These are the fields and scalar structures of
   `def-weil-residue-field`, and the degrees are those of `def-kun-transcendence-degree`.
4. `lem-weil-pbc-finite-type-domain-dimension-trdeg` gives finite natural numbers
   `d = dim B = trdeg_k kappa(x)` and `e = dim C = trdeg_k kappa(x')`.
5. Lift a prime chain of maximal length `e` from `C` to `B`. Each inverse-image prime
   contains the nonzero prime `q/p`, so prepending the zero prime of `B` gives a chain
   of length `e + 1`. By `def-weil-pbc-krull-dimension-ring`, `e + 1 ≤ d`, as required.
-/
theorem field_specialization_trdeg_drop
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (x x' : X) (hne : x ≠ x') (hsp : x' ∈ closure ({x} : Set X)) :
    @Algebra.trdeg k (X.residueField x') _ _ (f.residueFieldAlgebraMap x').toAlgebra <
      @Algebra.trdeg k (X.residueField x) _ _ (f.residueFieldAlgebraMap x).toAlgebra := by
  sorry

end AlgebraicGeometry
