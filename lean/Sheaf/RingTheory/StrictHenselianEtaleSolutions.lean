/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.RingTheory.HenselianLocalTargetEtaleMaps
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.IsSepClosed

/-!
# Étale polynomial solutions over strictly henselian local rings

Source: Stacks Project, Algebra, Tag 04GX, `lemma-strictly-henselian-solutions`
(blueprint: lem-sfb-strict-henselian-etale-solutions).
-/

@[expose] public section

universe u v

namespace MvPolynomial

/-- A local map of strictly henselian local rings induces a bijection on the solutions
of an étale polynomial system.

Source: Stacks Project, Algebra, Tag 04GX, `lemma-strictly-henselian-solutions`
(blueprint: lem-sfb-strict-henselian-etale-solutions).

Proof:
1. Put `D = R[X]/(P)` and let `k` and `K` be the residue fields of `R` and `S`.
   Locality induces an injective map `k → K` compatible with the residue maps.
   The polynomial universal property identifies solutions in any `R`-algebra `T`
   with `Hom_R(D,T)`: evaluation factors through `D` precisely when all `P i` vanish,
   and the variable classes determine the map. For `T = S`, these equations are
   those of `map θ (P i)`. The coordinate map is postcomposition by `θ`.
2. Étaleness is stable under base change (lem-weil-pbc-etale-ring-base-change).
   Apply lem-weil-pbc-henselian-local-target-etale-maps to `D` over `R`, with target
   `R`, and to `S ⊗[R] D` over `S`, with target `S`. Each target is module-finite
   and formally unramified over itself, and henselian. Tensor adjunction identifies
   these bijections with reduction from `Hom_R(D,R)` to `Hom_R(D,k)` and from
   `Hom_R(D,S)` to `Hom_R(D,K)`.
3. By lem-weil-pbc-etale-algebra-over-field-product, the étale algebra `k ⊗[R] D`
   is a finite product of finite separable extensions of `k`. As `k` is separably
   closed, each factor is `k` (def-kun-separably-closed). Thus it is `k^I` for a
   finite index set `I`, which may be empty.
4. A `k`-algebra map from `k^I` to either field `k` or `K` selects exactly one
   coordinate: the orthogonal standard idempotents sum to one, so exactly one has
   image one. Conversely each coordinate gives a map. If `I` is empty both Hom
   sets are empty. Postcomposition by `k → K` preserves the coordinate, hence is
   bijective. Tensor adjunction identifies this with `Hom_R(D,k) → Hom_R(D,K)`.
5. The square of postcomposition by `θ` and the residue-field map, with vertical
   reduction maps, commutes by compatibility of the residue maps. Both vertical
   maps and the bottom map are bijective, so the top is bijective. Evaluation on
   variable classes recovers the asserted coordinatewise bijection. For `n = 0`
   both solution sets are singletons. -/
theorem bijOn_solutions_of_isStrictlyHenselianLocalRing
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsStrictlyHenselianLocalRing R] [IsStrictlyHenselianLocalRing S]
    (θ : R →+* S) [IsLocalHom θ] (n : ℕ) (P : Fin n → MvPolynomial (Fin n) R)
    (hEtale : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)))))) :
    Set.BijOn (fun r : Fin n → R ↦ fun j ↦ θ (r j))
      {r : Fin n → R | ∀ i : Fin n, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i : Fin n, MvPolynomial.eval s (MvPolynomial.map θ (P i)) = 0} := by
  sorry

end MvPolynomial
