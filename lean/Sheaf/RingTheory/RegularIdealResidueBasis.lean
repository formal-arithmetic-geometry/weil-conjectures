module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.RingTheory.RegularSequenceConormal
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.LocalRing.Module

/-!
# Residue bases and prescribed generators of regular-sequence ideals

Source: Stacks Project, Algebra, Tags 00SE (last paragraph) and 00LN (1), in degree one.
(blueprint: lem-trf-regular-ideal-residue-basis-prescribed-generator)

The ideal `I` is parameterized together with its defining equality. Its generators are
viewed as elements of `I`. The quotient by `maximalIdeal R • ⊤` is taken inside `I`.
The reduction map on conormal modules is characterized on every representative, and
its compatibility with the two coordinate isomorphisms is stated on lifted coefficients.
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- A regular-sequence ideal has its generator classes as a residue basis, compatibly
with conormal coordinates, and any element with nonzero residue can be the first generator.

Source: Stacks Project, Algebra, Tags 00SE (last paragraph), 00LN (1) in degree one,
and 00DV (8).
(blueprint: lem-trf-regular-ideal-residue-basis-prescribed-generator)

Proof:
1. Apply `regularSequence_conormal_free` (lem-weil-pbc-regular-sequence-conormal-free)
   to obtain the basis of `I/I²` consisting of the original generators, including length zero.
2. Since `I ≤ maximalIdeal R`, the square of `I` lies in `maximalIdeal R * I`.
   The conormal coordinate map takes the maximal-ideal multiples of the coordinate
   module precisely onto the maximal-ideal multiples of `I/I²`. Quotienting gives the
   residue coordinate isomorphism. Both maps send lifted coefficients to the same
   sum of coefficient times generator; this proves the stated commuting formula.
3. Residues of any finite generating list span the residue module. Apply
   `linearIndependent_le_span''` (lem-sfb-independent-family-spanning-cardinality)
   to the original basis and this spanning set. Its cardinality is at most the list length,
   including lists with repetitions, so the list length is at least `b`.
4. A nonzero residue of `x` has a nonzero coordinate in the original basis, so `b ≥ 1`.
   Replace that coordinate's basis vector by the residue of `x`. Solving for the old
   vector proves spanning; the replaced coordinate in any relation proves independence.
   Put `x` first and enumerate the remaining original generators after it.
5. The ideal is a finite module. Nakayama, in the form `IsLocalRing.map_mkQ_eq_top`
   (lem-weil-pbc-nakayama-local-generators), lifts spanning of these residues to generation
   of `I`. No regularity of the new list is claimed. At length zero the ideal and its
   residue module are zero, so the prescribed-element assertion has no instances.
-/
theorem regularIdeal_residue_basis_prescribed_generator
    (R : Type u) [CommRing R] [IsLocalRing R] (b : ℕ) (I : Ideal R)
    (z : Fin b → I)
    (hI : Ideal.span (Set.range (fun i ↦ (z i : R))) = I)
    (hz : ∀ i : Fin b, (z i : R) ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsRegular R (List.ofFn (fun i ↦ (z i : R)))) :
    (∃ (c : Module.Basis (Fin b) (R ⧸ I) I.Cotangent)
        (v : Module.Basis (Fin b) (R ⧸ IsLocalRing.maximalIdeal R)
          (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)))),
      (∀ i : Fin b, c i = I.toCotangent (z i)) ∧
      (∀ i : Fin b, v i =
        (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)).mkQ (z i)) ∧
      ∃ q : I.Cotangent →ₗ[R]
          (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I))),
        (∀ x : I, q (I.toCotangent x) =
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)).mkQ x) ∧
        Function.Surjective q ∧
        LinearMap.ker q = IsLocalRing.maximalIdeal R • (⊤ : Submodule R I.Cotangent) ∧
        (∀ a : Fin b → R,
          q (c.equivFun.symm (fun i ↦ Ideal.Quotient.mk I (a i))) =
            v.equivFun.symm (fun i ↦ Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a i)))) ∧
    (∀ (r : ℕ) (y : Fin r → R), Ideal.span (Set.range y) = I → b ≤ r) ∧
    (∀ x : I, (x : R) ∉ IsLocalRing.maximalIdeal R * I →
      1 ≤ b ∧ ∃ (w : Fin b → I) (v : Module.Basis (Fin b)
          (R ⧸ IsLocalRing.maximalIdeal R)
          (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)))),
        (∀ i : Fin b, i.val = 0 → w i = x) ∧
        (∀ i : Fin b, v i =
          (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)).mkQ (w i)) ∧
        Ideal.span (Set.range (fun i ↦ (w i : R))) = I) ∧
    (b = 0 → I = ⊥ ∧
      Subsingleton (I ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R I)))) := by
  sorry

end RingTheory.Sequence
