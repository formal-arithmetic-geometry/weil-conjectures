module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.FiniteStability
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import WeilConjectures.RingTheory.QuasiFiniteFourRings
import Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition
import WeilConjectures.RingTheory.FiniteLocalHenselian

/-!
# Finite henselian localization of a tensor base change

Source: Stacks Project, Algebra, Tag 05WP (lemma-quasi-finite-henselization),
first two sentences of the proof, using Tags 00PN, 04GJ, 04GH and 00GS
(blueprint: lem-trf-quasi-finite-henselian-tensor-factor).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- For a finite-type map `A → B` quasi-finite at `q`, base change to a henselian local
`Aₚ`-algebra `R` is quasi-finite at every prime `n` over `q` and the maximal ideal of `R`.
Its localization at `n` is module-finite over `R`, the canonical map is local, and the
localization is henselian. Locality is written as equality of contracted maximal ideals.
Source: Stacks Project, Algebra, Tag 05WP (lemma-quasi-finite-henselization), proof,
and Tag 04GH (lemma-finite-over-henselian), parts (2) and (3)
(blueprint: lem-trf-quasi-finite-henselian-tensor-factor).

Proof:
1. The tensor-product pushout and generation by pure tensors express every element of
   `C = R ⊗[A] B` as a finite sum of products of images of `R` and `B`, using
   lem-weil-pbc-algebra-tensor-pushout-universal-property and
   def-weil-pbc-module-tensor-product. Apply lem-weil-pbc-quasi-finite-four-rings to
   `(A, B, R, C)`. This gives finite type over `R` and quasi-finiteness at `n`.
2. Apply lem-weil-pbc-henselian-finite-type-product-decomposition to write `C` as a
   product of finite local algebras and a remainder with no quasi-finite prime above the
   maximal ideal of `R`. Orthogonal coordinate idempotents select exactly one factor
   for `n`. It cannot select the remainder: apply the four-rings lemma to the surjective
   projection onto that factor to contradict its non-quasi-finiteness clause.
3. In the selected finite local factor `D`, the prime over the maximal ideal of `R` is
   maximal: its quotient is a finite-dimensional domain over the residue field, hence a
   field by lem-weil-pbc-finite-dimensional-domain-is-field. It is therefore the unique
   maximal ideal of `D`. The projection `C → D` extends to `Cₙ → D`, since denominators
   map to units. The inverse sends an element of `D` to its coordinate vector in `Cₙ`.
   The selected coordinate idempotent becomes one and all others become zero. These
   formulas give an `R`-algebra isomorphism `Cₙ ≃ D`, proving module-finiteness.
4. By def-weil-pbc-localization-at-prime, the maximal ideal of `Cₙ` contracts to `n`:
   if a denominator outside `n` times a numerator belongs to `n`, primality puts the
   numerator in `n`. Its further contraction to `R` is the given maximal ideal, which
   proves locality of the canonical map. Finally lem-weil-pbc-finite-local-henselian
   applies to the module-finite local `R`-algebra `Cₙ`, proving henselianity. -/
theorem quasiFinite_henselian_tensor_factor
    (A : Type u) (B : Type v) (R : Type w) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra.FiniteType A B]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hqp : q.asIdeal.comap (algebraMap A B) = p.asIdeal)
    (hq : IsQuasiFiniteAtPrime A B q)
    [HenselianLocalRing R] [Algebra A R] [Algebra (Localization.AtPrime p.asIdeal) R]
    [IsScalarTower A (Localization.AtPrime p.asIdeal) R]
    (hlocal : (IsLocalRing.maximalIdeal R).comap
      (algebraMap (Localization.AtPrime p.asIdeal) R) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (n : PrimeSpectrum (R ⊗[A] B))
    (hnR : n.asIdeal.comap (algebraMap R (R ⊗[A] B)) = IsLocalRing.maximalIdeal R)
    (hnB : n.asIdeal.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] R ⊗[A] B).toRingHom = q.asIdeal) :
    IsQuasiFiniteAtPrime R (R ⊗[A] B) n ∧
      Module.Finite R (Localization.AtPrime n.asIdeal) ∧
      (IsLocalRing.maximalIdeal (Localization.AtPrime n.asIdeal)).comap
        (algebraMap R (Localization.AtPrime n.asIdeal)) = IsLocalRing.maximalIdeal R ∧
      HenselianLocalRing (Localization.AtPrime n.asIdeal) := by
  sorry

end Algebra
