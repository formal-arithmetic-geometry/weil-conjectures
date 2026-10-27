module

public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.FlatModInjective
import Mathlib.RingTheory.Filtration

/-!
# Regular residue-fibre initial forms lift through a flat associated graded ring

Source: the DAG's filtered-algebra synthesis, using Stacks Project, Algebra,
Tags 00NZ, 00ME and 00IQ(2)
(blueprint: lem-trf-flat-graded-fibre-regular-lift).

Finite freeness is expressed by unique finite basis expansions inside the canonical
homogeneous inclusion. This uses the existing quotient scalar action on the graded
ring without introducing a second scalar action on its homogeneous pieces.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct BigOperators

namespace Ideal

/-- Multiplication by the residue-fibre initial form of `a`, using the coefficient
map `φ : R/I → K`. The data are the actual tensor-product multiplication, with
initial form `a mod I^(n+1)` included in degree `n` and tensored with `1`.
Source: the fibre multiplication in step 3 of the DAG's filtered-algebra synthesis
(blueprint: lem-trf-flat-graded-fibre-regular-lift). -/
noncomputable def associatedGradedFibreMul {R : Type u} [CommRing R]
    (I : Ideal R) {K : Type v} [CommRing K] (φ : (R ⧸ I) →+* K)
    (n : ℕ) (a : (I ^ n : Ideal R)) :
    @TensorProduct (R ⧸ I) _ (associatedGraded I) K _ _ _ φ.toAlgebra.toModule →
      @TensorProduct (R ⧸ I) _ (associatedGraded I) K _ _ _ φ.toAlgebra.toModule :=
  letI := φ.toAlgebra
  fun x ↦ (DirectSum.of (associatedGradedPiece I) n (Submodule.Quotient.mk a) ⊗ₜ 1) * x

/-- Every homogeneous piece of a flat associated graded algebra is finite free;
an initial form regular on the closed fibre is injective on every homogeneous
piece and its representative is a nonzerodivisor of the original ring.
Source: the DAG's filtered-algebra synthesis, supported by Stacks Project,
Algebra, Tags 00NZ, 00ME and 00IQ(2)
(blueprint: lem-trf-flat-graded-fibre-regular-lift).

Proof: (1) The quotient A=R/I is Noetherian local. Generators of the ideal I^j
map to generators of G_j=I^j/I^(j+1) over A, since I annihilates G_j.
(2) Homogeneous inclusion and projection split G_j off G. Tensor an injection
with this splitting to deduce flatness of G_j from flatness of G. Apply
lem-weil-pbc-finite-flat-local-free (Module.free_of_flat_of_isLocalRing, Tag 00NZ).
A finite generating family has finite union of basis supports, giving a finite
basis and precisely the unique coefficient expansions in the first conclusion.
(3) Identify M tensor_A k with M/nM by x tensor c mapping to c*x modulo nM,
with inverse [x] mapping to x tensor 1. The tensor-induced homogeneous inclusion
has a retraction. On its image, multiplication by the fibre initial form is
multiplication by alpha on G_j, tensored with k, then homogeneous inclusion.
Consequently injectivity on the whole fibre gives injectivity modulo n of this
map G_j to G_(n+j).
(4) Apply lem-weil-pbc-flat-mod-injective (flat_mod_injective, Tag 00ME) to
A to A with the identity local map, finite source G_j and flat target G_(n+j).
It gives injectivity on each graded piece; the flat-cokernel clause is unused.
(5) If a*b=0, prove b belongs to I^j for every j, starting with I^0=R.
Its class in G_j is killed by alpha, so injectivity makes the class zero and
puts b in I^(j+1). This also works when n=0.
(6) I is contained in the maximal ideal, which is the local Jacobson radical.
Apply lem-weil-pbc-krull-intersection-jacobson
(Ideal.iInf_pow_smul_eq_bot_of_le_jacobson, Tag 00IQ(2)) to the finite module R.
The intersection of the powers of I is zero, so b=0. No reducedness or
characteristic assumption is used. -/
theorem flat_graded_fibre_regular_lift
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    [Module.Flat (R ⧸ I) (associatedGraded I)] :
    (∀ j : ℕ, ∃ (r : ℕ) (v : Fin r → associatedGradedPiece I j),
      ∀ x : associatedGradedPiece I j, ∃! c : Fin r → (R ⧸ I),
        (∑ i : Fin r, c i • DirectSum.of (associatedGradedPiece I) j (v i)) =
          DirectSum.of (associatedGradedPiece I) j x) ∧
    (∀ (n : ℕ) (a : (I ^ n : Ideal R)),
      Function.Injective (associatedGradedFibreMul I (Ideal.Quotient.factor hI) n a) →
      (∀ j : ℕ, Function.Injective
        (associatedGradedMul I n j (Submodule.Quotient.mk a))) ∧
      ∀ b : R, a.val * b = 0 → b = 0) := by
  sorry

end Ideal
