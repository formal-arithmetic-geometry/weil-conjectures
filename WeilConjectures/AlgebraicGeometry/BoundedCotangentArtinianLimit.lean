/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.RingTheory.FiniteModuleComplete

/-! # Artinian inverse limits with bounded cotangent dimension

Source: Stacks Project, Formal Deformation Theory, Tag 06SF (lemma-limit-artinian)
(blueprint: lem-sfb-bounded-cotangent-artinian-limit).

The index `n : ℕ` denotes the positive level `n + 1` of the source. The limit is
literally a subalgebra of the product, with its inherited componentwise operations.
Its augmentation is the marked residue of its zeroth coordinate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [Field k] [Algebra R k]

/-- The ring of compatible sequences, as an equalizer subalgebra of the product.
Its `R`-structure is diagonal and its ring operations are componentwise.
Source: Stacks Project, Tag 06SF
(blueprint: lem-sfb-bounded-cotangent-artinian-limit). -/
def artinianSequenceLimit (A : ℕ → TestCategory R k)
    (q : ∀ n : ℕ, A (n + 1) ⟶ A n) : Subalgebra R (∀ n : ℕ, ring (A n)) :=
  AlgHom.equalizer
    (AlgHom.pi (fun n : ℕ ↦ (map (q n)).comp
      (Pi.evalAlgHom R (fun i : ℕ ↦ ring (A i)) (n + 1))))
    (AlgHom.id R (∀ n : ℕ, ring (A n)))

/-- The actual coordinate projection on the compatible-sequence ring.
Source: Stacks Project, Tag 06SF
(blueprint: lem-sfb-bounded-cotangent-artinian-limit). -/
def artinianSequenceProjection (A : ℕ → TestCategory R k)
    (q : ∀ n : ℕ, A (n + 1) ⟶ A n) (n : ℕ) :
    artinianSequenceLimit A q →ₐ[R] ring (A n) :=
  (Pi.evalAlgHom R (fun i : ℕ ↦ ring (A i)) n).comp (artinianSequenceLimit A q).val

/-- The canonical augmentation, given by the residue at the first positive level.
Source: Stacks Project, Tag 06SF
(blueprint: lem-sfb-bounded-cotangent-artinian-limit). -/
def artinianSequenceResidue (A : ℕ → TestCategory R k)
    (q : ∀ n : ℕ, A (n + 1) ⟶ A n) : artinianSequenceLimit A q →ₐ[R] k :=
  (residue (A 0)).comp (artinianSequenceProjection A q 0)

/-- A surjective Artinian tower of bounded cotangent dimension has a Noetherian
complete local limit, with the canonical marked residue field and surjective local
residue-preserving coordinate maps. The two filtrations are cofinal.
The intrinsic residue fields in `hbound` identify with the specified field `k`
through the markings of the tests; vector-space dimension is invariant under
these field isomorphisms. The kernel of the surjective augmentation is the maximal
ideal, which expresses the specified residue-field isomorphism without choosing it.

Source: Stacks Project, Tag 06SF (lemma-limit-artinian)
(blueprint: lem-sfb-bounded-cotangent-artinian-limit).

Proof plan, following the eight steps of the DAG node:
1. Lift coordinates recursively using surjectivity. Residues are constant along a
   compatible sequence; componentwise inverses show the augmentation kernel is
   precisely the nonunits. Thus the limit is local and each projection is local,
   surjective and preserves the marking.
2. Cotangent maps are onto. Their bounded nondecreasing dimensions stabilize.
   Lift a basis at a stable level to the limit. Nakayama
   (lem-weil-pbc-nakayama-local-generators) shows its images generate every maximal
   ideal. Artinian nilpotence (lem-weil-pbc-artinian-local-noetherian-nilpotent)
   supplies exponents `c_n` killing these ideals.
3. Lift finitely many `R`-module generators of `k` to the limit. Together with the
   maximal-ideal generators they define a polynomial map. Successively correcting
   errors in powers of each maximal ideal proves surjectivity onto every level,
   without assuming a coefficient field (def-weil-pbc-mv-polynomial-ring).
4. Complete that polynomial ring at its residue kernel. The completed-polynomial
   test-ring lemma (lem-sfb-artin-completed-polynomial-test-ring) makes it a complete
   Noetherian local ring `S` with unique compatible surjections to all levels.
   Their decreasing kernels `J_n` contain the powers with exponents `c_n`.
5. Set `J = ⋂ n, J_n`. The quotient `T = S/J` is Noetherian local, and completeness
   of finite modules (lem-weil-pbc-finite-module-complete-over-complete-noetherian)
   makes the cyclic `S`-module `T` complete for its maximal ideal.
6. Repeat the `J_n` in blocks whose endpoints grow past `c_n`. The descending-ideal
   lemma (lem-sfb-artin-descending-ideal-adic-topology) now applies with its exact
   power-index hypothesis. It proves cofinality of `J_n/J` and maximal-ideal powers.
7. Compatible coordinates in `T/(J_n/J)` give compatible residues modulo powers,
   hence a unique element of `T` by completeness. This inverts the canonical map
   from `T` to the literal limit; its kernel is zero by the definition of `J`.
8. Transport Noetherianity, completeness and both cofinality containments across
   this algebra isomorphism, which preserves all coordinates and residue maps. -/
theorem bounded_cotangent_artinian_limit
    (R k : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Field k] [Algebra R k] [Module.Finite R k]
    (A : ℕ → TestCategory R k) (q : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hq : ∀ n : ℕ, Function.Surjective (map (q n)))
    (hbound : ∃ d : ℕ, ∀ n : ℕ,
      Module.finrank (IsLocalRing.ResidueField (ring (A n)))
        (IsLocalRing.CotangentSpace (ring (A n))) ≤ d) :
    ∃ hB : IsLocalRing (artinianSequenceLimit A q),
      IsNoetherianRing (artinianSequenceLimit A q) ∧
      RingHom.ker (artinianSequenceResidue A q).toRingHom =
        @IsLocalRing.maximalIdeal (artinianSequenceLimit A q) _ hB ∧
      IsAdicComplete (RingHom.ker (artinianSequenceResidue A q).toRingHom)
        (artinianSequenceLimit A q) ∧
      Function.Surjective (artinianSequenceResidue A q) ∧
      (∀ n : ℕ, Function.Surjective (artinianSequenceProjection A q n) ∧
        IsLocalHom (artinianSequenceProjection A q n) ∧
        (residue (A n)).comp (artinianSequenceProjection A q n) =
          artinianSequenceResidue A q) ∧
      (∀ r : ℕ, 1 ≤ r → ∃ n : ℕ,
        RingHom.ker (artinianSequenceProjection A q n).toRingHom ≤
          RingHom.ker (artinianSequenceResidue A q).toRingHom ^ r) ∧
      (∀ n : ℕ, ∃ r : ℕ, 1 ≤ r ∧
        RingHom.ker (artinianSequenceResidue A q).toRingHom ^ r ≤
          RingHom.ker (artinianSequenceProjection A q n).toRingHom) := sorry

end AlgebraicGeometry.ArtinDeformation
