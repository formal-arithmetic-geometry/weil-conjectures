module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Fixed-residue Artinian tests for adic formal smoothness

Source: Stacks Project, Formal Deformation Theory, Tag 0DYL, equivalence (1) and (2),
and Tag 06GC; More on Algebra, Tag 0DYG
(blueprint: lem-sfb-adic-smooth-fixed-residue-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Adic formal smoothness is equivalent to lifting continuous local algebra maps through
surjections of Artinian local algebras with the specified residue field. The residue
compatibilities are written after precomposition with the surjective residue maps, so they
express precisely that the induced maps are the identity under the given identifications.

Source: Stacks Project, Tags 0DYL, 06GC and 0DYG.
(blueprint: lem-sfb-adic-smooth-fixed-residue-lifting)

Proof: In the forward direction let I be the kernel of the Artinian surjection. By
lem-weil-pbc-artinian-local-noetherian-nilpotent the maximal ideal, and hence I, is nilpotent.
Factor the surjection through successive quotients by powers of I. Their transition kernels
are square-zero. Use def-weil-pbc-formally-smooth-adic at each step. A lift of a map killing
m_C^t kills m_C^(2t), since its image on m_C^t lies in the square-zero kernel. Its residue map
is the prescribed isomorphism, so the lift is local and respects the marking. If I = 0 the
surjection is an isomorphism and its inverse gives the lift.

Conversely, mark the residue fields in any small-extension test by transporting the marking
of C through the residue isomorphism. A local map to an Artinian ring kills a power of m_C
by lem-weil-pbc-artinian-local-noetherian-nilpotent. The assumed property supplies a lift.
Apply lem-sfb-local-square-zero-small-extension-reduction, using Noetherianity of C, to
obtain lifting for local square-zero tests with nilpotent maximal ideal, including tests
that are not Artinian. For an arbitrary square-zero diagram C -> D/J, take the inverse image
E in D of the image of C. If the map kills m_C^t and D/J is nonzero, E/J is a proper quotient
of C, local with residue field that of C. The inverse image M of its maximal ideal satisfies
M^t <= J and M^(2t) = 0. Elements outside M are invertible by lifting inverses and correcting
by 1-j for j in J. Thus E is local, its structure map is local, and C -> E/J induces a residue
isomorphism. Lift to E by the local test and compose with E -> D. If D/J = 0, square-zero of J
forces D = 0 and the unique map is the lift. This is the defining arbitrary-ring lifting
condition for adic formal smoothness. -/
theorem formallySmoothAdic_iff_fixed_residue_artinian_lifting
    (R : Type u) (C : Type v) (k : Type w)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [Algebra R C]
    [IsLocalHom (algebraMap R C)] [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [Field k] [Algebra R k] [Algebra (IsLocalRing.ResidueField R) k]
    [IsScalarTower R (IsLocalRing.ResidueField R) k]
    [Module.Finite (IsLocalRing.ResidueField R) k]
    (eC : IsLocalRing.ResidueField C ≃ₐ[R] k) :
    FormallySmoothAdic R C (IsLocalRing.maximalIdeal C) ↔
      ∀ (A' A : Type (max u v w))
        [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra R A']
        [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra R A]
        (eA' : IsLocalRing.ResidueField A' ≃ₐ[R] k)
        (eA : IsLocalRing.ResidueField A ≃ₐ[R] k)
        (p : A' →ₐ[R] A),
        IsLocalHom p → Function.Surjective p →
        (∀ a' : A', eA (IsLocalRing.residue A (p a')) =
          eA' (IsLocalRing.residue A' a')) →
        ∀ f : C →ₐ[R] A, IsLocalHom f →
          (∀ c : C, eA (IsLocalRing.residue A (f c)) =
            eC (IsLocalRing.residue C c)) →
          (∃ n : ℕ, 1 ≤ n ∧ ∀ c ∈ IsLocalRing.maximalIdeal C ^ n, f c = 0) →
          ∃ f' : C →ₐ[R] A', IsLocalHom f' ∧
            (∀ c : C, eA' (IsLocalRing.residue A' (f' c)) =
              eC (IsLocalRing.residue C c)) ∧
            (∃ n : ℕ, 1 ≤ n ∧ ∀ c ∈ IsLocalRing.maximalIdeal C ^ n, f' c = 0) ∧
            p.comp f' = f := by
  sorry

end Algebra
