module

public import Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-! # Completed polynomial deformation test rings

Source: Stacks Project, Formal Deformation Theory, Tag 06SM, lemma-exists-smooth,
the polynomial completion construction; Commutative Algebra, Tag 0316
(blueprint: lem-sfb-artin-completed-polynomial-test-ring).

The completion is the literal completion of the polynomial ring, without first
localizing it. Its canonical augmentation is Mathlib's `AdicCompletion.kerProj`.
The two finite variable blocks retain the distinguished variables killed by e.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ArtinDeformation

/-- The completion of R[Y₁,…,Yₛ,X₁,…,X_d] at the kernel of its specified augmentation.
Source: Stacks, Tag 06SM, polynomial completion construction
(blueprint: lem-sfb-artin-completed-polynomial-test-ring). -/
abbrev PolynomialTestCompletion {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {s d : ℕ} (e : MvPolynomial (Fin s ⊕ Fin d) R →ₐ[R] k) :=
  AdicCompletion (RingHom.ker e.toRingHom) (MvPolynomial (Fin s ⊕ Fin d) R)

/-- The canonical polynomial-to-completion R-algebra map.
Source: Stacks, Tag 06SM, polynomial completion construction
(blueprint: lem-sfb-artin-completed-polynomial-test-ring). -/
def polynomialTestInclusion {R k : Type u} [CommRing R] [Field k] [Algebra R k]
    {s d : ℕ} (e : MvPolynomial (Fin s ⊕ Fin d) R →ₐ[R] k) :
    MvPolynomial (Fin s ⊕ Fin d) R →ₐ[R] PolynomialTestCompletion e :=
  IsScalarTower.toAlgHom R (MvPolynomial (Fin s ⊕ Fin d) R) (PolynomialTestCompletion e)

/-- The polynomial completion is complete Noetherian local, has the canonical marked
residue field k and Artinian infinitesimal quotients, represents polynomial maps to
Artinian tests, lifts through all test surjections, and every local map to a test is
continuous and factors through a positive infinitesimal quotient.

Source: Stacks, Tag 06SM (lemma-exists-smooth), polynomial completion construction,
and Tag 0316 (lemma-completion-Noetherian-Noetherian)
(blueprint: lem-sfb-artin-completed-polynomial-test-ring).

Proof:
1. Finite-type Noetherian permanence (lem-weil-pbc-finite-type-algebra-noetherian)
   makes P Noetherian, including s=d=0. Its augmentation kernel q is maximal and
   finitely generated, since P/q=k.
2. Apply lem-weil-pbc-adic-completion-noetherian and
   lem-weil-pbc-module-completion-complete to P and q. With J=qS, their projections
   give S/J^n=P/q^n, completeness, separatedness, and S/J=k.
3. If u is outside J, choose v inverse modulo J and put t=1-uv. The compatible
   sums 1+t+…+t^(n-1) lift by completeness; separatedness shows their lift inverts
   1-t. Thus u is a unit. Elements of J cannot be units, so J is the maximal ideal.
4. The lemma lem-weil-pbc-noetherian-local-quotient-artinian-local makes every
   S/L with J^n ≤ L ≤ J Artinian local. Its residue map is the induced canonical
   augmentation and its residue field is k. This includes L=J^n.
5. By lem-weil-pbc-artinian-local-noetherian-nilpotent, a positive power m_A^N is
   zero. Every local map S→A kills J^N, hence factors through S/J^N and is continuous
   for the maximal-ideal topologies. This does not require residue preservation.
6. For f:P→A over e, f(q) lies in m_A. Factor f through P/q^N and compose with the
   completion projection to extend it to S. The extension preserves residues and
   is local. Conversely every local map kills J^N. Surjectivity of P→S/J^N proves
   uniqueness. Restriction therefore gives exactly the stated bijection.
7. For a surjection B→A, lift the finitely many polynomial variable images to B,
   using def-weil-pbc-mv-polynomial-ring. Their residues give e, so step 6 extends
   this polynomial lift. Uniqueness in step 6 proves the required equality over A.
   No small-extension condition is needed; the empty family uses the structure map.
-/
theorem completedPolynomial_testRing
    (R k : Type u) [CommRing R] [IsNoetherianRing R] [Field k] [Algebra R k]
    [Algebra.FiniteType R k] (s d : ℕ)
    (e : MvPolynomial (Fin s ⊕ Fin d) R →ₐ[R] k) (he : Function.Surjective e)
    (hX : ∀ i : Fin d, e (MvPolynomial.X (Sum.inr i)) = 0) :
    ∃ (_ : IsLocalRing (PolynomialTestCompletion e)),
      IsNoetherianRing (PolynomialTestCompletion e) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (PolynomialTestCompletion e))
        (PolynomialTestCompletion e) ∧
      IsLocalRing.maximalIdeal (PolynomialTestCompletion e) =
        (RingHom.ker e.toRingHom).map (polynomialTestInclusion e).toRingHom ∧
      (∃ ρ : IsLocalRing.ResidueField (PolynomialTestCompletion e) ≃ₐ[R] k,
        ∀ z : PolynomialTestCompletion e,
          ρ (IsLocalRing.residue (PolynomialTestCompletion e) z) =
            AdicCompletion.kerProj he z) ∧
      (∀ n : ℕ, 1 ≤ n →
        ∃ ρ : (PolynomialTestCompletion e ⧸
            IsLocalRing.maximalIdeal (PolynomialTestCompletion e) ^ n) →ₐ[R] k,
          IsTestAlgebra R k (A := CommAlgCat.of R (PolynomialTestCompletion e ⧸
            IsLocalRing.maximalIdeal (PolynomialTestCompletion e) ^ n)) ρ ∧
          ρ.comp (Ideal.Quotient.mkₐ R _) = AdicCompletion.kerProj he) ∧
      (∀ L : Ideal (PolynomialTestCompletion e),
        (∃ n : ℕ, 1 ≤ n ∧ IsLocalRing.maximalIdeal (PolynomialTestCompletion e) ^ n ≤ L) →
        L ≤ IsLocalRing.maximalIdeal (PolynomialTestCompletion e) →
        ∃ ρ : (PolynomialTestCompletion e ⧸ L) →ₐ[R] k,
          IsTestAlgebra R k (A := CommAlgCat.of R (PolynomialTestCompletion e ⧸ L)) ρ ∧
          ρ.comp (Ideal.Quotient.mkₐ R L) = AdicCompletion.kerProj he) ∧
      (∀ A : TestCategory R k,
        Set.BijOn (fun h : PolynomialTestCompletion e →ₐ[R] ring A ↦
          h.comp (polynomialTestInclusion e))
          {h | IsLocalHom h ∧ (residue A).comp h = AdicCompletion.kerProj he}
          {f | (residue A).comp f = e}) ∧
      (∀ (A B : TestCategory R k) (π : B ⟶ A), Function.Surjective (map π) →
        ∀ h : PolynomialTestCompletion e →ₐ[R] ring A,
          IsLocalHom h → (residue A).comp h = AdicCompletion.kerProj he →
          ∃ g : PolynomialTestCompletion e →ₐ[R] ring B,
            IsLocalHom g ∧ (residue B).comp g = AdicCompletion.kerProj he ∧
            (map π).comp g = h) ∧
      (∀ (A : TestCategory R k) (h : PolynomialTestCompletion e →ₐ[R] ring A),
        IsLocalHom h →
          @Continuous (PolynomialTestCompletion e) (ring A)
            (IsLocalRing.maximalIdeal (PolynomialTestCompletion e)).adicTopology
            (IsLocalRing.maximalIdeal (ring A)).adicTopology h ∧
          ∃ n : ℕ, 1 ≤ n ∧
            ∃ g : (PolynomialTestCompletion e ⧸
                IsLocalRing.maximalIdeal (PolynomialTestCompletion e) ^ n) →ₐ[R] ring A,
              g.comp (Ideal.Quotient.mkₐ R _) = h) := sorry

end AlgebraicGeometry.ArtinDeformation
