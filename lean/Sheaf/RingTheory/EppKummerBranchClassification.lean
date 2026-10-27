/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Sheaf.FieldTheory.MultiradicalGaloisDegree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import Sheaf.NumberTheory.DvrGaloisDegreeData
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.PrincipalIdealDomain
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk
import Mathlib.FieldTheory.KummerPolynomial

/-! # Kummer branch classification at finite level

Source: Stacks Project, More on Algebra, Tag 09F3, cases (A)--(C), and Tags 09E8,
09EM for complete normalization and normalization in products.
(blueprint: lem-sfb-epp-kummer-branch-classification)

The auxiliary definitions expand the polynomial, its quotient, and the field branch
of this statement. Pole orders are expressed by the equivalent unit presentation
`t^d * η = u`; no choice of a valuation or of a field factor is required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace IsDiscreteValuationRing

/-- The polynomial `((1 + (1 - ζ)T)^p - 1) / (1 - ζ)^p` over the fraction field.
Source: Stacks Project, More on Algebra, Tags 09F2 and 09F3.
(blueprint: lem-sfb-epp-kummer-branch-classification) -/
def eppKummerPolynomial (F : Type v) [Field F] (p : ℕ) (ζ : F) : Polynomial F :=
  Polynomial.C (((1 - ζ) ^ p)⁻¹) *
    ((1 + Polynomial.C (1 - ζ) * Polynomial.X) ^ p - 1)

/-- The actual quotient algebra `F[T]/(P(T) - η)` of Tag 09F3, not a chosen field.
Source: Stacks Project, More on Algebra, Tag 09F3.
(blueprint: lem-sfb-epp-kummer-branch-classification) -/
abbrev eppKummerAlgebra (F : Type v) [Field F] (p : ℕ) (ζ η : F) : Type v :=
  AdjoinRoot (eppKummerPolynomial F p ζ - Polynomial.C η)

/-- The field alternative of the classification, including its complete normalization,
the three possible ramification/residue behaviours, and the refinements (A)--(C).
All algebra structures are canonical: the quotient has its coefficient algebra and
its `R`-algebra is the composite through `F`. `IsField.toField` only supplies inverses
in that same quotient ring. The local map in the normalization induces the residue
field algebra used throughout. Surjectivity of that map means unchanged residue field.

Source: Stacks Project, More on Algebra, Tag 09F3, cases (A)--(C), and Tag 09E8.
(blueprint: lem-sfb-epp-kummer-branch-classification) -/
def EppKummerFieldCase
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Type v) [Field F] [Algebra R F] (p : ℕ) (ζ t : R) (η : F) : Prop :=
  let D := eppKummerAlgebra F p (algebraMap R F ζ) η
  ∃ hD : IsField D,
    letI := hD.toField
    letI : Algebra R D := ((algebraMap F D).comp (algebraMap R F)).toAlgebra
    FiniteDimensional F D ∧ Module.finrank F D = p ∧ IsGalois F D ∧
      IsCyclic (D ≃ₐ[F] D) ∧
      ∃ hS : IsDiscreteValuationRing (integralClosure R D),
        letI := hS
        let S := integralClosure R D
        ∃ hlocal : IsLocalHom (algebraMap R S),
          letI := hlocal
          IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
            (((IsLocalRing.maximalIdeal R).map (algebraMap R S) =
                IsLocalRing.maximalIdeal S ^ p ∧
              Function.Surjective
                (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))) ∨
             ((IsLocalRing.maximalIdeal R).map (algebraMap R S) =
                IsLocalRing.maximalIdeal S ∧
              FiniteDimensional (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∧
              Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) = p ∧
              (Algebra.IsSeparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
               ∀ x : IsLocalRing.ResidueField S,
                 ∃ a : IsLocalRing.ResidueField R, algebraMap _ _ a = x ^ p))) ∧
            ((∃ r : R, algebraMap R F r = η) →
              (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
                IsLocalRing.maximalIdeal S) ∧
            (∀ (d : ℕ) (a : Rˣ), 0 < d → ¬p ∣ d →
              algebraMap R F t ^ d * η = algebraMap R F (a : R) →
              (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
                  IsLocalRing.maximalIdeal S ^ p ∧
                Function.Surjective
                  (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))) ∧
            (∀ (d : ℕ) (a : Rˣ), 0 < d → p ∣ d →
              algebraMap R F t ^ d * η = algebraMap R F (a : R) →
              (∀ b : IsLocalRing.ResidueField R, b ^ p ≠ IsLocalRing.residue R (a : R)) →
              (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
                  IsLocalRing.maximalIdeal S ∧
                FiniteDimensional (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∧
                Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) = p ∧
                ∀ x : IsLocalRing.ResidueField S,
                  ∃ b : IsLocalRing.ResidueField R, algebraMap _ _ b = x ^ p)

/-- The finite-level Kummer algebra is split or a cyclic Galois field of degree `p`.
In the field case `EppKummerFieldCase` records its complete DVR normalization and
all the ramification conclusions. The next two conjuncts exclude the split case
under the respective pole hypotheses (B) and (C). In the split case the final
conjunct identifies the normalization with the embedded product `R^p`; its factors
are `R`, so each has ramification index one, as also required by (A).

Source: Stacks Project, More on Algebra, Tag 09F3, cases (A)--(C), with finite-level
condition from immediately after that lemma; complete normalization from Tag 09E8,
and product normalization from Tag 09EM.
(blueprint: lem-sfb-epp-kummer-branch-classification)

Proof (the node's nine steps):
1. By lem-sfb-epp-kummer-pole-calculus, P is integral and monic with reduction
   T^p-T. Finite level makes b=1+w^p*η a unit. The invertible affine substitution
   Y=1+wT identifies D with F[Y]/(Y^p-b); this corrects the source's printed formula.
2. Choose an algebraic closure (lem-pc-algebraic-closure-exists-unique and
   def-weil-algebraic-closure) and a root y. Apply lem-sfb-multiradical-galois-degree
   to F(y) to get degree dividing p. By lem-sfb-split-binomial-root-torsor the roots
   are the distinct y*ζ^j. In degree one, lem-pc-crt-ideal-quotient-product gives
   F^p. In degree p, evaluation is onto by lem-weil-pbc-finite-dimensional-domain-is-field,
   and is an isomorphism by the equal dimensions (lem-weil-pbc-monic-quotient-free).
   The cyclic Galois assertion is lem-exc-kummer-binomial-splitting-field.
3. Apply lem-per-complete-dvr-finite-normalization. Its normalization is local;
   lem-exc-dvr-galois-degree-data therefore gives p=e*f. Thus (e,f)=(p,1) or (1,p).
4. Apply lem-weil-pbc-separable-first-purely-inseparable and
   lem-weil-pbc-field-degree-multiplicativity to the residue extension of degree p.
   It is separable or purely inseparable. In the latter case,
   lem-weil-pbc-purely-inseparable-pth-root-tower has exactly one step; hence every
   residue element has p-th power in the base field.
5. If η is integral, R[T]/(P-η) is finite free (lem-weil-pbc-monic-quotient-free).
   Its derivative is -1 modulo t. The unit form of lem-weil-pbc-finite-algebra-local-radical
   and lem-weil-pbc-standard-etale-monic-derivative make it finite etale.
   The DVR is normal Noetherian (lem-weil-pbc-pid-noetherian-normal).
   Apply lem-sfb-finite-etale-normal-generic-components to its generic factors,
   lem-per-complete-dvr-finite-normalization for locality, and
   lem-sbc-etale-trait-stalk for the equality of maximal ideals. This gives (A).
6. If v(η)=-d, write ν for the normalized valuation on any field factor and z for T.
   By lem-weil-pbc-dvr-unit-times-uniformizer-power, ν(c)=e*v(c) on F.
   Integrality of P forces ν(z)<0; its leading term has uniquely least valuation,
   so p*ν(z)=-e*d. The same computation includes split factors, with e=1.
7. If p does not divide d, the equality forces p to divide e. No split factor is
   possible, and p=e*f implies e=p and f=1, giving (B).
8. If d=p*m and the residue of u=t^d*η is not a p-th power, put U=t^m*T.
   The scaled monic Q reduces to U^p-u_bar, irreducible by
   lem-weil-pbc-x-pow-p-minus-t-irreducible. Its residue quotient is a field by
   lem-trf-irreducible-polynomial-quotient-field. The quotient C=R[U]/Q is free
   (lem-weil-pbc-monic-quotient-free), hence a DVR with maximal ideal t*C by
   lem-sfb-finite-free-field-fibre-dvr. Its generic algebra is D and is a field
   (lem-weil-pbc-finite-dimensional-domain-is-field). Uniqueness in
   lem-per-complete-dvr-finite-normalization identifies C with S. This gives e=1
   and residue degree p, as in (C).
9. In that residue field, taking p-th powers in the basis 1,U,...,U^(p-1) lands in
   the base field. Finally, a tuple in F^p integral over R is integral in each
   coordinate, hence lies in R^p by lem-weil-pbc-pid-noetherian-normal. Conversely
   a tuple (r_j) is killed by the monic product of (X-r_j); use
   def-weil-pbc-integral-closure to identify the integral closure with R^p.
-/
theorem epp_kummer_branch_classification
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (ζ : R) (hζ : IsPrimitiveRoot ζ p) (t : R) (ht : Irreducible t) (η : F)
    (hlevel : ∃ c : R, c ∈ IsLocalRing.maximalIdeal R ∧
      algebraMap R F c = (1 - algebraMap R F ζ) ^ p * η) :
    (Nonempty (eppKummerAlgebra F p (algebraMap R F ζ) η ≃ₐ[F] (Fin p → F)) ∨
      EppKummerFieldCase R F p ζ t η) ∧
    (∀ (d : ℕ) (a : Rˣ), 0 < d → ¬p ∣ d →
      algebraMap R F t ^ d * η = algebraMap R F (a : R) →
      EppKummerFieldCase R F p ζ t η) ∧
    (∀ (d : ℕ) (a : Rˣ), 0 < d → p ∣ d →
      algebraMap R F t ^ d * η = algebraMap R F (a : R) →
      (∀ b : IsLocalRing.ResidueField R, b ^ p ≠ IsLocalRing.residue R (a : R)) →
      EppKummerFieldCase R F p ζ t η) ∧
    (integralClosure R (Fin p → F) : Set (Fin p → F)) =
      {x | ∀ j : Fin p, ∃ r : R, algebraMap R F r = x j} := by
  sorry

end IsDiscreteValuationRing
