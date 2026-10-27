/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes
public import Sheaf.RingTheory.NormalFlatHilbertConvolution
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.Blowup.Affine.Defs
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Affine
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Homogeneous additive translation symmetry at a near point

Source: Cossart--Jannsen--Saito, March 12, 2009 preprint, section 2, proof of
Theorem 2.14, printed p.36; Hironaka, Certain numerical characters of singularities,
Theorem IV (blueprint: lem-per-scheme-near-point-additive-action).

The residue-fibre tensor factors follow the existing canonical model, k tensor_A G.
The point correspondence is fixed on every homogeneous Rees monomial. No arbitrary
identification of projective schemes, reducedness, or characteristic condition is used.
-/

@[expose] public section
set_option autoImplicit false

universe u v
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- A near point lies on a homogeneous additive subgroup whose translations preserve
all equations of the normal-cone fibre, without a reducedness hypothesis.
Source: Cossart--Jannsen--Saito, proof of Theorem 2.14, printed p.36, and Hironaka,
Certain numerical characters of singularities, Theorem IV
(blueprint: lem-per-scheme-near-point-additive-action).

The grading instance is on the already defined canonical fibre pieces. The point t
is y in Proj of this fibre: hpoint specifies the canonical correspondence by the
classes of every a in I^n. Its residue field is canonically k(y) as a k-algebra.
Finite Noetherian local lengths allow the natural-valued Hilbert--Samuel convention.

Proof, following the six steps of the node:
1. Split the kernel of P_1 -> S_1 and lift a basis of S_1. An invertible linear
   substitution gives P = Q[V], with Q -> S a minimal degree-one presentation,
   K = (V) + JP, and q_y = (V) + q_0 P. Evaluation at V = 0 proves these identities.
   The inverse matrix gives the inverse substitution. Since Proj S contains t,
   S_1 is nonzero, so Q has at least one variable. Linear substitution commutes
   with zero, inversion, and addition.
2. Apply lem-per-scheme-near-point-order-generators to Q -> S. It gives homogeneous
   generators H of J of positive degree d lying in (q_0 Q_(q_0))^d. For P put
   U_d = {f in P_d | f/1 in (q_y P_(q_y))^d}. The homogeneous prime q_y is relevant.
   By lem-trf-projective-order-algebra-additive-generators, U = k[T], where T is
   the set of its positive-degree homogeneous additive polynomials.
3. The local homomorphism Q_(q_0) -> P_(q_y) preserves powers of maximal ideals,
   so every H belongs to U; each redundant variable V belongs to U_1 as well.
   They generate K. This argument also covers J = 0 and an empty generating family.
4. Set L = (T). It is homogeneous. For each t in T its positive local order and
   primality, after clearing a denominator outside q_y, give t in q_y. Thus L is
   contained in q_y and is proper. Positive degree gives zero evaluation at zero
   for every generator, hence for every element of L.
5. Additivity gives t(Z+W) = t(Z)+t(W) and t(-Z) = -t(Z). Substitute into each
   finite ideal expression to obtain inversion stability and the addition inclusion
   for every f in L. These are polynomial identities in all characteristics.
6. Modulo L(W), every element of U = k[T] satisfies u(Z+W) = u(Z). Expand g in K
   in the generators from step 3. Its translated expression modulo L(W) is a sum
   of multiples of these generators evaluated at Z, hence belongs to K(Z).
   Pull back L by the inverse linear change from step 1 to return to the given
   presentation; all the substitution inclusions are preserved. -/
theorem scheme_near_point_additive_action
    {F : Type v} [Field F] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Algebra F R] [Algebra.EssFiniteType F R]
    (I : Ideal R) [I.IsPrime] (hI : I ≤ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ I)]
    (hcomponents : ∀ p ∈ minimalPrimes R, ¬ I ≤ p)
    [Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]
    [GradedAlgebra (Ideal.normalConeFibrePiece I hI)]
    (y : AffineBlowup I)
    (hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R)
    (t : Proj (Ideal.normalConeFibrePiece I hI))
    (hpoint : ∀ (n : ℕ) (a : (I ^ n : Ideal R)),
      Ideal.normalConeFibreClass I hI n a ∈ t.asHomogeneousIdeal.toIdeal ↔
        reesMonomial I a.val a.property ∈ y.asHomogeneousIdeal.toIdeal)
    (hnear : (summation^[Cardinal.toNat
        (@Algebra.trdeg (IsLocalRing.ResidueField R)
          ((Proj (Ideal.normalConeFibrePiece I hI)).residueField t) _ _
          ((Proj.toSpecOfAlgebra (Ideal.normalConeFibrePiece I hI)).residueFieldAlgebraMap
            t).toAlgebra)]) (localFunction (AffineBlowup I) y) =
      fun n : ℕ ↦ (Module.length R
        (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))).toNat)
    (N : ℕ)
    (π : MvPolynomial (Fin N) (IsLocalRing.ResidueField R) →ₐ[IsLocalRing.ResidueField R]
      Ideal.normalConeFibre I hI)
    (hπ : Function.Surjective π)
    (hgraded : ∀ (n : ℕ) (f : MvPolynomial (Fin N) (IsLocalRing.ResidueField R)),
      f ∈ MvPolynomial.homogeneousSubmodule (Fin N) (IsLocalRing.ResidueField R) n →
        π f ∈ Ideal.normalConeFibrePiece I hI n) :
    ∃ L : Ideal (MvPolynomial (Fin N) (IsLocalRing.ResidueField R)),
      L ≠ ⊤ ∧
      @Ideal.IsHomogeneous ℕ
        (Submodule (IsLocalRing.ResidueField R)
          (MvPolynomial (Fin N) (IsLocalRing.ResidueField R)))
        (MvPolynomial (Fin N) (IsLocalRing.ResidueField R)) _ _ _
        (MvPolynomial.homogeneousSubmodule (Fin N) (IsLocalRing.ResidueField R)) _ _
        (MvPolynomial.gradedAlgebra (σ := Fin N) (R := IsLocalRing.ResidueField R)) L ∧
      L ≤ Ideal.comap π.toRingHom t.asHomogeneousIdeal.toIdeal ∧
      (∀ f ∈ L,
        MvPolynomial.eval (fun _ : Fin N ↦ (0 : IsLocalRing.ResidueField R)) f = 0 ∧
        MvPolynomial.aeval (fun i : Fin N ↦
          -(MvPolynomial.X (Sum.inl i) :
            MvPolynomial (Fin N ⊕ Fin N) (IsLocalRing.ResidueField R))) f ∈
          L.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)) ∧
        MvPolynomial.aeval (fun i : Fin N ↦
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i) :
            MvPolynomial (Fin N ⊕ Fin N) (IsLocalRing.ResidueField R))) f ∈
          L.map (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)) +
            L.map (MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N))) ∧
      (∀ g ∈ RingHom.ker π.toRingHom,
        MvPolynomial.aeval (fun i : Fin N ↦
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i) :
            MvPolynomial (Fin N ⊕ Fin N) (IsLocalRing.ResidueField R))) g ∈
          (RingHom.ker π.toRingHom).map
              (MvPolynomial.rename (Sum.inl : Fin N → Fin N ⊕ Fin N)) +
            L.map (MvPolynomial.rename (Sum.inr : Fin N → Fin N ⊕ Fin N))) := by
  sorry

end AlgebraicGeometry.HilbertSamuel
