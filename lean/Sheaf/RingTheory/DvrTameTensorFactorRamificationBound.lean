/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Sheaf.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra

/-! # A numerical bound for tame DVR tensor factors

Source: Stacks Project, Tags 0BRM, 09EV, 09EM, 09E7 and 032L.
(blueprint: lem-sbc-dvr-tame-tensor-factor-ramification-bound) -/

@[expose] public section
universe u
open scoped TensorProduct
namespace RingTheory

/-- Quantitative tame ramification bound for a normalized tensor factor.

Source: Stacks Project, Tags 0BRM (Abhyankar), 09EV (uniformizer roots),
09EM (normalized tensor factors), 09E7 (index-one criterion), and 032L.
(blueprint: lem-sbc-dvr-tame-tensor-factor-ramification-bound)

Proof: The assumed injection A -> F, and the field inclusion E -> F, embed
B in A compatibly. Since A is finite and normal over B it is the normalization
of B in Frac(A). Inverting B minus zero identifies F with a field factor of
E tensor_Frac(B) Frac(A). Hence F/Frac(A) is finite separable. Clearing
denominators in a monic algebraic equation shows every element of F is a
fraction of elements of S,
so Frac(S) = F. The finite normalization S is Dedekind, and Q is nonzero
because it contracts to m_A; thus S_Q is a DVR. The same argument makes C a Dedekind domain.

Set t = r/gcd(r,n), which is positive and divides r. Adjoin a t-th root of a
uniformizer of A. For t = 1 use A itself; otherwise 09EV gives a DVR A'
with fraction field K', ramification index t over A, and therefore index
n*t = lcm(r,n) over B. The extension K'/Frac(A) is separable since t is a
unit. The root ring A' is also the normalization of B in K': it is integral
over B and normal, so any element of K' integral over B belongs to A'.
Choose a field factor F' of F tensor_Frac(A) K', with the induced compatible
embeddings of F and K'. Normalize S in F'; this is finite by 032L since
F'/F is finite separable. Choose a prime above Q by lying over and write T
for its local DVR. Its contraction in A' is the maximal ideal: it lies over
m_A in the integral local extension A'/A. Thus A' maps locally into T.
Its contraction R in C lies above m_B. The index e of C_R/B divides r;
its residue extension is separable since its inseparable degree is a power
of the residue characteristic and divides the residue degree, which divides
the unit r. Thus C_R/B is tame, and e divides n*t.

Apply 0BRM to C_R/B and K'/Frac(B), at the prime whose base DVR is A'.
Integrality over A, B and C agrees by transitivity, so T is the corresponding
normalized tensor factor of 09EM. By 09E7 its index over A' is one.
Multiplicativity in the towers A -> A' -> T and A -> S_Q -> T gives
 t = e(T/A) = e(T/S_Q) * e(S_Q/A).
Consequently e(S_Q/A) divides t and is at most t. The DVR index equals the
length of S_Q/m_A S_Q, which is Q.ramificationIdx A. -/
theorem dvr_tame_tensor_factor_ramificationIdx_le
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (n : ℕ) (hnpos : 0 < n) (r : ℕ) (hrpos : 0 < r) (hr : IsUnit (r : B))
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra B A] [Module.Finite B A]
    (hindex : (IsLocalRing.maximalIdeal B).map (algebraMap B A) =
      IsLocalRing.maximalIdeal A ^ n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E]
    (hE : FiniteDimensional (FractionRing B) E ∧ Algebra.IsSeparable (FractionRing B) E) :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let C := integralClosure B E
    Module.Finite B C →
    (∀ (R : Ideal C) (hR : R.IsPrime),
      letI := hR
      R.comap (algebraMap B C) = IsLocalRing.maximalIdeal B →
        R.ramificationIdx B ∣ r ∧ R.inertiaDeg B ∣ r) →
    let D := E ⊗[B] A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    let := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    Function.Injective alpha →
    let S := integralClosure A F
    Module.Finite A S →
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    let := hQ
    Q.comap (algebraMap A S) = IsLocalRing.maximalIdeal A →
      Q.ramificationIdx A ≤ r / Nat.gcd r n := by sorry

end RingTheory
