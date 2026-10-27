module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.FieldTheory.SeparableExtension

import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal

/-! # Index one and separable residues after normalized finite base change

Source: Stacks Project, More on Algebra, Tags 09EQ, 09E7 and Remark 09EM,
with the Noetherian comparison qualification in the node.
(blueprint: lem-sfb-dvr-index-one-separable-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace IsDiscreteValuationRing

/-- Index one and residue separability survive normalized finite base change.
The map f is characterized in the ambient reduced tensor algebra, hence is the
canonical normalization map, not a freely chosen ring map. The global equivalence
is likewise required to equal the canonical comparison on every pure tensor.

Source: Stacks Project, Tags 09EQ, 09E7 and 09EM, with the Noetherian
qualification for the global comparison recorded in the node.
(blueprint: lem-sfb-dvr-index-one-separable-base-change).

Proof:
1. Apply lem-sfb-dvr-algebraic-normalization-structure, case (a), to N/K.
   The contraction n of q is maximal and V = R_n and D = C_q are DVRs.
   The embeddings into the selected field factor give injective local maps
   from V and B into D. Choose uniformizers pi of A and t of V.
2. Localize U = B tensor_A V at the contraction of the maximal ideal of D,
   obtaining S and its local map phi to D. Reduction modulo t identifies
   S/tS with a prime localization of F tensor_k kappa(n), where F and k
   are the residues of B and A. By lem-sfb-separable-residue-finite-tensor-fields
   this is a field separable over kappa(n), so the maximal ideal of S is tS.
3. Clearing finitely many denominators in monic polynomials gives R[1/pi] = N
   and identifies the fraction fields of D and the image of S with the selected
   field factor of the reduced tensor algebra. Factor idempotents are integral.
4. The D-valuation bounds the powers of t dividing any element of S whose
   image is nonzero. Divide by the largest power; the remaining factor is a unit.
   Thus every nonzero element in the image is a power of t times a unit.
   The common fraction field and nonnegative valuation make phi surjective;
   its kernel is the intersection of all powers of tS.
5. Surjectivity and locality give the maximal ideal of D equal to tD, hence
   nD = qD. The kernel is contained in tS, giving S/tS = D/tD and therefore
   the asserted separable residue extension, with its canonical field map.
6. For the global assertion assume T = B tensor_A R is Noetherian.
   By lem-weil-pbc-pid-torsion-free-module-flat, B is flat over A. Tensoring
   R into N is injective, pi is regular on T, and T[1/pi] = L tensor_K N.
   The comparison has nilradical kernel and is integral. Apply
   lem-weil-pbc-integral-injective-lying-over after reduction to lift primes.
7. A prime over a maximal ideal of T is maximal by integrality. Its local
   comparison is the map S to D above, now with S Noetherian. Apply
   lem-weil-pbc-krull-intersection-jacobson to S and its principal maximal ideal.
   Its kernel is zero, so each maximal localization of T is a DVR. All prime
   localizations are integrally closed domains, proving normality of T.
8. The kernel vanishes at all maximal ideals, hence is zero. Generic localization
   identifies L tensor_K N with its reduction. This is the total fraction ring
   of T: a regular element is nonzero in every field factor and is thus invertible.
   By lem-weil-pbc-normal-ring-integrally-closed-total every element of C, integral
   over B and thus over T, lies in T. This proves the canonical comparison isomorphism.
-/
theorem dvr_index_one_separable_base_change
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (hindex : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hsep : Algebra.IsSeparableExtension
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    (N : Type y) [Field N] [Algebra K N] [FiniteDimensional K N]
    [Algebra A N] [IsScalarTower A K N] :
    ∃ f : integralClosure A N →+*
        integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)),
      (∀ r : integralClosure A N,
        (f r : (L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)) =
          Ideal.Quotient.mk _ (Algebra.TensorProduct.includeRight (r : N))) ∧
      (∀ (q : Ideal (integralClosure B
          ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)))) [q.IsMaximal],
        (q.comap f).IsMaximal ∧
        IsDiscreteValuationRing (Localization.AtPrime (q.comap f)) ∧
        (∃ hdom : IsDomain (Localization.AtPrime q),
          @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
        (q.comap f).map ((algebraMap _ (Localization.AtPrime q)).comp f) =
          q.map (algebraMap _ (Localization.AtPrime q)) ∧
        @Algebra.IsSeparableExtension (q.comap f).ResidueField q.ResidueField _ _
          (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra) ∧
      (IsNoetherianRing (B ⊗[A] integralClosure A N) →
        IsReduced (L ⊗[K] N) ∧
        ∃ e : (B ⊗[A] integralClosure A N) ≃ₐ[B]
            integralClosure B ((L ⊗[K] N) ⧸ nilradical (L ⊗[K] N)),
          ∀ (b : B) (r : integralClosure A N),
            e (b ⊗ₜ[A] r) = algebraMap B _ b * f r) := by
  sorry

end IsDiscreteValuationRing
