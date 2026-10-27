/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.RingTheory.MapIntoHenselianColimit

/-!
# Pointed tensor localizations of ordinary henselizations

Source: Stacks Project, Algebra, Tag 05WP, proof, with Tags 04GS and 08HR
(blueprint: lem-trf-henselization-tensor-local-comparison).
-/

@[expose] public section
set_option autoImplicit false

universe u v w z

namespace RingHom

/-- Localization at the prime kernel of a map to a field. This is just Mathlib's
localization, with its canonical proof of primality made explicit.
Source: Stacks Project, Algebra, Tag 05WP, pointed localization in the proof
(blueprint: lem-trf-henselization-tensor-local-comparison). -/
abbrev pointedKernelLocalization {C : Type u} {K : Type v}
    [CommRing C] [Field K] (ε : C →+* K) :=
  @Localization.AtPrime C _ (RingHom.ker ε) (RingHom.ker_isPrime ε)

end RingHom

open scoped TensorProduct

namespace Algebra

/-- Pointed tensor localization comparison, without a finiteness assumption.
All residue identifications and comparison maps are characterized by structural
compatibilities. In particular, the maps under the existential quantifiers are
canonical, rather than additional input maps.

Source: Stacks Project, Algebra, Tag 05WP, proof, lines 43600--43615;
Tags 04GN, 04GQ, 04GS, 08HR and 08HT
(blueprint: lem-trf-henselization-tensor-local-comparison).

Proof plan, following the eight steps of the node:
1. Apply the henselization universal property to the residue field, which is
   henselian. The resulting residue map is inverse to the structural residue
   map: their composite on the base residue field is the identity, and the
   reverse identity follows by injectivity of field homomorphisms.
2. The local map A_p to B_q extends uniquely to a local map h from R to H
   by def-weil-pbc-henselization-at-prime. Its residue map is the structural one.
3. Balanced multiplication of the two residue maps defines epsilon. Its kernel
   is prime, and restricting to the factors gives the two contractions. Extend
   epsilon to fractions. Every residue b/t is the image of (1 tensor b)/(1 tensor t),
   proving that the residue field of the localization is exactly kappa(q).
4. lem-trf-henselization-prime-ind-etale gives A to R and B to H ind-etale.
   Base change by lem-weil-pbc-ind-etale-stability gives B to R tensor_A B.
5. Localize using the directed system of principal localizations at products of
   finite subsets of the prime complement. The empty subset supplies the original
   algebra. The fraction universal property identifies its colimit with D.
   lem-weil-pbc-etale-algebra-finite-presentation-localization makes each term
   finitely presented etale; ind-etale stability gives B to D ind-etale.
6. If D is henselian, lem-weil-pbc-map-into-henselian-colimit with prescribed
   residue identity gives local B-maps D to H and H to D. Applying its uniqueness
   to both composites makes them inverse, and gives uniqueness of e.
7. The map R to D is local by its contraction. Its composite with e and h agree
   on A_p, so the henselization universal property identifies them.
8. Send r tensor b to r tensor (b/1) and extend to the pointed localizations.
   Conversely, send r tensor (b/t) to (r tensor b)/(1 tensor t) in D. Its
   reduction is the analogous tensor residue evaluation, so all denominators
   outside its kernel become units. These fraction maps are inverse and fix
   both factors. Composing with e inverse gives the final compatibility.
-/
theorem henselization_tensor_local_comparison
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (R : Type w) [CommRing R] [Algebra (Localization.AtPrime p) R]
    [Algebra A R] [IsScalarTower A (Localization.AtPrime p) R]
    [HenselianLocalRing R] (hR : IsHenselizationAtPrime' A p R)
    (H : Type z) [CommRing H] [Algebra (Localization.AtPrime q) H]
    [HenselianLocalRing H] (hH : IsHenselizationAtPrime' B q H)
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    ∃ (iR : p.ResidueField ≃+* IsLocalRing.ResidueField R)
      (iH : q.ResidueField ≃+* IsLocalRing.ResidueField H),
      (∀ a : Localization.AtPrime p,
        iR (IsLocalRing.residue (Localization.AtPrime p) a) =
          IsLocalRing.residue R (algebraMap (Localization.AtPrime p) R a)) ∧
      (∀ b : Localization.AtPrime q,
        iH (IsLocalRing.residue (Localization.AtPrime q) b) =
          IsLocalRing.residue H (algebraMap (Localization.AtPrime q) H b)) ∧
      ∃ h : R →+* H,
        IsLocalHom h ∧
        h.comp (algebraMap (Localization.AtPrime p) R) =
          (algebraMap (Localization.AtPrime q) H).comp
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) ∧
        (∀ h' : R →+* H, IsLocalHom h' →
          h'.comp (algebraMap (Localization.AtPrime p) R) =
            (algebraMap (Localization.AtPrime q) H).comp
              (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) → h' = h) ∧
        ∃ (ε : R ⊗[A] B →+* q.ResidueField)
          (εT : R ⊗[Localization.AtPrime p] Localization.AtPrime q →+* q.ResidueField),
          (∀ (r : R) (b : B), ε (r ⊗ₜ[A] b) =
            Ideal.ResidueField.map p q (algebraMap A B) Ideal.LiesOver.over
              (iR.symm (IsLocalRing.residue R r)) * algebraMap B q.ResidueField b) ∧
          (∀ (r : R) (b : Localization.AtPrime q),
            εT (r ⊗ₜ[Localization.AtPrime p] b) =
              Ideal.ResidueField.map p q (algebraMap A B) Ideal.LiesOver.over
                (iR.symm (IsLocalRing.residue R r)) *
                  IsLocalRing.residue (Localization.AtPrime q) b) ∧
          (RingHom.ker ε).IsPrime ∧ (RingHom.ker εT).IsPrime ∧
          (RingHom.ker ε).comap
            (TensorProduct.includeLeftRingHom : R →+* R ⊗[A] B) =
              IsLocalRing.maximalIdeal R ∧
          (RingHom.ker ε).comap
            (TensorProduct.includeRight : B →ₐ[A] R ⊗[A] B).toRingHom = q ∧
          ∃ (iD : IsLocalRing.ResidueField (RingHom.pointedKernelLocalization ε) ≃+*
              q.ResidueField)
            (bD : Localization.AtPrime q →+* RingHom.pointedKernelLocalization ε)
            (α : RingHom.pointedKernelLocalization ε ≃+*
              RingHom.pointedKernelLocalization εT),
            (∀ c : R ⊗[A] B,
              iD (IsLocalRing.residue (RingHom.pointedKernelLocalization ε)
                (algebraMap (R ⊗[A] B) (RingHom.pointedKernelLocalization ε) c)) = ε c) ∧
            (∀ b : B, bD (algebraMap B (Localization.AtPrime q) b) =
              algebraMap (R ⊗[A] B) (RingHom.pointedKernelLocalization ε) (1 ⊗ₜ[A] b)) ∧
            RingHom.IndEtaleAcrossUniverses
              (bD.comp (algebraMap B (Localization.AtPrime q))) ∧
            RingHom.IndEtaleAcrossUniverses
              ((algebraMap (Localization.AtPrime q) H).comp
                (algebraMap B (Localization.AtPrime q))) ∧
            (∀ r : R, α (algebraMap (R ⊗[A] B)
                (RingHom.pointedKernelLocalization ε) (r ⊗ₜ[A] 1)) =
              algebraMap (R ⊗[Localization.AtPrime p] Localization.AtPrime q)
                (RingHom.pointedKernelLocalization εT) (r ⊗ₜ[Localization.AtPrime p] 1)) ∧
            (∀ b : Localization.AtPrime q, α (bD b) =
              algebraMap (R ⊗[Localization.AtPrime p] Localization.AtPrime q)
                (RingHom.pointedKernelLocalization εT) (1 ⊗ₜ[Localization.AtPrime p] b)) ∧
            (HenselianLocalRing (RingHom.pointedKernelLocalization ε) →
              ∃ e : RingHom.pointedKernelLocalization ε ≃+* H,
                IsLocalHom e.toRingHom ∧
                (∀ b : B, e (bD (algebraMap B (Localization.AtPrime q) b)) =
                  algebraMap (Localization.AtPrime q) H
                    (algebraMap B (Localization.AtPrime q) b)) ∧
                (∀ d : RingHom.pointedKernelLocalization ε,
                  iH.symm (IsLocalRing.residue H (e d)) =
                    iD (IsLocalRing.residue (RingHom.pointedKernelLocalization ε) d)) ∧
                (∀ e' : RingHom.pointedKernelLocalization ε ≃+* H,
                  IsLocalHom e'.toRingHom →
                  (∀ b : B, e' (bD (algebraMap B (Localization.AtPrime q) b)) =
                    algebraMap (Localization.AtPrime q) H
                      (algebraMap B (Localization.AtPrime q) b)) →
                  (∀ d : RingHom.pointedKernelLocalization ε,
                    iH.symm (IsLocalRing.residue H (e' d)) =
                      iD (IsLocalRing.residue (RingHom.pointedKernelLocalization ε) d)) →
                  e' = e) ∧
                (∀ r : R, e (algebraMap (R ⊗[A] B)
                  (RingHom.pointedKernelLocalization ε) (r ⊗ₜ[A] 1)) = h r) ∧
                (∀ r : R, (e.symm.trans α) (h r) =
                  algebraMap (R ⊗[Localization.AtPrime p] Localization.AtPrime q)
                    (RingHom.pointedKernelLocalization εT)
                      (r ⊗ₜ[Localization.AtPrime p] 1)) ∧
                (∀ b : Localization.AtPrime q,
                  (e.symm.trans α) (algebraMap (Localization.AtPrime q) H b) =
                    algebraMap (R ⊗[Localization.AtPrime p] Localization.AtPrime q)
                      (RingHom.pointedKernelLocalization εT)
                        (1 ⊗ₜ[Localization.AtPrime p] b))) := by
  sorry

end Algebra
