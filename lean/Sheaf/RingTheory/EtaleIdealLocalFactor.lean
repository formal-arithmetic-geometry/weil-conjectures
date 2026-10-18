module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Etale local factorization of an ideal

Source: literature/stacks-project/flat.tex, Tag 0813 (blueprint: lem-trf-etale-ideal-local-factor).
-/

@[expose] public section

universe u

open scoped Polynomial

namespace AlgebraicGeometry

/--
Source: Stacks Project, Tag 0813, lemma-push-ideal, literature/stacks-project/flat.tex
(blueprint: lem-trf-etale-ideal-local-factor).

Let `φ : A →+* B` be a ring map with `Spec B → Spec A` etale, let `a : A` be a nonzerodivisor,
and let `J ⊆ B` be a finitely generated ideal with `V(J) ⊆ V(aB)`. For every prime `q` of `B`
there are a finitely generated ideal `I ⊆ A`, an element `g ∉ q` and a finitely generated ideal
`J' ⊆ B_g` with `V(I) ⊆ V(a)` and `I B_g = (J B_g) J'`.

Proof (the node's steps, Stacks 0813 with Tag 0812 as auxiliary statement):
1. By lem-weil-pbc-zero-locus-eq-iff-radical-eq, `√J` is the intersection of the primes
   containing `J`; each contains the image `a_B` of `a` since `V(J) ⊆ V(aB)`. So `a_B ∈ √J`,
   and there is `m ≥ 1` with `a_B ^ m ∈ J`. This exponent is fixed before any localization.
2. Fix `q`. The standard-etale localization lem-weil-pbc-etale-locally-standard gives `g ∉ q`,
   a monic `f ∈ A[T]` and an `A`-algebra isomorphism `θ : B_g ≃ C_h`, with `C = A[T]/(f)` and
   `h ∈ C` (the algebra `A[T][Y]/(f, Yh - 1)` identifies with `C_h`). By
   lem-weil-pbc-principal-localization-open-immersion and
   lem-weil-pbc-etale-composition-cancellation, `Spec C_h → Spec A` is etale. Put `d = deg f`;
   lem-weil-pbc-monic-quotient-free gives the free `A`-basis `1, t, …, t^(d-1)` of `C`.
3. Let `j_1, …, j_r` generate `J` and write `θ(j_i / 1) = c_i / h ^ e_i` with `c_i ∈ C`
   (def-weil-ring-localization-away). Set `K = (c_1, …, c_r, a_C ^ m) ⊆ C`. Since the `h ^ e_i`
   are units and `a_C ^ m / 1 ∈ θ(J B_g)` by step 1, `K` is finitely generated,
   `K C_h = θ(J B_g)`, and `a_C ^ m` annihilates `C / K`.
4. Using the basis of step 2, fix `π : A^d ≅ C ↠ C / K` and put `I = Fit_0(π)`. The auxiliary
   statement lem-trf-etale-fitting-trick (Tag 0812) gives `I` finitely generated and a finitely
   generated `L ⊆ C_h` with `I C_h = (K C_h) L`. With `J' = θ⁻¹(L)`, step 3 turns this into
   `I B_g = (J B_g) J'`, and `J'` is finitely generated.
5. Each `a ^ m e_i` lies in `ker π` by step 3; these rows form the diagonal matrix `a ^ m 1_d`,
   whose determinant is `a ^ (m d)` (def-weil-pbc-matrix-determinant). By the kernel-minor
   definition lem-trf-fitting-ideal-independence-base-change, `a ^ (m d) ∈ I`. If `d = 0` then
   `I = A` and `V(I) = ∅`; if `d > 0` a prime containing `I` contains `a`. So `V(I) ⊆ V(a)`.

The theorem is stated with `sorry` for the stage-2 declaration.
-/
theorem exists_fg_ideal_local_factor
    (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B)
    [AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom φ))]
    (a : A) (ha : Function.Injective (fun x : A => a * x))
    (J : Ideal B) (hJ : J.FG)
    (hV : PrimeSpectrum.zeroLocus (J : Set B) ⊆
      PrimeSpectrum.zeroLocus
        (Ideal.map φ (Ideal.span ({a} : Set A)) : Set B))
    (q : PrimeSpectrum B) :
    ∃ (I : Ideal A) (g : B),
      I.FG ∧ g ∉ q.asIdeal ∧
      ∃ (J' : Ideal (Localization.Away g)),
        J'.FG ∧
        PrimeSpectrum.zeroLocus (I : Set A) ⊆
          PrimeSpectrum.zeroLocus (Ideal.span ({a} : Set A) : Set A) ∧
        Ideal.map ((algebraMap B (Localization.Away g)).comp φ) I =
          Ideal.map (algebraMap B (Localization.Away g)) J * J' := by
  sorry

end AlgebraicGeometry
