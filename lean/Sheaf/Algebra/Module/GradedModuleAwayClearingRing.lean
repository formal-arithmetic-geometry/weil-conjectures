/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# GradedModuleAwayClearingRing

Source: Stacks Project, Constructions, Lemma 01M4.
-/

@[expose] public section

universe u v

namespace LocalizedModule

set_option linter.unusedVariables false in
/-- Clearing denominators for degree-zero ring restriction maps.
Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open), (1)(e).
(blueprint: lem-weil-pbc-graded-module-away-clearing-ring)

Proof: If g is nilpotent, S_g and its homogeneous degree-zero subring R_g are zero;
choose n = 0 and x = 0. Otherwise the homogeneous fraction representation gives
y = b/g^n with b homogeneous of degree n*deg(g), as in
HomogeneousLocalization.Away.mk_surjective. Put d = deg(f), delta = deg(g), and
B = g^(n*(d-1))*b. The graded multiplication rule gives degree n*d*delta for B,
so x = B/f^(n*delta) lies in R_f. Because lambdaS preserves S and f/1 is a unit,
it sends a fraction c/f^m to c/f^m in S_g. In particular it sends U to g^d/f^delta.
Consequently lambdaS(x) = B/f^(n*delta) = (g^d/f^delta)^n*y in S_g, using d > 0
and n*(d-1)+n = n*d. The compatibility of rhoS with lambdaS and injectivity of
the inclusion R_g into S_g yield rhoS(x) = rhoS(U)^n*y. Only units in S_g are
canceled, so zero divisors, zero numerators, and n = 0 cause no exception. -/
theorem gradedModuleAwayClearingRing
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M]
    (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 z → a • x ∈ 𝓜 (n + z)) :
    let F := {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
    let R := fun f : F ↦ HomogeneousLocalization.Away 𝒜 f.val.1
    let L := fun f : F ↦ Localization.Away f.val.1
    let N := fun f : F ↦ LocalizedModule.Away f.val.1 M
    let Rel := fun f g : F ↦ ∃ (e k : ℕ) (a : S),
      0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1
    letI : ∀ f : F, Module (R f) (N f) :=
      fun f ↦ Module.compHom (N f) (algebraMap (R f) (L f))
    ∀ (Z : ∀ f : F, Submodule (R f) (N f)),
      (∀ f : F, (Z f : Set (N f)) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)) →
    ∀ (lambda : ∀ (f g : F), Rel f g → N f →ₗ[S] N g)
      (lambdaS : ∀ (f g : F), Rel f g → L f →+* L g)
      (rho : ∀ (f g : F), Rel f g → Z f →+ Z g)
      (rhoS : ∀ (f g : F), Rel f g → R f →+* R g)
      (U : ∀ (f g : F), R f),
      (∀ (f g : F), (U f g).val = Localization.mk (g.val.1 ^ f.val.2)
        (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1)) ∧
      (∀ (f g : F) (p : Rel f g),
        IsUnit (algebraMap S (L g) f.val.1) ∧
        Function.Bijective (fun x : N g ↦ f.val.1 • x) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k →
          g.val.1 ^ e = a * f.val.1 →
          algebraMap S (L g) f.val.1 * Localization.mk a
            (⟨g.val.1 ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers g.val.1) = 1) ∧
        (∀ x : M, lambda f g p (mk x 1) = mk x 1) ∧
        (∀ T : N f →ₗ[S] N g,
          (∀ x : M, T (mk x 1) = mk x 1) → T = lambda f g p) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k →
          g.val.1 ^ e = a * f.val.1 → ∀ (x : M) (m : ℕ),
          lambda f g p (mk x (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1)) =
            mk (a ^ m • x)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1)) ∧
        (∀ r : S, lambdaS f g p (algebraMap S (L f) r) = algebraMap S (L g) r) ∧
        (∀ (r : L f) (x : N f),
          lambda f g p (r • x) = lambdaS f g p r • lambda f g p x) ∧
        (∀ x : Z f, (rho f g p x : N g) = lambda f g p (x : N f)) ∧
        (∀ r : R f, (rhoS f g p r).val = lambdaS f g p r.val) ∧
        (∀ (r : R f) (x : Z f), rho f g p (r • x) = rhoS f g p r • rho f g p x) ∧
        IsUnit (rhoS f g p (U f g))) →
    ∀ (f g : F) (p : Rel f g),
      (∀ y : R g, ∃ (n : ℕ) (x : R f),
        (rhoS f g p (U f g)) ^ n * y = rhoS f g p x) := by sorry

end LocalizedModule
