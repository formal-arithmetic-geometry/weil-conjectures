/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Restriction maps between degree-zero graded module localizations

Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open),
parts (1)(a),(c),(d),(e),(g),(h); Algebra, Section 00JM
(blueprint: lem-weil-pbc-graded-module-away-restriction).
-/

@[expose] public section

universe u v

namespace LocalizedModule

/-- Restriction maps, their principal localization comparisons, and compatibility.
The positive homogeneous elements are indexed by `F`; `Rel f g` records a homogeneous
relation `g ^ e = a * f`. The submodules `Z f` have exactly the equal-degree fractions
as carriers; the scalar action is restricted from the ordinary localized module.

Source: Stacks Project, Constructions, Lemma 01M4 (lemma-standard-open).
(blueprint: lem-weil-pbc-graded-module-away-restriction)

Proof:
1. If the target denominator is nilpotent, its localizations are zero; otherwise the
   grading determines the degree of the homogeneous multiplier in the relation.
2. Apply the ordinary module localization universal property: `f` is a unit after
   localizing at `g`, with inverse `a / g ^ e`. This gives the unique map `lambda`.
3. Its fraction formula gives the ring map `lambdaS` and semilinearity.
4. Degree bookkeeping restricts these maps to `rho` and `rhoS` on equal-degree fractions.
5. Uniqueness gives identity and composition, independently of the relation witnesses.
6. The image of `u = g ^ deg f / f ^ deg g` is a unit, with inverse
   `f ^ deg g / g ^ deg f` in the target degree-zero ring.
7. The module localization universal property gives `theta`, and the ring version gives
   `thetaS`, with their fraction formula and semilinearity.
8. For surjectivity, rewrite `y / g ^ n` as `g ^ (n * (deg f - 1)) y / g ^ (n * deg f)`.
9. For injectivity, a target-zero fraction is killed by a power of `g`, hence by a power
   of `u` before the second localization. Thus both comparison maps are isomorphisms.
10. For a third denominator `h`, transitivity and the ring isomorphism make `u` a unit
    after localizing at `u'`; the fraction formulas give the canonical map `kappa` and
    the commuting square. These use the three localization definition dependencies.
-/
theorem gradedModuleAwayRestriction
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
    ∃ (Z : ∀ f : F, Submodule (R f) (N f)),
      (∀ f : F, (Z f : Set (N f)) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)) ∧
    ∃ (lambda : ∀ (f g : F), Rel f g → N f →ₗ[S] N g)
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
        IsUnit (rhoS f g p (U f g))) ∧
      (∀ (f : F) (p : Rel f f),
        (∀ x : Z f, rho f f p x = x) ∧ (∀ r : R f, rhoS f f p r = r)) ∧
      (∀ (f g h : F) (e e' : ℕ) (a a' : S),
        g.val.1 ^ e = a * f.val.1 → h.val.1 ^ e' = a' * g.val.1 →
        h.val.1 ^ (e * e') = (a' ^ e * a) * f.val.1) ∧
      (∀ (f g h : F) (p : Rel f g) (q : Rel g h), Rel f h ∧
        ∀ t : Rel f h,
          (∀ x : Z f, rho g h q (rho f g p x) = rho f h t x) ∧
          (∀ r : R f, rhoS g h q (rhoS f g p r) = rhoS f h t r)) ∧
    ∃ (theta : ∀ (f g : F), Rel f g → LocalizedModule.Away (U f g) (Z f) ≃+ Z g)
      (thetaS : ∀ (f g : F), Rel f g → Localization.Away (U f g) ≃+* R g),
      (∀ (f g : F) (p : Rel f g),
        (∀ r : R f, thetaS f g p (algebraMap (R f) (Localization.Away (U f g)) r) =
          rhoS f g p r) ∧
        (∀ x : Z f, theta f g p (mk x 1) = rho f g p x) ∧
        (∀ (x : Z f) (k : ℕ), (rhoS f g p (U f g)) ^ k •
          theta f g p (mk x (⟨(U f g) ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers (U f g))) =
            rho f g p x) ∧
        (∀ (r : Localization.Away (U f g)) (x : LocalizedModule.Away (U f g) (Z f)),
          theta f g p (r • x) = thetaS f g p r • theta f g p x)) ∧
      (∀ (f g h : F) (p : Rel f g) (q : Rel g h) (t : Rel f h),
        IsUnit (algebraMap (R f) (Localization.Away (U f h)) (U f g)) ∧
        ∃ kappa : LocalizedModule.Away (U f g) (Z f) →ₗ[R f]
          LocalizedModule.Away (U f h) (Z f),
          (∀ x : Z f, kappa (mk x 1) = mk x 1) ∧
          (∀ K : LocalizedModule.Away (U f g) (Z f) →ₗ[R f]
            LocalizedModule.Away (U f h) (Z f),
            (∀ x : Z f, K (mk x 1) = mk x 1) → K = kappa) ∧
          (∀ x : LocalizedModule.Away (U f g) (Z f),
            rho g h q (theta f g p x) = theta f h t (kappa x))) := by
  sorry

end LocalizedModule
