/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverCyclicChartModel
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.EtaleRegularDivisorBaseChange

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Cyclic orbit charts for a cover split by a root extension

Source: Stacks Project, Tag 0EYG, final paragraph on intermediate root extensions,
and finite etale descent (Tags 02LA and 02VN).
(blueprint: lem-sbc-root-split-cover-prescribed-cyclic-charts)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Classification of a root-split cover retaining the specified equation.

Source: Stacks Project, Tag 0EYG, intermediate-root and descent paragraphs;
Tags 02LA and 02VN for faithfully flat descent.
(blueprint: lem-sbc-root-split-cover-prescribed-cyclic-charts)

Proof: The punctured n-th root map is finite etale and faithfully flat over D(g).
The splitting therefore descends finiteness and etaleness to the factorization j.
At y, pass to the strict henselization A. Flatness preserves g as a nonzerodivisor;
A and A/(g) are regular local domains, so g is prime. The root ring is regular
local and strictly henselian. Hensel lifting supplies all n-th roots of unity.
Its punctured spectrum is connected and is a cyclic torsor over D(g). The splitting
identifies the descent datum with a cyclic permutation action on Fin d. Decompose
this set into orbits of lengths e dividing n. The stabilizer of each orbit fixes
the intermediate root t^(n/e), whose e-th power is exactly g. Normality identifies
the orbit algebra with the punctured e-th root algebra. Descend these finitely
presented isomorphisms, inverses and projection identities to a pointed affine
etale neighborhood. The equation remains the image of the original g throughout.
Each e divides the unit n, hence is a unit. Etale base change preserves regularity
of the base and quotient; flatness preserves the nonzerodivisor. Finite products
combine the orbit charts. For d = 0 use the empty product; for n = 1 every orbit
has length one. -/
theorem root_split_cover_prescribed_cyclic_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    [IsRegularRing R] (hg : IsSMulRegular R g)
    [IsRegularRing (R ⧸ Ideal.span {g})]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap R A g)
    ∀ (δ : pullback p (V.ι ≫ q) ≅ ∐ fun _ : Fin d ↦ V.toScheme),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 V.toScheme) =
        pullback.snd p (V.ι ≫ q) →
    ∃ (S : CommRingCat.{u}) (ψ : Spec S ⟶ Spec R) (z : Spec S),
      Etale ψ ∧ ψ z = y ∧
      let h := (Spec.preimage ψ).hom g
      ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        IsRegularRing S ∧ IsSMulRegular S h ∧
        IsRegularRing (S ⧸ Ideal.span {h}) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C h)) h)
        ∃ γ : pullback p ψ ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p ψ := by
  dsimp only
  intro δ hδ
  obtain ⟨S, φ, z, hφ, hz, m, e, he, γ, hγ⟩ :=
    root_split_cover_cyclic_chart_model R g n hn hg p hj d y δ hδ
  obtain ⟨hS, hh, hSh⟩ := etale_regular_divisor_base_change R S φ g hg hφ
  refine ⟨S, Spec.map (CommRingCat.ofHom φ), z, hφ, hz, ?_⟩
  rw [Spec.preimage_map]
  exact ⟨m, e, he, hS, hh, hSh, γ, hγ⟩

end AlgebraicGeometry.Scheme
