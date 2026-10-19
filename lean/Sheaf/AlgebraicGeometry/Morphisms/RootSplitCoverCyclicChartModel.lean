/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverOnDivisorCharts
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitCoverAwayDivisorCharts

/-!
# Cyclic orbit charts for a cover split by a root extension

Source: Stacks Project, Tag 0EYG, final paragraph on intermediate root extensions,
and finite etale descent (Tags 02LA and 02VN).
(blueprint: lem-sbc-root-split-cover-cyclic-chart-model)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Cyclic descent gives a root chart with equation the image of the original divisor.

Source: Stacks Project, Tag 0EYG, final intermediate-root-extension paragraph;
Tags 02LA, 02VN, 0BSK and 05N9.
(blueprint: lem-sbc-root-split-cover-cyclic-chart-model)

Proof: Descend finiteness and etaleness from the faithfully flat punctured root cover.
At a divisor point, strict henselization makes the root cover a connected cyclic torsor:
regularity of the divisor makes its equation prime, and Hensel lifts roots of unity.
The splitting induces a cyclic action on Fin d. Decompose into orbits of lengths e.
The orbit of length e is the intermediate root extension with root t^(n/e), as follows
by comparing invariant fraction fields and normal integral closures. Thus e divides n
and is a positive unit. Descend the finite collection of orbit isomorphisms, their
inverses, and their projection identities to an affine pointed etale neighborhood.
Keep the equation equal to the image of g. Away from the divisor, that image is a unit:
split the finite etale cover etale locally and use e=1 for each component. The empty
cover uses m=0. Spec of the product, restricted to the basic open, assembles the orbit
charts. This lemma supplies the model; etale preservation of regularity is separate. -/
theorem root_split_cover_cyclic_chart_model
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
    ∃ (S : CommRingCat.{u}) (φ : R →+* S) (z : Spec S),
      Etale (Spec.map (CommRingCat.ofHom φ)) ∧
      (Spec.map (CommRingCat.ofHom φ)) z = y ∧
      ∃ (m : ℕ) (e : Fin m → ℕ),
        (∀ k, 0 < e k ∧ IsUnit (e k : S)) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin m,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin m,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ e k - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  classical
  dsimp
  intro δ hδ
  by_cases hy : g ∈ y.asIdeal
  · obtain ⟨S, ψ, z, hψ, hz, m, e, he, γ, hγ⟩ :=
      root_split_cover_on_divisor_charts R g n hn hg p hj d y hy δ hδ
    refine ⟨S, ψ, z, hψ, hz, m, e, he, γ, hγ⟩
  · obtain ⟨S, φ, z, hφ, hz, hunit, γ, hγ⟩ :=
      root_split_cover_away_divisor_charts R g n hn p hj d y hy δ hδ
    refine ⟨S, φ, z, hφ, hz, d, fun _ ↦ 1, ?_, γ, hγ⟩
    intro k
    exact ⟨Nat.zero_lt_one, by simp⟩

end AlgebraicGeometry.Scheme
