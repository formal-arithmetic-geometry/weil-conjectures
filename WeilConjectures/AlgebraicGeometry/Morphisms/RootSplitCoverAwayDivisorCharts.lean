/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Algebra.Pi
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationPoint
import WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayTransportChart

/-!
# Degree-one root charts away from the divisor

Source: Stacks Project, Tag 0EYG, first paragraph of the proof (the point off the divisor),
and Tags 02LA, 02VN and 04HN.
(blueprint: lem-sbc-root-split-cover-away-divisor-charts)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option linter.unusedVariables false in
/-- A root-split cover has only degree-one charts near a point off the divisor.

Source: Stacks Project, Tag 0EYG, first proof paragraph; Tags 02LA, 02VN and 04HN.
(blueprint: lem-sbc-root-split-cover-away-divisor-charts)

Proof: Set A=R[T]/(T^n-g), h=algebraMap R A g and S=A[1/h], with φ the composite
R→A→S. The standard affine basic-open isomorphism identifies Spec S with V=D(h).
Over U=D(g), the monic root polynomial gives a finite free cover of positive rank n.
Its root is invertible, and n*T^(n-1) is invertible, so V→U is finite etale.
Positive finite free rank makes this map surjective. Since g∉y.asIdeal, the point y
belongs to U; choose a point z of Spec S mapping to y. The composite Spec S→U→Spec R
is etale, and φ(g) is a unit by construction. Transport the supplied δ along
Spec S≅V to identify Y×_{Spec R}Spec S with d disjoint copies of Spec S, over Spec S.
Thus no descent of Y and no further local splitting is needed.

Evaluation at φ(g) identifies S[T]/(T-φ(g)) with S as an S-algebra, with inverse
the algebra map. The finite product of these isomorphisms and the fact that Spec
sends finite products to disjoint unions identify the displayed root-product
spectrum with d copies of Spec S. The image of φ(g) remains a unit in the product,
so its basic open is the whole spectrum. Compose with the transported δ. All maps
commute with the structure map to Spec S, proving the projection identity.
If d=0 the product is the zero ring and both sides are empty. Neither regularity
nor a nonzerodivisor assumption is used. This is a root-split specialization of
Stacks 0EYG's off-divisor branch; its given splitting permits the shorter route.
-/
theorem root_split_cover_away_divisor_charts
    (R : CommRingCat.{u}) (g : R) (n : ℕ) (hn : 0 < n ∧ IsUnit (n : R))
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (hj : ∃ j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g),
      j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ) (y : Spec R) (hy : g ∉ y.asIdeal) :
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
      IsUnit (φ g) ∧
        let N := Spec (CommRingCat.of (∀ k : Fin d,
          AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))))
        let q := Spec.map (CommRingCat.ofHom
          (algebraMap S (∀ k : Fin d,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g)))))
        let V : N.Opens := PrimeSpectrum.basicOpen
          (algebraMap S (∀ k : Fin d,
            AdjoinRoot ((Polynomial.X : Polynomial S) ^ (1 : ℕ) - Polynomial.C (φ g))) (φ g))
        ∃ γ : pullback p (Spec.map (CommRingCat.ofHom φ)) ≅ V.toScheme,
          γ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom φ)) := by
  dsimp
  intro δ hδ
  obtain ⟨S, φ, z, e, he, hφ, hz, hunit⟩ :=
    root_split_away_localization_point R g n hn y hy
  obtain ⟨γ, hγ⟩ := root_split_away_transport_chart R g n p d S φ hunit e he δ hδ
  exact ⟨S, φ, z, hφ, hz, hunit, γ, hγ⟩

end AlgebraicGeometry.Scheme
