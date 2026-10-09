/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# Local structure of the deformation to the normal cone of a section

The clauses of `sk-lem-geometry` that the proof of `sk-thm-dnc` uses to compute the family
object `ℱ = Ls̃^* ω_{g̃}` étale-locally, for `g : V ⟶ B` smooth of pure relative dimension `d`
with a closed section `s`:

* the *normal form* (clause (2)): étale-locally on `B`, and on an étale neighbourhood of the
  section, there are relative coordinates `x₁, …, x_d` in which `s` is `x = 0`, that is an
  étale map to `𝔸^d` carrying `s` to the zero section;
* *étale localization* (clause (5)): the deformation space only depends on an étale
  neighbourhood of the section;
* *base change* (clause (5)): the deformation space commutes with base change in `B`;
* the *punctured trivialization* (clause (3)): over `𝔾_{m,B}` the deformation space is
  `V ×_B 𝔾_{m,B}`;
* the *standard pair* (clause (4)): for `(𝔸^d_B ⟶ B, 0)` the deformation space is
  `𝔸^d_{𝔸¹_B}` over `𝔸¹_B`, with `s̃` its zero section.

Together they reduce the computation of `ℱ` to the standard pair, where it is constant along
`𝔸¹_B`; the cohomological half of clause (4) is
`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_deformation_affineSpace`.

## Implementation notes

The étale neighbourhood of the section in the normal form and in étale localization is an
étale `e : V' ⟶ V` with a section `s'` over `s` such that the square `s' ≫ e = 𝟙 ≫ s` is
cartesian, i.e. `e⁻¹(s(B)) = s'(B)`. This makes the centre of the blow-up pull back to the
centre, so that the deformation spaces are compared by flat base change of blow-ups.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_etale_coordinates_of_section`
- `AlgebraicGeometry.Scheme.Hom.exists_etale_deformationSpace_map`
- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`
- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_multiplicativeGroup`
- `AlgebraicGeometry.Scheme.Hom.exists_iso_deformationSpace_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {V B : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B)

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*Normal form of a section of a smooth morphism* (clause (2), the relative local linearization).
If `g` is smooth of pure relative dimension `d` with a closed section `s`, there are a jointly
surjective family of étale maps `b i : B' i ⟶ B` and, for each `i`, an étale neighbourhood
`w i : W i ⟶ V` of the section over `b i`, with section `σ i` and `w i⁻¹(s(B)) = σ i(B' i)`,
together with an étale map `x i : W i ⟶ 𝔸^d_{B' i}` over `B' i` carrying `σ i` to the zero
section: the coordinates `x₁, …, x_d` in which `s` is `x = 0`. -/
theorem exists_etale_coordinates_of_section (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] :
    ∃ (ι : Type u) (B' : ι → Scheme.{u}) (b : ∀ i, B' i ⟶ B) (W : ι → Scheme.{u})
      (w : ∀ i, W i ⟶ V) (σ : ∀ i, B' i ⟶ W i) (x : ∀ i, W i ⟶ 𝔸(ULift.{u} (Fin d); B' i)),
      (∀ i, AlgebraicGeometry.Etale (b i)) ∧ ⋃ i, Set.range (b i).base = Set.univ ∧
      (∀ i, AlgebraicGeometry.Etale (w i)) ∧ (∀ i, AlgebraicGeometry.Etale (x i)) ∧
      (∀ i, x i ≫ (𝔸(ULift.{u} (Fin d); B' i) ↘ B' i) ≫ b i = w i ≫ g) ∧
      (∀ i, IsPullback (σ i) (b i) (w i) s) ∧
      (∀ i, σ i ≫ x i = AffineSpace.zeroSection (ULift.{u} (Fin d)) (B' i)) :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*Étale localization* (clause (5)). Let `e : V' ⟶ V` be étale over `B`, with a section `s'` of
`g' = e ≫ g` such that `e⁻¹(s(B)) = s'(B)`. Then there is an étale morphism
`𝒟_{s'} V' ⟶ 𝒟_s V` over `𝔸¹_B` carrying `s̃'` to `s̃`: the deformation to the normal cone
only depends on an étale neighbourhood of the section. -/
theorem exists_etale_deformationSpace_map [IsClosedImmersion s] {V' : Scheme.{u}}
    (e : V' ⟶ V) [AlgebraicGeometry.Etale e] (s' : B ⟶ V') [IsClosedImmersion s']
    (hs' : s' ≫ e ≫ g = 𝟙 B)
    (he : IsPullback s' (𝟙 B) e s) :
    ∃ φ : deformationSpace (e ≫ g) s' hs' ⟶ deformationSpace g s hs,
      AlgebraicGeometry.Etale φ ∧ φ ≫ deformationProj g s hs = deformationProj (e ≫ g) s' hs' ∧
        deformationSection (e ≫ g) s' hs' ≫ φ = deformationSection g s hs :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*Base change* (clause (5)). For `g` smooth and a cartesian square `bV ≫ g = g' ≫ b` with a
section `s'` of `g'` lying over `s`, the deformation space of `(g', s')` is the base change of
that of `(g, s)` along `𝔸¹_b : 𝔸¹_{B'} ⟶ 𝔸¹_B`, compatibly with the sections `s̃`. Smoothness of
`g` makes `s` a regular immersion whose extended Rees algebra commutes with arbitrary base
change. -/
theorem exists_isPullback_deformationSpace_baseChange (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] {V' B' : Scheme.{u}} (g' : V' ⟶ B') (s' : B' ⟶ V')
    [IsClosedImmersion s'] (hs' : s' ≫ g' = 𝟙 B') (b : B' ⟶ B) (bV : V' ⟶ V)
    (h : IsPullback bV g' g b) (hsb : s' ≫ bV = b ≫ s) :
    ∃ φ : deformationSpace g' s' hs' ⟶ deformationSpace g s hs,
      IsPullback φ (deformationProj g' s' hs') (deformationProj g s hs)
          (AffineSpace.map (ULift.{u} (Fin 1)) b) ∧
        deformationSection g' s' hs' ≫ φ =
          AffineSpace.map (ULift.{u} (Fin 1)) b ≫ deformationSection g s hs :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*The punctured trivialization* (clause (3), geometric half). Over `𝔾_{m,B} ⊆ 𝔸¹_B` the
deformation space is `V ×_B 𝔾_{m,B}`, with `s̃` restricting to `s × 𝟙`: away from `t = 0` the
blow-up is an isomorphism and the removed strict transform lies over `t = 0`. With base change
for `ω` this gives the trivialization `κ° : j^* ℱ ≅ j^* a^* 𝒞(g, s)` of the family object. -/
theorem exists_isPullback_deformationSpace_multiplicativeGroup [IsClosedImmersion s] :
    ∃ φ : pullback g (AffineSpace.multiplicativeGroupProj B) ⟶ deformationSpace g s hs,
      IsPullback φ (pullback.snd _ _) (deformationProj g s hs)
          (AffineSpace.multiplicativeGroupOpen B).ι ∧
        pullback.lift (AffineSpace.multiplicativeGroupProj B ≫ s) (𝟙 _)
            (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp]) ≫ φ =
          (AffineSpace.multiplicativeGroupOpen B).ι ≫ deformationSection g s hs :=
  sorry

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

*The standard pair* (clause (4), geometric half). For the zero section of `𝔸^d_S ⟶ S`, the
deformation space is `𝔸^d_{𝔸¹_S}` over `𝔸¹_S`, with `s̃` its zero section: on the chart
`u_k = x_k / t` the extended Rees algebra is `𝒪_S[t][u₁, …, u_d]`, with `x_k = t u_k`. -/
theorem exists_iso_deformationSpace_affineSpace (d : ℕ) (S : Scheme.{u}) :
    ∃ Φ : deformationSpace (𝔸(ULift.{u} (Fin d); S) ↘ S)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
        (AffineSpace.zeroSection_over (ULift.{u} (Fin d)) S) ≅
        𝔸(ULift.{u} (Fin d); 𝔸(ULift.{u} (Fin 1); S)),
      Φ.hom ≫ (𝔸(ULift.{u} (Fin d); 𝔸(ULift.{u} (Fin 1); S)) ↘ 𝔸(ULift.{u} (Fin 1); S)) =
          deformationProj _ _ (AffineSpace.zeroSection_over (ULift.{u} (Fin d)) S) ∧
        deformationSection _ _ (AffineSpace.zeroSection_over (ULift.{u} (Fin d)) S) ≫ Φ.hom =
          AffineSpace.zeroSection (ULift.{u} (Fin d)) 𝔸(ULift.{u} (Fin 1); S) :=
  sorry

end Scheme.Hom

end AlgebraicGeometry
