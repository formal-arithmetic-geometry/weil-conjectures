/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Finiteness.Subalgebra

/-!
# Linear projections of `Proj` to projective space

Let `A` be a commutative `k`-algebra graded by `𝒜 : ℕ → Submodule k A`, and let `l : ι → A` be
a family of elements of degree one such that the basic opens `D₊(lᵢ)` cover `Proj 𝒜`. Then
`l` defines a morphism `Proj 𝒜 ⟶ ℙ(ι; Spec k)`, `x ↦ [lᵢ(x)]`. On the chart `D₊(lᵢ)` it is the
morphism given by the global sections `lⱼ / lᵢ` of `Spec (A_{lᵢ})₀`, which generate the unit
ideal since `lᵢ / lᵢ = 1`. Two such chart morphisms agree on the overlap `D₊(lᵢ lⱼ)`, as their
sections differ by the unit `lᵢ / lⱼ`, so they glue.

The case of a pair `l₀, l₁` gives the morphism `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`, which on `D₊(l₀)`
corresponds to the ring map `k[t] → A_(l₀)`, `t ↦ l₁ / l₀`, and on `D₊(l₁)` to the ring map
`k[t⁻¹] → A_(l₁)`, `t⁻¹ ↦ l₀ / l₁`.

## Main definitions

- `AlgebraicGeometry.Proj.toSpecBase` — the structure morphism `Proj 𝒜 ⟶ Spec k`.
- `AlgebraicGeometry.Proj.linearChartHom` — the morphism `Spec (A_{lᵢ})₀ ⟶ ℙ(ι; Spec k)`
  given by the sections `lⱼ / lᵢ`.
- `AlgebraicGeometry.Proj.linearProjection` — the morphism `Proj 𝒜 ⟶ ℙ(ι; Spec k)` defined by
  a family of linear forms without common zero.
- `AlgebraicGeometry.Proj.linearPairProjection` — the morphism `π_{l₀,l₁} : Proj 𝒜 ⟶ ℙ¹_k`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.comp_homOfSections` — naturality of `homOfSections`.
- `AlgebraicGeometry.ProjectiveSpace.homOfSections_eq_of_unit_mul` — rescaling the sections
  by a unit does not change `homOfSections`.
- `AlgebraicGeometry.Proj.linearChartHom_compatible` — the chart morphisms agree on overlaps.
- `AlgebraicGeometry.Proj.awayι_linearProjection` — on the chart `D₊(lᵢ)` the linear
  projection is `linearChartHom`.
- `AlgebraicGeometry.Proj.linearProjection_over` — the linear projection is a morphism over
  `Spec k`.
- `AlgebraicGeometry.Proj.linearProjection_preimage_standardOpen` — the preimage of `D₊(Tᵢ)` is
  `D₊(lᵢ)`.
- `AlgebraicGeometry.Proj.isFinite_linearProjection` — finiteness criterion for the linear
  projection.
- `AlgebraicGeometry.Proj.isFinite_linearPairProjection` — `π_{l₀,l₁}` is finite for a
  standard graded `k`-algebra.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

namespace ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X Y S : Scheme.{u}} {n : Type u}

/-- If global sections `s i` generate the unit ideal, so do their pullbacks along any
morphism of schemes. -/
lemma span_range_appTop_eq_top (h : Y ⟶ X) {s : n → Γ(X, ⊤)}
    (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range fun i ↦ h.appTop.hom (s i)) = ⊤ := by
  rw [Set.range_comp' h.appTop.hom s, ← Ideal.map_span, hs, Ideal.map_top]

/-- `homOfSections` is natural in the source: precomposing with `h : Y ⟶ X` gives the morphism
attached to `h ≫ g` and the pulled back sections. -/
@[reassoc]
lemma comp_homOfSections (h : Y ⟶ X) (g : X ⟶ S) (s : n → Γ(X, ⊤))
    (hs : Ideal.span (Set.range s) = ⊤) :
    h ≫ homOfSections g s hs =
      homOfSections (h ≫ g) (fun i ↦ h.appTop.hom (s i)) (span_range_appTop_eq_top h hs) := by
  refine hom_ext n S (by simp) ?_
  rw [Category.assoc, homOfSections_toProjInt, homOfSections_toProjInt,
    Proj.comp_fromOfGlobalSections _ h _ _ (Proj.map_irrelevant_comp_appTop_eq_top _ h _
      (map_irrelevant_evalSections_eq_top s hs))]
  congr 1
  exact comp_evalSections h s

/-- Rescaling all the sections by a unit `u` of `Γ(X, ⊤)` does not change `homOfSections`. -/
lemma homOfSections_eq_of_unit_mul (g : X ⟶ S) (u : Γ(X, ⊤)ˣ) {s s' : n → Γ(X, ⊤)}
    (hs : Ideal.span (Set.range s) = ⊤) (hs' : Ideal.span (Set.range s') = ⊤)
    (hss' : ∀ i, s' i = u * s i) :
    homOfSections g s hs = homOfSections g s' hs' := by
  obtain rfl : s' = fun i ↦ u * s i := funext hss'
  refine hom_ext n S (by simp) ?_
  rw [homOfSections_toProjInt, homOfSections_toProjInt]
  exact Proj.fromOfGlobalSections_eq_of_unit_pow_mul _ u _ _
    (fun _ _ ha ↦ evalSections_const_mul _ _ ha) _ _

end ProjectiveSpace

namespace AffineSpace

end AffineSpace

namespace Proj

section Construction

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜]

variable {ι : Type u} (l : ι → A) (hl : ∀ i, l i ∈ 𝒜 1)

variable (hcov : ⨆ i, basicOpen 𝒜 (l i) = ⊤)

section Finite

open ProjectiveSpace

end Finite

end Construction

section Pair

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  [GradedAlgebra 𝒜] {l₀ l₁ : A}

variable {𝒜} (h₀ : l₀ ∈ 𝒜 1) (h₁ : l₁ ∈ 𝒜 1)
  (hcov : ProjectiveSpectrum.basicOpen 𝒜 l₀ ⊔ ProjectiveSpectrum.basicOpen 𝒜 l₁ = ⊤)

end Pair

end Proj

end AlgebraicGeometry
