/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF Q08
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Sheaf.AlgebraicGeometry.ProjInvertibleMapTwistIso
import Sheaf.TraceFormula.SpaceLineModuleProjMap

/-!
# Sufficiently divisible twists pull back to powers of the line module

Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme.Modules

/-- The homogeneous section of the invertible section ring determined by a graded map.
Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison). -/
noncomputable def gradedSectionElement {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    {Z : Scheme.{u}} (M : Z.Modules) [M.IsInvertible]
    (ψ : 𝒜 →+*ᵍ sectionRingGrade M) {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) :
    sectionRingGrade M n :=
  ⟨ψ.toRingHom a, ψ.map_mem ha⟩

/-- The graded section-ring element has the prescribed homogeneous degree.
Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison). -/
@[simp] theorem gradedSectionElement_val {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    {Z : Scheme.{u}} (M : Z.Modules) [M.IsInvertible]
    (ψ : 𝒜 →+*ᵍ sectionRingGrade M) {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) :
    (gradedSectionElement 𝒜 M ψ a ha).val = ψ.toRingHom a :=
  by sorry

/-- For a graded section-ring map whose positive-degree nonvanishing opens cover a
quasi-compact scheme, the canonical Proj morphism pulls back a sufficiently divisible
twist to the corresponding tensor power of the invertible module. Each isomorphism
is normalized by sending the actual tensor pullback of every homogeneous degree-`d * k`
section to its image under `ψ`, as in the commutative diagram of Tag 01NK.

Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison).

Proof: Apply the canonical generation-locus construction to the graded map and identify its
positive-degree locus with all of `Z`.  Quasi-compactness gives finitely many positive-degree
homogeneous sections; taking a common positive multiple `d` makes the degree-`d` sections
and all their positive multiples generate the corresponding tensor powers.  The generated-chart
comparison gives the canonical isomorphism on each degree `d * k`; the uniqueness clause makes
these comparisons independent of the finite subcover and common multiple. The normalization
is the equality on homogeneous sections in property (2) of Tag 01NK: `unitToTwist` is the
section `a/1`, `tensorPullbackSection` is its actual pullback `1 ⊗ a`, and the comparison
sends this to `ψ(a)`. For an empty scheme,
`d = 1` is allowed and all comparison assertions are vacuous. -/
theorem exists_proj_canonical_map_twist_comparison
    {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (Z : Scheme.{u}) [CompactSpace Z] (M : Z.Modules) [M.IsInvertible]
    (ψ : 𝒜 →+*ᵍ sectionRingGrade M)
    (hcover : ∀ z : Z, ∃ (n : ℕ) (a : A) (ha : a ∈ 𝒜 n),
      0 < n ∧ z ∈ nonvanishingLocus (M.tensorPow n)
        ((gradedSectionElement 𝒜 M ψ a ha).val n))
    (r : Z ⟶ Proj 𝒜)
    (hr_preimage : ∀ (d : ℕ) (_hd : 0 < d) (a : A) (ha : a ∈ 𝒜 d),
      (r ⁻¹ᵁ Proj.basicOpen 𝒜 a : Set Z) =
        nonvanishingLocus (M.tensorPow d)
          ((gradedSectionElement 𝒜 M ψ a ha).val d))
    (hr_formula : ∀ (d : ℕ) (_hd : 0 < d) (a : A) (ha : a ∈ 𝒜 d),
      ∀ (n : ℕ) (b : A) (hb : b ∈ 𝒜 (n • d)),
        (r.app (Proj.basicOpen 𝒜 a)
          (Proj.awayToSection 𝒜 a
            (HomogeneousLocalization.Away.mk 𝒜 ha n b hb))) •
            (M.tensorPow (n • d)).presheaf.map
              (homOfLE (le_top : r ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
              (((gradedSectionElement 𝒜 M ψ a ha).val ^ n) (n • d)) =
          (M.tensorPow (n • d)).presheaf.map
            (homOfLE (le_top : r ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
            ((gradedSectionElement 𝒜 M ψ b hb).val (n • d))) :
    ∃ d : ℕ, 0 < d ∧
      ∀ k : ℕ, 0 < k →
        ∃ θ : ((tensorPullback r).obj (Proj.twist 𝒜 (0 + ((d * k : ℕ) : ℤ))) ≅
          M.tensorPow (d * k)),
          ∀ (a : A) (ha : a ∈ 𝒜 (d * k)),
            θ.hom.app (r ⁻¹ᵁ ⊤)
                (tensorPullbackSection r (Proj.twist 𝒜 (0 + ((d * k : ℕ) : ℤ))) ⊤
                  ((Proj.unitToTwist (𝒜 := 𝒜) ha).app ⊤ (1 : Γ(Proj 𝒜, ⊤)))) =
              (M.tensorPow (d * k)).presheaf.map
                (homOfLE (le_top : r ⁻¹ᵁ ⊤ ≤ ⊤)).op
                ((gradedSectionElement 𝒜 M ψ a ha).val (d * k)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
