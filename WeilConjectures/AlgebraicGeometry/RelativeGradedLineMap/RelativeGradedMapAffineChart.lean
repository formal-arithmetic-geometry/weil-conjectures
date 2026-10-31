/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedLineMap
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample

/-! # Affine restriction of a relative graded canonical map

Source: Stacks Project, Constructions, Tag 01O9, part (3).
(blueprint: lem-trf-relative-graded-map-affine-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine base chart, a normalized graded section map whose positive-degree
images generate has the basic-open and fraction formulas of its canonical relative map.
No immersion or quasi-compactness assumption is required.

Source: Stacks Project, Constructions, Tag 01O9, characterization (3), and Tag 01NK
(blueprint: lem-trf-relative-graded-map-affine-chart).

Proof: trivialize the pulled-back line on an open cover. In each frame, the homogeneous
sections defining phi give their coefficient ring map alpha to regular functions.
Multiplication of tensor powers and the degree-zero unit show that alpha preserves
products and one. At every point some positive-degree coefficient is a unit, since
the corresponding section has nonzero residue. Thus the image of the irrelevant
ideal is the unit ideal on each trivializing open. The supplied IsCanonicalMap
condition identifies the restriction of r with Proj.fromOfGlobalSections(alpha).
The supplied lift rho is unique since the relative-Proj chart is an open immersion.
Cancel that chart and transport the identity grading isomorphism. The usual inverse
image formula for fromOfGlobalSections gives rho inverse-image D_+(a) as the basic
open of alpha(a), which in a frame is exactly the nonvanishing locus of phi(a).
On that open the degree-zero fraction b/a^n maps to alpha(b)/alpha(a)^n. Multiply
by the frame expression for phi(a)^n to obtain the displayed section equation.
Tensor-power coherence and the normalization identify these frame expressions with
the given sections, including n=0. Sheaf separatedness glues the equations over
the preimage of D_+(a). Empty charts have the unique equations. Arbitrary degree-zero
algebras and arbitrary positive degrees are allowed throughout.
-/
theorem RelativeGradedLineMap.affine_chart_formulas
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules} [L.IsInvertible]
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    (r : Z ⟶ A.relProj) (hr : ψ.IsCanonicalMap r)
    (V : S.affineOpens)
    (hM : ((tensorPullback (h ⁻¹ᵁ V.1).ι).obj L).IsInvertible) :
    let T := (h ⁻¹ᵁ V.1).toScheme
    let M := (tensorPullback (h ⁻¹ᵁ V.1).ι).obj L
    let 𝒜 : ℕ → AddSubgroup (A.obj V) := fun n ↦ (A.grading V n).toAddSubgroup
    letI : GradedRing 𝒜 := { (inferInstance : GradedRing (A.grading V)) with }
    let γ : A.grading V →+*ᵍ 𝒜 :=
      { toRingHom := RingHom.id _
        map_mem := fun ha ↦ ha }
    ∀ (ρ : T ⟶ Proj 𝒜),
      ρ ≫ Proj.map γ (by
        intro a ha
        exact Ideal.mem_map_of_mem γ.toRingHom ha) ≫ A.relProjι V = (h ⁻¹ᵁ V.1).ι ≫ r →
      ∀ (φ : 𝒜 →+*ᵍ sectionRingGrade M),
        (∀ (n : ℕ) (a : A.grading V n),
          φ.toRingHom a = (DirectSum.of (SectionRingComponent M) n)
            (ψ.evaluate (h ⁻¹ᵁ V.1).ι V (by simp) n a)) →
        (∀ z : T, ∃ (n : ℕ) (a : A.obj V) (ha : a ∈ 𝒜 n),
          0 < n ∧ z ∈ nonvanishingLocus (M.tensorPow n) ((φ.toRingHom a) n)) →
        (∀ (d : ℕ) (_hd : 0 < d) (a : A.obj V) (_ha : a ∈ 𝒜 d),
          (ρ ⁻¹ᵁ Proj.basicOpen 𝒜 a : Set T) =
            nonvanishingLocus (M.tensorPow d) ((φ.toRingHom a) d)) ∧
        (∀ (d : ℕ) (_hd : 0 < d) (a : A.obj V) (ha : a ∈ 𝒜 d),
          ∀ (n : ℕ) (b : A.obj V) (_hb : b ∈ 𝒜 (n • d)),
            (ρ.app (Proj.basicOpen 𝒜 a)
              (Proj.awayToSection 𝒜 a (HomogeneousLocalization.Away.mk 𝒜 ha n b _hb))) •
              (M.tensorPow (n • d)).presheaf.map
                (homOfLE (le_top : ρ ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
                (((φ.toRingHom a) ^ n) (n • d)) =
              (M.tensorPow (n • d)).presheaf.map
                (homOfLE (le_top : ρ ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
                ((φ.toRingHom b) (n • d))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
