/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Explicit twist frames on product standard charts

Source: Stacks Project, Constructions, Tags 01MU and 01MV, first proof paragraphs
(blueprint: lem-trf-proj-product-chart-twist-frame).

The degree parts and twists are the existing homogeneous-localization and Proj constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite HomogeneousLocalization

namespace AlgebraicGeometry.Proj

/-- The fraction `a^(2n)/(ab)^n = (a/b)^n` in the ordinary product-chart localization.
Source: Stacks 01MU, first proof paragraph
(blueprint: lem-trf-proj-product-chart-twist-frame). -/
def productChartFrameFraction {A : Type u} [CommRing A] (a b : A) (n : ℕ) :
    Localization.Away (a * b) :=
  Localization.mk (a ^ (2 * n)) ⟨(a * b) ^ n, ⟨n, rfl⟩⟩

/-- The inverse fraction `b^(2n)/(ab)^n = (b/a)^n` in the product-chart localization.
Source: Stacks 01MU, first proof paragraph
(blueprint: lem-trf-proj-product-chart-twist-frame). -/
def productChartInverseFrameFraction {A : Type u} [CommRing A] (a b : A) (n : ℕ) :
    Localization.Away (a * b) :=
  Localization.mk (b ^ (2 * n)) ⟨(a * b) ^ n, ⟨n, rfl⟩⟩

/-- The explicit product-chart frame, its inverse, restriction compatibility and coefficients.
Source: Stacks Project, Constructions, Tags 01MU and 01MV, first proof paragraphs
(blueprint: lem-trf-proj-product-chart-twist-frame).

Proof:
1. Put k = alpha + beta. The inverses of a and b in A_(ab) are b/(ab) and a/(ab).
   Thus e = a^(2n)/(ab)^n and v = b^(2n)/(ab)^n multiply to one. Their numerator
   degrees are nk+nd and nk-nd, respectively, so they belong to the indicated degree parts.
2. Multiplication by e carries degree zero to degree nd, and multiplication by v is its
   inverse. These are linear over the existing homogeneous localization (degree zero).
3. For a standard chart D_+(g) inside D_+(ab), the standard-open-inclusion lemma
   (lem-weil-pbc-proj-standard-open-inclusion) makes ab invertible in A_g. The canonical
   localization map preserves degree and sends e and v to mutually inverse fractions.
   Multiplication by these images gives F; its displayed equations give compatibility
   of E and its inverse with localization. The same argument for two nested subcharts
   gives all standard-open restriction compatibilities.
4. These standard opens form a basis by lem-weil-pbc-proj-standard-open-inclusion.
   Apply lem-weil-pbc-sheaf-morphism-on-basis to the compatible multiplication maps and
   their inverses. They glue to inverse module-sheaf maps: linearity is checked on the
   basis and then by separation. The resulting Phi has the displayed pointwise formula
   on every open of V and sends one to the section s represented by e.
5. The canonical section of f is f/1 (def-weil-pbc-proj-twisting-sheaf). Its coefficient
   is c = v(f/1) = b^(2n)f/(ab)^n = b^n f/a^n, of degree zero. Multiplication by e
   gives f/1. The canonical map awayToSection identifies this degree-zero localization
   with the functions on V; restricting the equality gives the formula on every subopen.
   No cancellation in A or nonvanishing assumption on a or b is used.
-/
theorem productChartTwistFrame
    {A : Type u} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (d n α β : ℕ) (hd : 0 < d) (hn : 0 < n) (hα : α = β + d)
    (a b : A) (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β) :
    IsUnit (algebraMap A (Localization.Away (a * b)) a) ∧
    IsUnit (algebraMap A (Localization.Away (a * b)) b) ∧
    ∃ (e : degreePart 𝒜 (Submonoid.powers (a * b)) ((n * d : ℕ) : ℤ))
      (v : degreePart 𝒜 (Submonoid.powers (a * b)) (-((n * d : ℕ) : ℤ)))
      (E : Away 𝒜 (a * b) ≃ₗ[Away 𝒜 (a * b)]
        degreePart 𝒜 (Submonoid.powers (a * b)) ((n * d : ℕ) : ℤ)),
      (e : Localization.Away (a * b)) = productChartFrameFraction a b n ∧
      (v : Localization.Away (a * b)) = productChartInverseFrameFraction a b n ∧
      (e : Localization.Away (a * b)) * v = 1 ∧
      (∀ r : Away 𝒜 (a * b),
        (E r : Localization.Away (a * b)) = r.val * e) ∧
      (∀ t : degreePart 𝒜 (Submonoid.powers (a * b)) ((n * d : ℕ) : ℤ),
        (E.symm t).val = (t : Localization.Away (a * b)) * v) ∧
      (∀ (g : A) (k : ℕ), 0 < k → g ∈ 𝒜 k →
        basicOpen 𝒜 g ≤ basicOpen 𝒜 (a * b) →
        ∃ (ρ : Localization.Away (a * b) →+* Localization.Away g)
          (ρ₀ : Away 𝒜 (a * b) →+* Away 𝒜 g)
          (F : Away 𝒜 g ≃ₗ[Away 𝒜 g]
            degreePart 𝒜 (Submonoid.powers g) ((n * d : ℕ) : ℤ)),
          ρ.comp (algebraMap A (Localization.Away (a * b))) =
            algebraMap A (Localization.Away g) ∧
          (∀ r : Away 𝒜 (a * b), (ρ₀ r).val = ρ r.val) ∧
          (∀ r : Away 𝒜 g, (F r : Localization.Away g) = r.val * ρ e) ∧
          (∀ t : degreePart 𝒜 (Submonoid.powers g) ((n * d : ℕ) : ℤ),
            (F.symm t).val = (t : Localization.Away g) * ρ v) ∧
          (∀ r : Away 𝒜 (a * b),
            ρ (E r : Localization.Away (a * b)) = (F (ρ₀ r) : Localization.Away g)) ∧
          (∀ (t : degreePart 𝒜 (Submonoid.powers (a * b)) ((n * d : ℕ) : ℤ))
            (t' : degreePart 𝒜 (Submonoid.powers g) ((n * d : ℕ) : ℤ)),
            (t' : Localization.Away g) = ρ t → ρ₀ (E.symm t) = F.symm t')) ∧
      ∃ (s : Γ(twist 𝒜 (0 + ((n * d : ℕ) : ℤ)), basicOpen 𝒜 (a * b)))
        (Φ : (Scheme.Modules.unit (Proj 𝒜)).restrict (basicOpen 𝒜 (a * b)).ι ≅
          (twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).restrict (basicOpen 𝒜 (a * b)).ι),
        (∀ x : basicOpen 𝒜 (a * b),
          (s.val x : Localization.AtPrime x.val.asHomogeneousIdeal.toIdeal) =
            Localization.mk (a ^ (2 * n)) ⟨(a * b) ^ n, pow_mem_primeCompl x n⟩) ∧
        (∀ (Q : (basicOpen 𝒜 (a * b)).toScheme.Opens)
          (r : Γ((Scheme.Modules.unit (Proj 𝒜)).restrict
            (basicOpen 𝒜 (a * b)).ι, Q)),
          ((twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).restrictAppIso
            (basicOpen 𝒜 (a * b)).ι Q).hom (Φ.hom.app Q r) =
          (Scheme.Modules.unitSectionsEquiv ((basicOpen 𝒜 (a * b)).ι ''ᵁ Q)).symm
            (((Scheme.Modules.unit (Proj 𝒜)).restrictAppIso
              (basicOpen 𝒜 (a * b)).ι Q).hom r) •
          (twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).presheaf.map
            (homOfLE ((basicOpen 𝒜 (a * b)).ι_image_le Q)).op s) ∧
        (∀ (f : A) (hf : f ∈ 𝒜 (n * d)),
          ∃ c : Away 𝒜 (a * b),
            c.val = productChartInverseFrameFraction a b n *
              algebraMap A (Localization.Away (a * b)) f ∧
            c.val * (algebraMap A (Localization.Away (a * b)) a) ^ n =
              (algebraMap A (Localization.Away (a * b)) b) ^ n *
                algebraMap A (Localization.Away (a * b)) f ∧
            c.val * e = algebraMap A (Localization.Away (a * b)) f ∧
            ∀ (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 (a * b)),
              (twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).presheaf.map (homOfLE le_top).op
                  ((unitToTwist hf).app ⊤ (Scheme.Modules.unitSectionsEquiv ⊤ 1)) =
                (Proj 𝒜).presheaf.map (homOfLE hU).op (awayToSection 𝒜 (a * b) c) •
                  (twist 𝒜 (0 + ((n * d : ℕ) : ℤ))).presheaf.map
                    (homOfLE hU).op s) := by
  sorry

end AlgebraicGeometry.Proj
