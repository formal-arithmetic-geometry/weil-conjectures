/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import Sheaf.AlgebraicGeometry.SerreSectionModuleFractionLift
import Sheaf.AlgebraicGeometry.SerreSectionModuleFractionEquality
import Sheaf.AlgebraicGeometry.SerreSectionModuleFractionAdd
import Sheaf.AlgebraicGeometry.SerreSectionModuleComparison

/-!
# Canonical additive chart for a graded section module

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On one positive-degree standard open the additive comparison map has exactly the
homogeneous fractions as its range, and is characterized by clearing its denominator.
Source: Stacks Project, Proposition 0BXD, final paragraph; the fraction construction in
step 1 of lem-sc-p1-serre-section-module-charts.
(blueprint: lem-sc-p1-serre-section-module-chart-additive)

Proof: use serreSectionModuleComparison for existence and annihilation. Multiplication
by f^m on G over D+(f) is invertible: restrict unitToTwist, tensor with G, and compose
with the inverse right unitor. Send a homogeneous fraction y/f^m to the inverse image
of the restriction of phi(y). If f is zero, D+(f) is empty and M_f is zero, so use the
unique map. Otherwise f^m is nonzero and its homogeneous degree is m*d; uniqueness
of homogeneous degree puts every equal-degree fraction in this form. Clear the two
denominators in an equality LocalizedModule.mk_eq; compatibility hphi shows that the
inverse images agree. This defines an additive map out of the degree-zero fractions.
For addition take a common denominator and use additivity of phi in that degree.
If its image is zero, the annihilation clause of the comparison kills the numerator
by a power of f; compatibility hphi and injectivity of phi translate this into zero
in M_f. The existence clause makes the map surjective. Invert this additive bijection
and include it into M_f to obtain alpha. The definition and invertibility of
multiplication give the stated equivalence for every homogeneous y and every s. -/
theorem serreSectionModuleChartAdditive
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (hneg : ∀ z : ℤ, z < 0 → 𝓜 z = ⊥)
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) :
    ∃ (alpha : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M),
      Function.Injective alpha ∧
      Set.range alpha = degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f) ∧
      (∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
      alpha s = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ↔
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s) := by
  classical
  let Rel := fun (x : LocalizedModule.Away f M)
      (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))) ↦
      ∃ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ))),
        x = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ∧
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s
  have heq := serreSectionModuleFractionEquality
    k G hG M 𝓜 h𝓜 hsmul hneg φ hφ f d hd hf
  have hadd := serreSectionModuleFractionAdd
    k G M 𝓜 hsmul φ hφ f d hf
  have hlift := serreSectionModuleFractionLift
    k G hG M 𝓜 h𝓜 hsmul hneg φ hφ f d hd hf
  have htotal : ∀ s, ∃ x, Rel x s := by
    intro s
    obtain ⟨m, t, ht⟩ := (serreSectionModuleComparison G hG hd hf).1 s
    let y := (φ _ (by positivity)).symm t
    refine ⟨mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f), m, y, rfl, ?_⟩
    simpa only [y, AddEquiv.apply_symm_apply] using ht
  choose a ha using htotal
  have a_add : ∀ s t, a (s + t) = a s + a t := by
    intro s t
    exact (heq _ _ _ _ (ha (s + t)) (hadd _ _ _ _ (ha s) (ha t))).2 rfl
  have a_zero : a 0 = 0 := by
    have h := a_add 0 0
    have h' : a 0 + a 0 = a 0 + 0 := by simpa using h.symm
    exact add_left_cancel h'
  let alpha : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
      LocalizedModule.Away f M := { toFun := a, map_zero' := a_zero, map_add' := a_add }
  refine ⟨alpha, ?_, ?_, ?_⟩
  · intro s t h
    exact (heq _ _ _ _ (ha s) (ha t)).1 h
  · apply Set.Subset.antisymm
    · rintro x ⟨s, rfl⟩
      obtain ⟨m, y, hy, _⟩ := ha s
      refine ⟨m • d, y, ⟨f ^ m, ⟨m, rfl⟩⟩, ?_,
        SetLike.pow_mem_graded m hf, hy.symm⟩
      simpa using y.property
    · intro x hx
      obtain ⟨s, hs, _⟩ := hlift x hx
      exact ⟨s, (heq _ _ _ _ (ha s) hs).2 rfl⟩
  · intro m y s
    constructor
    · intro h
      obtain ⟨t, ht, hformula⟩ := hlift _
        ⟨m • d, y, ⟨f ^ m, ⟨m, rfl⟩⟩, by simpa using y.property,
          SetLike.pow_mem_graded m hf, rfl⟩
      have hst := (heq _ _ _ _ (ha s) ht).1 h
      have hfml := hformula m y rfl
      simpa only [← hst] using hfml
    · intro h
      exact (heq _ _ _ _ (ha s) ⟨m, y, rfl, h⟩).2 rfl

end AlgebraicGeometry.Proj
