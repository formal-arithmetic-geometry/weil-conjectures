/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.AlgebraicGeometry.SerreSectionModuleFractionEquality
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection


/-!
# Section represented by a homogeneous fraction

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra


private lemma fraction_power_rep
    {k : Type u} [Field k] (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) {f : MvPolynomial (Fin 2) k} {d : ℕ}
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (x : LocalizedModule.Away f M)
    (hx : x ∈ degreeZeroFractions
      (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
      (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f)) :
    ∃ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ))),
      x = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
  by_cases hf0 : f = 0
  · have : Subsingleton (LocalizedModule.Away f M) :=
      LocalizedModule.subsingleton (by exact ⟨1, by simp [hf0]⟩)
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  · obtain ⟨n, y, h, hy, hh, hxy⟩ := hx
    obtain ⟨m, hm⟩ := h.property
    have hh' : f ^ m ∈ homogeneousSubmodule (Fin 2) k n := by simpa [hm] using hh
    have hdeg : n = m • d :=
      MvPolynomial.IsHomogeneous.inj_right hh' (SetLike.pow_mem_graded m hf)
        (pow_ne_zero _ hf0)
    have hy' : y ∈ 𝓜 (0 + ((m • d : ℕ) : ℤ)) := by simpa [hdeg] using hy
    refine ⟨m, ⟨y, hy'⟩, ?_⟩
    rw [← hxy]
    congr 1
    exact Subtype.ext hm.symm

private lemma fraction_twist_bijective
    {k : Type u} [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    {f : MvPolynomial (Fin 2) k} {d : ℕ}
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) :
    Function.Bijective (Scheme.Modules.Hom.app
      ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
      (basicOpen (homogeneousSubmodule (Fin 2) k) f)) := by
  have hU : basicOpen (homogeneousSubmodule (Fin 2) k) f ≤
      basicOpen (homogeneousSubmodule (Fin 2) k) (f ^ m) := by
    cases m with
    | zero => simp
    | succ m =>
      simp [Proj.basicOpen_pow (homogeneousSubmodule (Fin 2) k) f (m + 1) (Nat.succ_pos m)]
  have he := (Proj.isFreeGenerator_unitToTwist (SetLike.pow_mem_graded m hf)).map hU
  have hb := he.bijective_tmulSection_right (M := G) le_rfl
  convert hb using 1
  ext s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.rightUnitor_inv_app, Scheme.Modules.whiskerLeft_app_tmulSection]
  congr 1

/-- Every degree-zero fraction comes from a section on the standard open.
Source: Stacks Project, Proposition 0BXD, final paragraph.
(blueprint: lem-sc-p1-serre-section-module-fraction-lift)

Proof: If f=0, localization is zero and the standard open is empty; the zero section
works. Otherwise write the denominator as f^m. Its homogeneous degree is m*d,
by uniqueness of degree for nonzero homogeneous polynomials. The numerator
therefore lies in M_(m*d). Multiplication by f^m identifies G on D+(f) with
G tensor O(m*d): restrict unitToTwist, tensor with G and use the right unitor.
Apply its inverse to the restricted phi of the numerator. This yields the
required section and the displayed relation. For another representative,
LocalizedModule.mk_eq provides a power killing the cross multiplied
numerator difference. Apply phi and restrict; multiplication by the extra
power and by the first denominator is invertible on D+(f), giving the
formula for the other representative as well. -/
theorem serreSectionModuleFractionLift
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
    ∀ x, x ∈ degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f) → ∃ s, Rel x s ∧
      (∀ (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ))),
        x = mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
        (G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
          (0 + ((m • d : ℕ) : ℤ))).presheaf.map
            (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
            (φ _ (by positivity) y) =
          Scheme.Modules.Hom.app
            ((ρ_ G).inv ≫ G ◁ Proj.unitToTwist (SetLike.pow_mem_graded m hf))
            (basicOpen (homogeneousSubmodule (Fin 2) k) f) s) := by
  dsimp only
  intro x hx
  obtain ⟨m, y, hxy⟩ := fraction_power_rep M 𝓜 hf x hx
  obtain ⟨s, hs⟩ := (fraction_twist_bijective G hf m).2
    ((G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
      (0 + ((m • d : ℕ) : ℤ))).presheaf.map
        (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
        (φ _ (by positivity) y))
  refine ⟨s, ⟨m, y, hxy, hs.symm⟩, ?_⟩
  intro n z hxz
  obtain ⟨t, ht⟩ := (fraction_twist_bijective G hf n).2
    ((G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k)
      (0 + ((n • d : ℕ) : ℤ))).presheaf.map
        (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
        (φ _ (by positivity) z))
  have hst := (serreSectionModuleFractionEquality
    k G hG M 𝓜 h𝓜 hsmul hneg φ hφ f d hd hf x x s t
    ⟨m, y, hxy, hs.symm⟩ ⟨n, z, hxz, ht.symm⟩).1 rfl
  simpa only [← hst] using ht.symm


end AlgebraicGeometry.Proj
