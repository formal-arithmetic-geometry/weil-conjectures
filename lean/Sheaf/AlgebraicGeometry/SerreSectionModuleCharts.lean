/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups H1 and P3
-/
module

public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.AlgebraicGeometry.SerreSectionModuleComparison
import Sheaf.AlgebraicGeometry.SerreSectionModuleChartAdditive
import Sheaf.AlgebraicGeometry.SerreSectionModuleChartScalar
import Sheaf.AlgebraicGeometry.SerreSectionModuleChartRestriction

/-!
# Localization charts for the truncated graded section module

Source: Stacks Project, Proposition 0BXD, final paragraph of the proof.
(blueprint: lem-sc-p1-serre-section-module-charts)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Changing denominators preserves equality, including for nonhomogeneous numerators. -/
private theorem fractionChange_eq {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (f g a : R) (e m n : ℕ) (hrel : g ^ e = a * f) (y z : M)
    (h : mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) =
      mk z (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)) :
    mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g) =
      mk (a ^ n • z) (⟨g ^ (e * n), ⟨e * n, rfl⟩⟩ : Submonoid.powers g) := by
  obtain ⟨t, ht⟩ := mk_eq.mp h
  obtain ⟨q, hq⟩ := t.property
  have hclear : f ^ q • (f ^ n • y) = f ^ q • (f ^ m • z) := by
    simpa only [Submonoid.smul_def, ← hq] using ht
  apply mk_eq.mpr
  refine ⟨⟨g ^ (e * q), ⟨e * q, rfl⟩⟩, ?_⟩
  simp only [Submonoid.smul_def, pow_mul, hrel, mul_pow, mul_smul]
  calc
    a ^ q • f ^ q • (a ^ n • f ^ n • (a ^ m • y)) =
        (a ^ q * a ^ n * a ^ m) • (f ^ q • (f ^ n • y)) := by
      simp only [← mul_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = (a ^ q * a ^ n * a ^ m) • (f ^ q • (f ^ m • z)) := by rw [hclear]
    _ = a ^ q • f ^ q • (a ^ m • f ^ m • (a ^ n • z)) := by
      simp only [← mul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- The truncated section module has canonical localization charts on the original sheaf.
Source: Stacks Project, Proposition 0BXD, final paragraph of the proof.
(blueprint: lem-sc-p1-serre-section-module-charts)

Proof:
1. Use serreSectionModuleChartAdditive on each homogeneous positive-degree f and
   choose its additive injection, range identity, and denominator characterization.
2. Represent an arbitrary scalar by a/f^l using Away.mk_surjective. The existence
   clause of serreSectionModuleComparison and the denominator characterization
   represent the section by y/f^m with homogeneous y. Apply the homogeneous scalar
   calculation serreSectionModuleChartScalar, then mk_smul_mk and pow_add.
3. For restriction, the same comparison gives a homogeneous representative z/f^n.
   Apply serreSectionModuleChartRestriction to it. For the arbitrary representative
   y/f^m in the statement, mk_eq clears denominators. The proved fractionChange_eq
   multiplies this equality by powers of a and uses g^e=a*f to give equality of the
   transformed fractions in M_g. Thus the homogeneous restriction formula implies
   the formula for every representative, including nonhomogeneous numerators.
The statement assumes a graded section module but asserts no finite generation;
that independent part is supplied by serreSectionModuleFinite.
-/
theorem serreSectionModuleCharts
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
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y)) :
    ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M),
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f)) ∧
      (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s) ∧
      (∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (G.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)) := by
  classical
  have hcharts := fun f d hd hf ↦
    serreSectionModuleChartAdditive k G hG M 𝓜 h𝓜 hsmul hneg φ hφ f d hd hf
  choose alpha hinj hrange hnorm using hcharts
  refine ⟨alpha, ?_, ?_, ?_⟩
  · intro f d hd hf
    exact ⟨hinj f d hd hf, hrange f d hd hf⟩
  · intro f d hd hf r s
    obtain ⟨l, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (homogeneousSubmodule (Fin 2) k) hf r
    obtain ⟨m, t, ht⟩ := (serreSectionModuleComparison G hG hd hf).1 s
    let y : 𝓜 (0 + ((m • d : ℕ) : ℤ)) := (φ _ (by positivity)).symm t
    have hs : alpha f d hd hf s =
        mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := by
      apply (hnorm f d hd hf m y s).mpr
      simpa only [y, AddEquiv.apply_symm_apply] using ht
    rw [serreSectionModuleChartScalar k G M 𝓜 hsmul φ hφ f d hd hf
      (alpha f d hd hf) (hnorm f d hd hf) l a ha m y s hs]
    simp only [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
      hs, mk_smul_mk]
    congr 1
    apply Subtype.ext
    exact pow_add f l m
  · intro f g d b hd hb hf hg inc e c a he ha hrel m y s hs
    -- The comparison supplies a homogeneous representative for this same section.
    obtain ⟨n, t, ht⟩ := (serreSectionModuleComparison G hG hd hf).1 s
    let z : 𝓜 (0 + ((n • d : ℕ) : ℤ)) := (φ _ (by positivity)).symm t
    have hz : alpha f d hd hf s =
        mk (z : M) (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) := by
      apply (hnorm f d hd hf n z s).mpr
      simpa only [z, AddEquiv.apply_symm_apply] using ht
    have hres := serreSectionModuleChartRestriction k G M 𝓜 hsmul φ hφ
      f g d b hd hb hf hg (alpha f d hd hf) (alpha g b hb hg)
      (hnorm f d hd hf) (hnorm g b hb hg) inc e c a he ha hrel n z s hz
    refine hres.trans ?_
    exact fractionChange_eq f g a e n m hrel (z : M) y (hz.symm.trans hs)

end AlgebraicGeometry.Proj
