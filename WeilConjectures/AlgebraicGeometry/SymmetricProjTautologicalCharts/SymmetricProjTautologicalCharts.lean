/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Transition
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjNormalizedDescent
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjOpenComparison
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjFreeComparison

/-!
# Degree-one charts of the tautological quotient on symmetric Proj

Source: Stacks Project, Constructions, Tags 01OB, 01NR, 01MS and 01OE.

The auxiliary predicates spell out fraction, frame and restriction equations for the
existing normalized quotient datum. They neither select a line bundle nor assume its
existence. The only theorem asserts existence, including all these equations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι

section Affine

variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (ι : M →ₗ[R] A)
    (hι : ∀ m : M, ι m ∈ 𝒜 1)

/-- Explicit chart equations for the specified degree-one generators. The module
`degreePart` is the actual submodule of ordinary localization. The chart equivalence
is additive and explicitly respects the action through `awayToSection`, hence is linear.
Source: Stacks, Tags 01MS, 01OB and 01M4. -/
def AffineChartFormulas : Prop :=
  (⨆ m : M, Proj.basicOpen 𝒜 (ι m)) = ⊤ ∧
  (∀ m : M, IsAffineOpen (Proj.basicOpen 𝒜 (ι m))) ∧
  (∀ m : M,
    ∃ (φ : Away 𝒜 (ι m) ≃ₗ[Away 𝒜 (ι m)]
          degreePart 𝒜 (Submonoid.powers (ι m)) 1)
      (τ : degreePart 𝒜 (Submonoid.powers (ι m)) 1 ≃+
          Γ(Proj.twist 𝒜 1, Proj.basicOpen 𝒜 (ι m))),
      (∀ z : Away 𝒜 (ι m),
        (φ z : Localization.Away (ι m)) = z.val * Localization.mk (ι m) 1) ∧
      (∀ z : degreePart 𝒜 (Submonoid.powers (ι m)) 1,
        (φ.symm z).val = (z : Localization.Away (ι m)) *
          Localization.mk 1 (⟨ι m, 1, pow_one (ι m)⟩ : Submonoid.powers (ι m))) ∧
      (∀ (c : Away 𝒜 (ι m)) (z : degreePart 𝒜 (Submonoid.powers (ι m)) 1),
        τ (c • z) = Proj.awayToSection 𝒜 (ι m) c • τ z) ∧
      (∀ c : Away 𝒜 (ι m),
        τ (φ c) = Proj.awayToSection 𝒜 (ι m) c • Proj.twistPowSection 1 (hι m)) ∧
      (∀ (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k + 1))
        (hp : (ι m) ^ k ∈ 𝒜 k)
        (x : Proj.basicOpen 𝒜 (ι m)),
        ((τ (degreePart.mk (m := 1) ⟨a, ha⟩ ⟨(ι m) ^ k, hp⟩
          (⟨k, rfl⟩ : (ι m) ^ k ∈ Submonoid.powers (ι m))
          (by omega))).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
            Localization.mk a
              (⟨(ι m) ^ k, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 k⟩ :
                x.1.asHomogeneousIdeal.toIdeal.primeCompl))) ∧
  (∀ m v : M,
    (Proj.unitToTwist (hι v)).app (Proj.basicOpen 𝒜 (ι m))
        (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (ι m))) =
      Proj.awayToSection 𝒜 (ι m)
        (Away.mk 𝒜 (hι m) 1 (ι v) (hι v)) • Proj.twistPowSection 1 (hι m)) ∧
  (∀ m n : M,
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 (ι m)
      (Away.mk 𝒜 (hι m) 1 (ι n) (hι n))) =
        Proj.basicOpen 𝒜 (ι m) ⊓ Proj.basicOpen 𝒜 (ι n)) ∧
  (∀ (m n : M) (W : (Proj 𝒜).Opens)
    (hm : W ≤ Proj.basicOpen 𝒜 (ι m)) (hn : W ≤ Proj.basicOpen 𝒜 (ι n)),
    (Proj.twist 𝒜 1).presheaf.map (homOfLE hm).op
        (Proj.twistPowSection 1 (hι m)) =
      (Proj 𝒜).presheaf.map (homOfLE hn).op
        (Proj.awayToSection 𝒜 (ι n) (Away.mk 𝒜 (hι n) 1 (ι m) (hι m))) •
          (Proj.twist 𝒜 1).presheaf.map (homOfLE hn).op
            (Proj.twistPowSection 1 (hι n))) ∧
  (∀ (m n l : M) (W : (Proj 𝒜).Opens)
    (hn : W ≤ Proj.basicOpen 𝒜 (ι n)) (hl : W ≤ Proj.basicOpen 𝒜 (ι l)),
    (Proj 𝒜).presheaf.map (homOfLE hn).op
        (Proj.awayToSection 𝒜 (ι n) (Away.mk 𝒜 (hι n) 1 (ι m) (hι m))) *
      (Proj 𝒜).presheaf.map (homOfLE hl).op
        (Proj.awayToSection 𝒜 (ι l) (Away.mk 𝒜 (hι l) 1 (ι n) (hι n))) =
      (Proj 𝒜).presheaf.map (homOfLE hl).op
        (Proj.awayToSection 𝒜 (ι l) (Away.mk 𝒜 (hι l) 1 (ι m) (hι m))))

include hι in
private theorem chart_linear_equiv (m : M) :
    ∃ φ : Away 𝒜 (ι m) ≃ₗ[Away 𝒜 (ι m)]
        degreePart 𝒜 (Submonoid.powers (ι m)) 1,
      (∀ z : Away 𝒜 (ι m),
        (φ z : Localization.Away (ι m)) = z.val * Localization.mk (ι m) 1) ∧
      (∀ z : degreePart 𝒜 (Submonoid.powers (ι m)) 1,
        (φ.symm z).val = (z : Localization.Away (ι m)) *
          Localization.mk 1 (⟨ι m, 1, pow_one (ι m)⟩ : Submonoid.powers (ι m))) := by
  classical
  let φ := degreePart.powDivPowEquiv (hι m)
    (Submonoid.mem_powers (ι m)) 1 0 (by norm_num : (1 : ℤ) * (1 - 0) = 1)
  have hf : ∀ c : Away 𝒜 (ι m),
      (φ c : Localization.Away (ι m)) = c.val * Localization.mk (ι m) 1 := by
    intro c
    simp only [φ, degreePart.powDivPowEquiv_apply, Submodule.coe_smul,
      degreePart.powDivPow, degreePart.coe_mk, Algebra.smul_def, pow_one, pow_zero]
    rfl
  refine ⟨φ, hf, ?_⟩
  intro z
  have he := congrArg
    (fun y : degreePart 𝒜 (Submonoid.powers (ι m)) 1 ↦ (y : Localization.Away (ι m)))
    (φ.apply_symm_apply z)
  rw [hf] at he
  rw [← he, mul_assoc, Localization.mk_mul]
  simp

private theorem chart_sections_equiv (m : M) :
    ∃ τ : Away 𝒜 (ι m) ≃+ Γ(Proj.twist 𝒜 1, Proj.basicOpen 𝒜 (ι m)),
      ∀ c : Away 𝒜 (ι m),
        τ c = Proj.awayToSection 𝒜 (ι m) c • Proj.twistPowSection 1 (hι m) := by
  classical
  let ψ : Away 𝒜 (ι m) →+ Γ(Proj.twist 𝒜 1, Proj.basicOpen 𝒜 (ι m)) :=
    { toFun := fun c ↦ Proj.awayToSection 𝒜 (ι m) c • Proj.twistPowSection 1 (hι m)
      map_zero' := by simp
      map_add' := by intros; simp [add_smul] }
  have hb : Function.Bijective ψ :=
    (Proj.isFreeGenerator_twistPowSection 1 (hι m)).bijective.comp
      (ConcreteCategory.bijective_of_isIso
        (Proj.basicOpenIsoAway 𝒜 (ι m) (hι m) (by decide)).hom)
  exact ⟨AddEquiv.ofBijective ψ hb, fun _ ↦ rfl⟩

private theorem chart_transition (m n : M) (W : (Proj 𝒜).Opens)
    (hm : W ≤ Proj.basicOpen 𝒜 (ι m)) (hn : W ≤ Proj.basicOpen 𝒜 (ι n)) :
    (Proj.twist 𝒜 1).presheaf.map (homOfLE hm).op
        (Proj.twistPowSection 1 (hι m)) =
      (Proj 𝒜).presheaf.map (homOfLE hn).op
        (Proj.awayToSection 𝒜 (ι n) (Away.mk 𝒜 (hι n) 1 (ι m) (hι m))) •
          (Proj.twist 𝒜 1).presheaf.map (homOfLE hn).op
            (Proj.twistPowSection 1 (hι n)) :=
  (Proj.map_awayToSection_smul_twistPowSection_one (hι m) (hι n) (hι m) hm hn).symm

private theorem chart_generator (m v : M) :
    (Proj.unitToTwist (hι v)).app (Proj.basicOpen 𝒜 (ι m))
        (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (ι m))) =
      Proj.awayToSection 𝒜 (ι m)
        (Away.mk 𝒜 (hι m) 1 (ι v) (hι v)) • Proj.twistPowSection 1 (hι m) := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  have h3 := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 (ι m)
    (Away.mk 𝒜 (hι m) 1 (ι v) (hι v)) x
  rw [Proj.val_unitToTwist_app_apply, Proj.coe_twist_smul_apply,
    Proj.val_twistPowSection_apply]
  refine (by simp : _ = Localization.mk (ι v) 1).trans
    (Eq.trans ?_ (congrArg (· * _) h3.symm))
  simp only [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    RingHom.id_apply]
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq]
  simp [mul_comm]

private theorem chart_cocycle (m n l : M) (W : (Proj 𝒜).Opens)
    (hn : W ≤ Proj.basicOpen 𝒜 (ι n)) (hl : W ≤ Proj.basicOpen 𝒜 (ι l)) :
    (Proj 𝒜).presheaf.map (homOfLE hn).op
        (Proj.awayToSection 𝒜 (ι n) (Away.mk 𝒜 (hι n) 1 (ι m) (hι m))) *
      (Proj 𝒜).presheaf.map (homOfLE hl).op
        (Proj.awayToSection 𝒜 (ι l) (Away.mk 𝒜 (hι l) 1 (ι n) (hι n))) =
      (Proj 𝒜).presheaf.map (homOfLE hl).op
        (Proj.awayToSection 𝒜 (ι l) (Away.mk 𝒜 (hι l) 1 (ι m) (hι m))) := by
  apply ((Proj.isFreeGenerator_twistPowSection 1 (hι l)).map hl).smul_left_injective
  dsimp only
  rw [mul_smul, ← chart_transition 𝒜 ι hι n l W hn hl]
  have hg (i : M) (hi : W ≤ Proj.basicOpen 𝒜 (ι i)) :
      (Proj 𝒜).presheaf.map (homOfLE hi).op
          (Proj.awayToSection 𝒜 (ι i) (Away.mk 𝒜 (hι i) 1 (ι m) (hι m))) •
        (Proj.twist 𝒜 1).presheaf.map (homOfLE hi).op
          (Proj.twistPowSection 1 (hι i)) =
      (Proj.twist 𝒜 1).presheaf.map (homOfLE hi).op
        ((Proj.unitToTwist (hι m)).app (Proj.basicOpen 𝒜 (ι i))
          (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (ι i)))) := by
    rw [chart_generator 𝒜 ι hι i m, Scheme.Modules.map_smul]
  rw [hg n hn, hg l hl]
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change (((Proj.unitToTwist (hι m)).app (Proj.basicOpen 𝒜 (ι n))
    (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (ι n)))).1 ⟨x.1, hn x.2⟩).1 =
    (((Proj.unitToTwist (hι m)).app (Proj.basicOpen 𝒜 (ι l))
      (1 : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (ι l)))).1 ⟨x.1, hl x.2⟩).1
  rw [Proj.val_unitToTwist_app_apply, Proj.val_unitToTwist_app_apply]
  simp

private theorem chart_basicOpen (m n : M) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 (ι m)
      (Away.mk 𝒜 (hι m) 1 (ι n) (hι n))) =
        Proj.basicOpen 𝒜 (ι m) ⊓ Proj.basicOpen 𝒜 (ι n) := by
  apply le_antisymm
  · intro x hx
    have hm := (Proj 𝒜).basicOpen_le (Proj.awayToSection 𝒜 (ι m)
      (Away.mk 𝒜 (hι m) 1 (ι n) (hι n))) hx
    refine ⟨hm, ?_⟩
    have hu := (Proj.mem_basicOpen_iff_isUnit_val
      (Proj.awayToSection 𝒜 (ι m) (Away.mk 𝒜 (hι m) 1 (ι n) (hι n))) hm).mp hx
    have hh := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 (ι m)
      (Away.mk 𝒜 (hι m) 1 (ι n) (hι n)) ⟨x, hm⟩
    have hu' := hh ▸ hu
    change ι n ∈ x.asHomogeneousIdeal.toIdeal.primeCompl
    simpa only [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      RingHom.id_apply, IsLocalization.AtPrime.isUnit_mk'_iff] using hu'
  · intro x hx
    apply (Proj.mem_basicOpen_iff_isUnit_val
      (Proj.awayToSection 𝒜 (ι m) (Away.mk 𝒜 (hι m) 1 (ι n) (hι n))) hx.1).mpr
    have hh := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 (ι m)
      (Away.mk 𝒜 (hι m) 1 (ι n) (hι n)) ⟨x, hx.1⟩
    refine hh.symm ▸ ?_
    simpa only [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
      RingHom.id_apply, IsLocalization.AtPrime.isUnit_mk'_iff] using
        (show ι n ∈ x.asHomogeneousIdeal.toIdeal.primeCompl from hx.2)

set_option backward.isDefEq.respectTransparency true in
include hι in
private theorem chart_full_equiv (m : M) :
    ∃ (φ : Away 𝒜 (ι m) ≃ₗ[Away 𝒜 (ι m)]
          degreePart 𝒜 (Submonoid.powers (ι m)) 1)
      (τ : degreePart 𝒜 (Submonoid.powers (ι m)) 1 ≃+
          Γ(Proj.twist 𝒜 1, Proj.basicOpen 𝒜 (ι m))),
      (∀ z : Away 𝒜 (ι m),
        (φ z : Localization.Away (ι m)) = z.val * Localization.mk (ι m) 1) ∧
      (∀ z : degreePart 𝒜 (Submonoid.powers (ι m)) 1,
        (φ.symm z).val = (z : Localization.Away (ι m)) *
          Localization.mk 1 (⟨ι m, 1, pow_one (ι m)⟩ : Submonoid.powers (ι m))) ∧
      (∀ (c : Away 𝒜 (ι m)) (z : degreePart 𝒜 (Submonoid.powers (ι m)) 1),
        τ (c • z) = Proj.awayToSection 𝒜 (ι m) c • τ z) ∧
      (∀ c : Away 𝒜 (ι m),
        τ (φ c) = Proj.awayToSection 𝒜 (ι m) c • Proj.twistPowSection 1 (hι m)) ∧
      (∀ (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k + 1))
        (hp : (ι m) ^ k ∈ 𝒜 k)
        (x : Proj.basicOpen 𝒜 (ι m)),
        ((τ (degreePart.mk (m := 1) ⟨a, ha⟩ ⟨(ι m) ^ k, hp⟩
          (⟨k, rfl⟩ : (ι m) ^ k ∈ Submonoid.powers (ι m))
          (by omega))).1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
            Localization.mk a
              (⟨(ι m) ^ k, x.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem x.2 k⟩ :
                x.1.asHomogeneousIdeal.toIdeal.primeCompl)) := by
  classical
  set_option backward.isDefEq.respectTransparency true in
   set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨φ, hφ, hφinv⟩ := chart_linear_equiv 𝒜 ι hι m
  obtain ⟨ψ, hψ⟩ := chart_sections_equiv 𝒜 ι hι m
  let τ : degreePart 𝒜 (Submonoid.powers (ι m)) 1 ≃+
      Γ(Proj.twist 𝒜 1, Proj.basicOpen 𝒜 (ι m)) := φ.symm.toAddEquiv.trans ψ
  have hτ (z : degreePart 𝒜 (Submonoid.powers (ι m)) 1) :
      τ z = Proj.awayToSection 𝒜 (ι m) (φ.symm z) •
        Proj.twistPowSection 1 (hι m) := hψ _
  refine ⟨φ, τ, hφ, hφinv, ?_, ?_, ?_⟩
  · intro c z
    calc
      τ (c • z) = Proj.awayToSection 𝒜 (ι m) (φ.symm (c • z)) •
          Proj.twistPowSection 1 (hι m) := hτ _
      _ = Proj.awayToSection 𝒜 (ι m) (c * φ.symm z) •
          Proj.twistPowSection 1 (hι m) := by
        rw [φ.symm.map_smul, smul_eq_mul]
      _ = (Proj.awayToSection 𝒜 (ι m) c * Proj.awayToSection 𝒜 (ι m) (φ.symm z)) •
          Proj.twistPowSection 1 (hι m) :=
        congrArg (fun a : Γ(Proj 𝒜, Proj.basicOpen 𝒜 (ι m)) ↦
          a • Proj.twistPowSection 1 (hι m))
            (map_mul (Proj.awayToSection 𝒜 (ι m)).hom c (φ.symm z))
      _ = Proj.awayToSection 𝒜 (ι m) c •
          (Proj.awayToSection 𝒜 (ι m) (φ.symm z) • Proj.twistPowSection 1 (hι m)) :=
        mul_smul _ _ _
      _ = Proj.awayToSection 𝒜 (ι m) c • τ z :=
        congrArg (fun a ↦ Proj.awayToSection 𝒜 (ι m) c • a) (hτ z).symm
  · intro c
    simp only [hτ, φ.symm_apply_apply]
  · intro k a ha hp x
    rw [hτ, Proj.coe_twist_smul_apply, Proj.val_twistPowSection_apply]
    have hmap := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 (ι m)
      (φ.symm (degreePart.mk (m := 1) ⟨a, ha⟩ ⟨(ι m) ^ k, hp⟩ ⟨k, rfl⟩ (by omega))) x
    refine (congrArg (· * _) hmap).trans ?_
    rw [hφinv]
    simp only [degreePart.coe_mk, map_mul, Localization.mk_eq_mk',
      IsLocalization.map_mk', RingHom.id_apply]
    rw [← IsLocalization.mk'_mul, ← IsLocalization.mk'_mul,
      IsLocalization.mk'_eq_iff_eq]
    simp only [Submonoid.coe_mul, pow_one, Int.toNat_one,
      show (-1 : ℤ).toNat = 0 from rfl, pow_zero, mul_one]
    congr 1
    ring

end Affine

private theorem symmetric_chart_cover {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M]
    (𝒜 : ℕ → Submodule R (SymmetricAlgebra R M)) [GradedAlgebra 𝒜]
    (hι : ∀ m : M, SymmetricAlgebra.ι R M m ∈ 𝒜 1) :
    (⨆ m : M, Proj.basicOpen 𝒜 (SymmetricAlgebra.ι R M m)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top' 𝒜 (SymmetricAlgebra.ι R M) (fun m ↦ ⟨1, hι m⟩)
  apply top_unique
  intro x hx
  clear hx
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    have h := (Algebra.adjoin (𝒜 0) (Set.range (SymmetricAlgebra.ι R M))).algebraMap_mem
      (algebraMap R (𝒜 0) r)
    exact h
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul a b ha hb => exact mul_mem ha hb
  | add a b ha hb => exact add_mem ha hb

private theorem affine_chart_formulas (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (U : S.affineOpens) :
    ∃ hι : ∀ m : E.val.obj (op U.1),
      SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1,
      AffineChartFormulas ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
        (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))) hι := by
  let : GradedAlgebra ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) :=
    (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra U
  let hι (m : E.val.obj (op U.1)) :
      SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
        (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1 := by
    change _ ∈ _ ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ m
  refine ⟨hι, ?_⟩
  refine ⟨symmetric_chart_cover _ hι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact Proj.isAffineOpen_basicOpen _ _ (hι m) (by decide)
  · exact chart_full_equiv _ _ hι
  · exact chart_generator _ _ hι
  · exact chart_basicOpen _ _ hι
  · exact chart_transition _ _ hι
  · exact chart_cocycle _ _ hι

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The affine-restriction comparison respects the chosen normalization charts of D,
and sends every degree-one homogeneous section to its restricted section. The formula
on arbitrary fractions is expressed both in degree zero and on degree-one twist sections.
Source: Stacks, Tags 01NR, 01N2 and 01OB. -/
def AffineRestrictionFormulas
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E) : Prop :=
  ∀ (U V : S.affineOpens) (h : U ≤ V),
    Nonempty (NormalizedAffineRestriction E D U V h) ∧
    (∀ (e : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (he : e ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V 1)
        (k : ℕ) (a : (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V)
        (ha : a ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V (k • 1)),
        Away.map ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h) e
            (Away.mk ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) he k a ha) =
          Away.mk ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
            (((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem he) k
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).res h a)
            (((SymmetricAlgebraSheaf.gradedAlgebraData E).res h).map_mem ha))

attribute [local irreducible] AffineChartFormulas AffineRestrictionFormulas
  Proj.twist
  ProjectiveBundleQuotientGeometry.HasOpenCompatibility
  ProjectiveBundleQuotientGeometry.HasFreeCompatibility

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized tautological quotient and its degree-one charts, affine restrictions,
open-base comparisons and ordered finite-free comparisons.

Source: Stacks Project, Constructions, Tags 01OB, 01NR, 01MS and 01OE. -/
theorem symmetric_proj_tautological_chart_gluing (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] :
    ∃ D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E,
      ProjectiveBundleQuotientGeometry.HasOpenCompatibility D ∧
      ProjectiveBundleQuotientGeometry.HasFreeCompatibility D ∧
      AffineRestrictionFormulas E D ∧
      ∀ U : S.affineOpens,
        ∃ hι : ∀ m : E.val.obj (op U.1),
          SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈
            (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1,
          AffineChartFormulas ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U)
            (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))) hι := by
  set_option backward.isDefEq.respectTransparency true in
   set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨D, hD⟩ := exists_normalized_quotient_with_affine_restriction S E
    refine ⟨D, open_compatibility_of_normalized_quotient S E D,
      free_compatibility_of_normalized_quotient S E D, ?_, affine_chart_formulas S E⟩
    unfold AffineRestrictionFormulas
    intro U V h
    exact ⟨hD U V h, fun e he k a ha ↦ Away.map_mk _ e he k a ha⟩

end AlgebraicGeometry.SymmetricProjTautologicalCharts
