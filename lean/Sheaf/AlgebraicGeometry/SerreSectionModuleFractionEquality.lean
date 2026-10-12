/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous

import Sheaf.AlgebraicGeometry.SerreSectionModuleComparison
import Sheaf.AlgebraicGeometry.SerreSectionModuleFractionAdd
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-!
# Equality of represented homogeneous fractions

Source: Stacks Project, Proposition 0BXD, final paragraph.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace LocalizedModule
open HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma injective_app_of_restrict_iso
    {X : Scheme.{u}} {F H : X.Modules} (ψ : F ⟶ H) (U V : X.Opens)
    (hVU : V ≤ U) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ)] :
    Function.Injective (ψ.app V) := by
  obtain ⟨V', rfl⟩ : ∃ V' : U.toScheme.Opens, U.ι ''ᵁ V' = V :=
    ⟨U.ι ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hVU]⟩
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctor U.ι).map ψ).app V')).1

private lemma basicOpen_le_pow
    {k : Type u} [Field k] (f : MvPolynomial (Fin 2) k) (m : ℕ) :
    basicOpen (homogeneousSubmodule (Fin 2) k) f ≤
      basicOpen (homogeneousSubmodule (Fin 2) k) (f ^ m) := by
  by_cases hm : m = 0
  · simp [hm]
  · rw [basicOpen_pow _ _ m (Nat.pos_of_ne_zero hm)]

private lemma isIso_restrict_tensor
    {X : Scheme.{u}} (G : X.Modules) {F H : X.Modules} (ψ : F ⟶ H) {U : X.Opens}
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map ψ)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (G ◁ ψ)) := by
  rw [NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι)] at *
  have h := Functor.LaxMonoidal.μ_natural_right (Scheme.Modules.pullback U.ι) G ψ
  rw [(IsIso.eq_inv_comp _).mpr h.symm]
  infer_instance

private lemma injective_tensor_unitToTwist
    {k : Type u} [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    {f : MvPolynomial (Fin 2) k} {d : ℕ}
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d) (m : ℕ) :
    Function.Injective
      (((ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded m hf)).app
        (basicOpen (homogeneousSubmodule (Fin 2) k) f)) := by
  have := isIso_restrict_tensor G
    (unitToTwist (SetLike.pow_mem_graded m hf))
    (U := basicOpen (homogeneousSubmodule (Fin 2) k) (f ^ m))
  have : IsIso ((Scheme.Modules.restrictFunctor
      (basicOpen (homogeneousSubmodule (Fin 2) k) (f ^ m)).ι).map
        ((ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded m hf))) := by
    rw [Functor.map_comp]
    infer_instance
  exact injective_app_of_restrict_iso _ _ _ (basicOpen_le_pow f m)

private lemma fraction_zero_iff
    (k : Type u) [Field k]
    (G : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (φ : ∀ z : ℤ, 0 ≤ z →
        (𝓜 z ≃+ Γ(G ⊗ Proj.twist (homogeneousSubmodule (Fin 2) k) z, ⊤)))
    (hφ : ∀ (z : ℤ) (hz : 0 ≤ z) (e : ℕ) (hze : 0 ≤ z + e) (a : MvPolynomial (Fin 2) k)
        (ha : a ∈ homogeneousSubmodule (Fin 2) k e)
        (y : 𝓜 z) (hay : a • (y : M) ∈ 𝓜 (z + e)),
        φ (z + e) hze ⟨a • (y : M), hay⟩ =
          Scheme.Modules.Hom.app (G ◁ Proj.twistMul z ha) ⊤ (φ z hz y))
    (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (m : ℕ) (y : 𝓜 (0 + ((m • d : ℕ) : ℤ)))
    (s : G.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)))
    (hy : (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
        (0 + ((m • d : ℕ) : ℤ))).presheaf.map
        (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
        (φ _ (by positivity) y) =
      (((ρ_ G).inv ≫ G ◁ unitToTwist (SetLike.pow_mem_graded m hf)).app
        (basicOpen (homogeneousSubmodule (Fin 2) k) f)) s) :
    mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) = 0 ↔ s = 0 := by
  have hmem (e : ℕ) : f ^ e • (y : M) ∈
      𝓜 ((0 + ((m • d : ℕ) : ℤ)) + ((e • d : ℕ) : ℤ)) := by
    simpa only [add_comm] using
      hsmul (e • d) _ (f ^ e) y (SetLike.pow_mem_graded e hf) y.property
  have hphi_zero (e : ℕ) :
      (G ◁ twistMul (0 + ((m • d : ℕ) : ℤ))
        (SetLike.pow_mem_graded e hf)).app ⊤ (φ _ (by positivity) y) = 0 ↔
        f ^ e • (y : M) = 0 := by
    rw [← hφ _ (by positivity) (e • d) (by positivity) (f ^ e)
      (SetLike.pow_mem_graded e hf) y (hmem e)]
    have hzero : (φ _ (by positivity))
        (0 : 𝓜 ((0 + ((m • d : ℕ) : ℤ)) + ((e • d : ℕ) : ℤ))) = 0 := map_zero _
    constructor
    · intro hz
      have hz' := (φ _ (by positivity)).injective (hz.trans hzero.symm)
      exact congrArg Subtype.val hz'
    · intro hz
      have hz' : (⟨f ^ e • (y : M), hmem e⟩ :
          𝓜 ((0 + ((m • d : ℕ) : ℤ)) + ((e • d : ℕ) : ℤ))) = 0 :=
        Subtype.ext hz
      rw [hz', map_zero]
  constructor
  · intro hx
    have hx' : mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) =
        mk (0 : M) (1 : Submonoid.powers f) := by simpa using hx
    obtain ⟨a, ha⟩ := LocalizedModule.mk_eq.mp hx'
    obtain ⟨e, he⟩ := a.property
    have hekill : f ^ e • (y : M) = 0 := by
      simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, smul_zero,
        ← he] using ha
    have hp := (hphi_zero e).mpr hekill
    have := isIso_restrict_tensor G
      (twistMul (0 + ((m • d : ℕ) : ℤ)) (SetLike.pow_mem_graded e hf))
      (U := basicOpen (homogeneousSubmodule (Fin 2) k) (f ^ e))
    have hinj := injective_app_of_restrict_iso
      (G ◁ twistMul (0 + ((m • d : ℕ) : ℤ)) (SetLike.pow_mem_graded e hf))
      (basicOpen (homogeneousSubmodule (Fin 2) k) (f ^ e))
      (basicOpen (homogeneousSubmodule (Fin 2) k) f) (basicOpen_le_pow f e)
    have hr : (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
        (0 + ((m • d : ℕ) : ℤ))).presheaf.map
        (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
        (φ _ (by positivity) y) = 0 := by
      apply hinj
      rw [Scheme.Modules.Hom.app_presheaf_map, hp, map_zero, map_zero]
    apply injective_tensor_unitToTwist G hf m
    rw [← hy, hr, map_zero]
  · intro hs
    have ht : (G ⊗ twist (homogeneousSubmodule (Fin 2) k)
        (0 + ((m • d : ℕ) : ℤ))).presheaf.map
        (homOfLE le_top : basicOpen (homogeneousSubmodule (Fin 2) k) f ⟶ ⊤).op
        (φ _ (by positivity) y) = 0 := by rw [hy, hs, map_zero]
    obtain ⟨e, he⟩ := (serreSectionModuleComparison G hG hd hf).2
      m (φ _ (by positivity) y) ht
    have hyzero := (hphi_zero e).mp he
    have hx : mk (y : M) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) =
        mk (0 : M) (1 : Submonoid.powers f) := by
      apply LocalizedModule.mk_eq.mpr
      refine ⟨⟨f ^ e, ⟨e, rfl⟩⟩, ?_⟩
      simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, smul_zero]
        using hyzero
    simpa using hx

/-- Equality of fractions is equivalent to equality of their represented sections.
Source: Stacks Project, Proposition 0BXD, final paragraph.
(blueprint: lem-sc-p1-serre-section-module-fraction-equality)

Proof: First prove the zero criterion for a represented numerator y/f^m and
section s. LocalizedModule.mk_eq identifies vanishing of the fraction with
annihilation of y by a power f^e. Compatibility of phi turns this into
vanishing of the twist-multiplied global section. Restrict to D+(f) and cancel
multiplication by f^e and then by f^m: these maps remain isomorphisms after
tensoring with G. Conversely, if s=0, the restriction of phi(y) is zero;
the annihilation clause of serreSectionModuleComparison and injectivity of
phi give f^e*y=0, hence the fraction is zero. Negation preserves the relation
by additivity. Apply serreSectionModuleFractionAdd to the first relation and
the negative of the second, and use the zero criterion for x-z and s-t.
For exponent zero, D+(f) is contained in D+(1); positive powers have the same
basic open as f, so the proof also covers f=0 without a separate case. -/
theorem serreSectionModuleFractionEquality
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
    ∀ x z s t, Rel x s → Rel z t → (x = z ↔ s = t) := by
  have _ := h𝓜
  have _ := hneg
  intro Rel
  have hnegrel : ∀ x s, Rel x s → Rel (-x) (-s) := by
    rintro x s ⟨m, y, hx, hy⟩
    refine ⟨m, -y, ?_, ?_⟩
    · rw [hx, ← LocalizedModule.mk_neg]
      rfl
    · simpa only [map_neg] using congrArg Neg.neg hy
  intro x z s t hx hz
  have hadd := serreSectionModuleFractionAdd k G M 𝓜 hsmul φ hφ f d hf
  obtain ⟨m, y, hxy, hy⟩ := hadd x (-z) s (-t) hx (hnegrel z t hz)
  have hzero := fraction_zero_iff k G hG M 𝓜 hsmul φ hφ f d hd hf m y (s + -t) hy
  calc
    x = z ↔ x - z = 0 := sub_eq_zero.symm
    _ ↔ s - t = 0 := by simpa only [sub_eq_add_neg, ← hxy] using hzero
    _ ↔ s = t := sub_eq_zero

end AlgebraicGeometry.Proj
