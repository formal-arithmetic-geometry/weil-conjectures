/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

import Sheaf.AlgebraicGeometry.CoherentProjRepresentation
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjectiveSpace.SheafifyGradedChain
import Sheaf.AlgebraicGeometry.ProjectiveSpace.HomogeneousBasisSheafTwists
import Sheaf.RingTheory.GradedSyzygy
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Sheaf.AlgebraicGeometry.ProjSheafificationExact

/-!
# Serre duality on the projective line

Let `k` be a field, `ℙ¹_k = ProjectiveLine (Spec k)` and `ω = Ω¹_{ℙ¹_k/k}`. Every coherent
`𝒪_{ℙ¹}`-module `𝒢` has a resolution `0 → ℰ₂ → ℰ₁ → ℰ₀ → 𝒢 → 0` by finite direct sums of twists
`𝒪(d)`, and the two duality isomorphisms
`H¹(ℙ¹, 𝒢)^∨ ≅ Hom(𝒢, ω)` and `H⁰(ℙ¹, 𝒢)^∨ ≅ Ext¹(𝒢, ω)` hold.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist`: resolutions by twists.
- `AlgebraicGeometry.ProjectiveLine.bijective_dualPairing_twist`: the duality pairing
  `Hom(𝒪(a), ω) → H¹(ℙ¹, 𝒪(a))^∨` is bijective.
- `AlgebraicGeometry.ProjectiveLine.bijective_dualPairing_of_isCoherent`: the duality pairing
  `Hom(𝒢, ω) → H¹(ℙ¹, 𝒢)^∨` is bijective for coherent `𝒢`.
- `AlgebraicGeometry.ProjectiveLine.nonempty_dual_H_one_iso`: `H¹(ℙ¹, 𝒢)^∨ ≅ Hom(𝒢, ω)`,
  naturally in coherent `𝒢`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_dual_H_zero_addEquiv_ext_of_shortExact`:
  `H⁰(X, 𝒢)^∨ ≅ Ext¹(𝒢, ω)` from a resolution `0 → 𝒦 → ℰ → 𝒢 → 0` on which the `H¹`-duality
  pairing is known.
- `AlgebraicGeometry.ProjectiveLine.nonempty_dual_H_zero_addEquiv_ext`:
  `H⁰(ℙ¹, 𝒢)^∨ ≅ Ext¹(𝒢, ω)`.

## Implementation notes

Coherence is spelled as `AlgebraicGeometry.Scheme.Modules.isCoherent`. The `𝒪_{ℙ¹}`-module
`Hom(𝒢, ω)` of global homomorphisms is written as `H⁰(ℙ¹, Hom(𝒢, ω))`, the global sections of the
internal hom, so that it is a functor to `k`-vector spaces.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

open Scheme.Modules

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- **The dual of a twist.** `𝒪(a)ᵛ ≅ 𝒪(-a)` on `ℙ(n; S)`: both are tensor inverses of the
invertible module `𝒪(a)`. -/
theorem nonempty_dual_twist_iso (a : ℤ) : Nonempty ((twist n S a)ᵛ ≅ twist n S (-a)) := by
  obtain ⟨e⟩ := nonempty_tensorObj_twist_iso n S (-a) a
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit (twist n S a)
  let e' : twist n S (-a) ⊗ twist n S a ≅ 𝟙_ _ :=
    e ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫ (unitIsoTwistZero n S).symm
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso e'.symm _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ d ≪≫ ρ_ _⟩

end ProjectiveSpace

namespace Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [HasExt.{u} X.Modules]
  {ω : X.Modules} (t : Module.Dual k (ω.H 1))

/-- **`H⁰`-duality from a resolution.** Let `0 → 𝒦 → ℰ → 𝒢 → 0` be a short exact sequence of
`𝒪_X`-modules with `H⁰(ℰ) = 0` and `Ext¹(ℰ, ω) = 0`, such that the duality pairing
`Hom(-, ω) → H¹(X, -)^∨` is bijective on `𝒦` and surjective on `ℰ`. Then
`H⁰(X, 𝒢)^∨ ≅ Ext¹(𝒢, ω)`.

Both sides are cokernels of `Hom(ℰ, ω) ⟶ Hom(𝒦, ω)`: the `Ext` side by the long exact `Ext`
sequence, and the `H⁰` side because `δ : H⁰(𝒢) ⟶ H¹(𝒦)` is the kernel of `H¹(𝒦) ⟶ H¹(ℰ)`, so
that `H⁰(𝒢)^∨` is the cokernel of `H¹(ℰ)^∨ ⟶ H¹(𝒦)^∨`. -/
lemma nonempty_dual_H_zero_addEquiv_ext_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Subsingleton (S.X₂.H 0)] [Subsingleton (Ext S.X₂ ω 1)]
    (h₁ : Function.Bijective (dualPairing t S.X₁))
    (h₂ : Function.Surjective (dualPairing t S.X₂)) :
    Nonempty (Module.Dual k (S.X₃.H 0) ≃+ Ext S.X₃ ω 1) := by
  let δ := H.δLinearMap k hS 0
  have hδ : Function.Injective δ := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (H.ker_δ_eq_range_map_g hS 0).le hx
    rw [Subsingleton.elim y 0, map_zero]
  have hfδ (x : S.X₃.H 0) : H.map S.f 1 (δ x) = 0 :=
    (H.ker_map_f_eq_range_δ hS 0).ge ⟨x, rfl⟩
  let Ψ : Ext S.X₁ ω 0 →+ Module.Dual k (S.X₃.H 0) :=
    δ.dualMap.toAddMonoidHom.comp
      ((dualPairing t S.X₁).comp Abelian.Ext.addEquiv₀.toAddMonoidHom)
  let D : Ext S.X₁ ω 0 →+ Ext S.X₃ ω 1 := hS.extClass.precomp ω (add_zero 1)
  have hΨφ (φ : S.X₁ ⟶ ω) :
      Ψ (Abelian.Ext.addEquiv₀.symm φ) = δ.dualMap (dualPairing t S.X₁ φ) := by
    change δ.dualMap (dualPairing t S.X₁ (Abelian.Ext.addEquiv₀
      (Abelian.Ext.addEquiv₀.symm φ))) = _
    rw [AddEquiv.apply_symm_apply]
  have hD : Function.Surjective D := fun x ↦
    Abelian.Ext.contravariant_sequence_exact₃ hS ω x (Subsingleton.elim _ _) (add_zero 1)
  have hΨ : Function.Surjective Ψ := fun ν ↦ by
    obtain ⟨μ, rfl⟩ := LinearMap.dualMap_surjective_of_injective hδ ν
    obtain ⟨φ, hφ⟩ := h₁.2 μ
    exact ⟨Abelian.Ext.addEquiv₀.symm φ, by rw [hΨφ, hφ]⟩
  have hker : D.ker = Ψ.ker := by
    ext x
    obtain ⟨φ, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective x
    simp only [AddMonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS ω _ (add_zero 1) hx
      obtain ⟨ψ, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective y
      have : φ = S.f ≫ ψ := by
        apply Abelian.Ext.addEquiv₀.symm.injective
        rw [← hy]
        exact Abelian.Ext.mk₀_comp_mk₀ _ _
      subst this
      rw [hΨφ, dualPairing_comp]
      refine LinearMap.ext fun x ↦ ?_
      change dualPairing t S.X₂ ψ (H.map S.f 1 (δ x)) = 0
      rw [hfδ, map_zero]
    · intro hx
      rw [hΨφ] at hx
      have hl : dualPairing t S.X₁ φ ∈
          (LinearMap.ker (H.mapLinearMap k S.f 1)).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro v hv
        obtain ⟨w, rfl⟩ := (H.ker_map_f_eq_range_δ hS 0).le hv
        exact LinearMap.congr_fun hx w
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hl
      obtain ⟨μ, hμ⟩ := hl
      obtain ⟨ψ, rfl⟩ := h₂ μ
      have : φ = S.f ≫ ψ := h₁.1 (by rw [dualPairing_comp]; exact hμ.symm)
      subst this
      change hS.extClass.comp (Abelian.Ext.mk₀ (S.f ≫ ψ)) (add_zero 1) = 0
      rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
        hS.extClass_comp, Abelian.Ext.zero_comp]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective Ψ hΨ).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective D hD))⟩

end Scheme.Modules

namespace ProjectiveLine

variable (k : Type u) [Field k]

/-- **Resolutions by twists on `ℙ¹_k`.** Every coherent `𝒪_{ℙ¹_k}`-module `𝒢` has a resolution
`0 → ℰ₂ → ℰ₁ → ℰ₀ → 𝒢 → 0` in which each `ℰᵢ` is a finite direct sum of twists `𝒪(d)`. Indeed
`𝒢 = M^~` for a finitely generated graded module `M` over `k[x₀, x₁]`, which has a graded free
resolution of length two by the graded Hilbert syzygy theorem; sheafifying it gives the
resolution, since `S(d)^~ = 𝒪(d)`.

(blueprint: `lem-sc-p1-graded-resolution`) -/
theorem exists_exact_sigma_twist (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    let 𝒪 : ℤ → (ProjectiveLine (Spec (.of k))).Modules :=
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k))
    ∃ (n₀ n₁ n₂ : ℕ) (d₀ : Fin n₀ → ℤ) (d₁ : Fin n₁ → ℤ) (d₂ : Fin n₂ → ℤ)
      (f₂ : ∐ (fun j ↦ 𝒪 (d₂ j)) ⟶ ∐ (fun j ↦ 𝒪 (d₁ j)))
      (f₁ : ∐ (fun j ↦ 𝒪 (d₁ j)) ⟶ ∐ (fun j ↦ 𝒪 (d₀ j)))
      (f₀ : ∐ (fun j ↦ 𝒪 (d₀ j)) ⟶ 𝒢),
      Mono f₂ ∧ Epi f₀ ∧ (ComposableArrows.mk₃ f₂ f₁ f₀).Exact := by
  let := MvPolynomial.gradedAlgebra (σ := Fin 2) (R := k)
  obtain ⟨C, -, -⟩ := Proj.proj_shifted_free_is_twist k 0
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have : IsLocallyNoetherian (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)) :=
    LocallyOfFiniteType.isLocallyNoetherian C.iso.hom
  have hG := (isCoherent_iff_isQuasicoherent_and_isFiniteType _
    ((Scheme.Modules.pullback C.iso.hom).obj 𝒢)).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨M, hM, ℳ, hℳ, hsmul, F, ⟨eF⟩, alpha, halpha, hscalar, hres⟩ :=
    Proj.coherent_exists_graded_representation k _ hG
  let := hM
  obtain ⟨A, 𝒜, r, d, b, a₂, a₁, a₀, h𝒜, hA, hb, ha₂, ha₁, ha₀, hinj, hex₁,
      hex₀, hsurj⟩ := MvPolynomial.exists_graded_free_resolution_two ℳ hℳ hsmul
  obtain ⟨E, g₂, g₁, g₀, hE, hg₂, hg₀, hex⟩ :=
    Proj.sheafify_graded_chain k C M ℳ hℳ hsmul F alpha halpha hscalar
      hres A 𝒜 a₂ a₁ a₀ h𝒜 hA ha₂ ha₁ ha₀ hinj hex₁ hex₀ hsurj
  have eTw (i : Fin 3) :
      Nonempty ((Scheme.Modules.pullback C.iso.inv).obj (E i) ≅
        ∐ (fun j ↦ ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (d i j))) := by
    obtain ⟨alphaE, hαE, hsE, hrE⟩ := hE i
    exact Proj.homogeneous_basis_sheaf_twists k C (A i) (𝒜 i) (h𝒜 i) (hA i)
      (E i) alphaE hαE hsE hrE (r i) (d i) (b i) (hb i)
  obtain ⟨e₂⟩ := eTw 2
  obtain ⟨e₁⟩ := eTw 1
  obtain ⟨e₀⟩ := eTw 0
  let e : (Scheme.Modules.pullback C.iso.inv).obj F ≅ 𝒢 :=
    (Scheme.Modules.pullback C.iso.inv).mapIso eF ≪≫ (pullbackComp C.iso.inv C.iso.hom).app 𝒢 ≪≫
      (pullbackCongr C.iso.inv_hom_id).app 𝒢 ≪≫ (pullbackId _).app 𝒢
  let := hg₂
  let := hg₀
  refine ⟨r 0, r 1, r 2, d 0, d 1, d 2, e₂.inv ≫ g₂ ≫ e₁.hom,
    e₁.inv ≫ g₁ ≫ e₀.hom, e₀.inv ≫ g₀ ≫ e.hom, inferInstance, inferInstance, ?_⟩
  apply ComposableArrows.exact_of_iso _ hex
  exact ComposableArrows.isoMk₃ e₂ e₁ e₀ e
    (by change g₂ ≫ e₁.hom = e₂.hom ≫ (e₂.inv ≫ g₂ ≫ e₁.hom); simp)
    (by change g₁ ≫ e₀.hom = e₁.hom ≫ (e₁.inv ≫ g₁ ≫ e₀.hom); simp)
    (by change g₀ ≫ e.hom = e₀.hom ≫ (e₀.inv ≫ g₀ ≫ e.hom); simp)

/-- `Hom(𝒪(a), Ω¹_{ℙ¹_k/k}) ≅ 𝒪(-a - 2)`, since `Ω¹_{ℙ¹_k/k} ≅ 𝒪(-2)` is invertible and
`𝒪(a)ᵛ ≅ 𝒪(-a)`. -/
theorem nonempty_homObj_twist_iso (a : ℤ) :
    Nonempty (homObj (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) a)
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-a + -2)) := by
  obtain ⟨eω⟩ := nonempty_relativeDifferentials_iso_twist k
  have : (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.IsInvertible :=
    IsInvertible.of_iso eω.symm
  obtain ⟨ed⟩ := ProjectiveSpace.nonempty_dual_twist_iso (ULift.{u} (Fin 2)) (Spec (.of k)) a
  obtain ⟨et⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2)) (Spec (.of k))
    (-a) (-2)
  exact ⟨(asIso (dualTensorHom _ _)).symm ≪≫ (ed ⊗ᵢ eω) ≪≫ et⟩

local notation3 "𝒪(" a ")" => ProjectiveSpace.twist (ULift (Fin 2)) (Spec (CommRingCat.of k)) a

local notation3 "ω" =>
  Scheme.Hom.relativeDifferentials (ProjectiveLine (Spec (CommRingCat.of k)) ↘
    Spec (CommRingCat.of k))

lemma finiteDimensional_homogeneousSubmodule (d : ℕ) :
    FiniteDimensional k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ d)

lemma finrank_homogeneousSubmodule_zero :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k 0) = 1 := by
  rw [Module.finrank_eq_nat_card_basis (ProjectiveSpace.homogeneousSubmoduleBasis _ k 0)]
  have : Unique {s : ULift.{u} (Fin 2) →₀ ℕ | s.degree = 0} :=
    ⟨⟨⟨0, by simp⟩⟩, fun s ↦ Subtype.ext ((Finsupp.degree_eq_zero_iff _).1 s.2)⟩
  exact Nat.card_unique

lemma finiteDimensional_H_zero_twist (b : ℤ) : FiniteDimensional k ((𝒪(b)).H 0) := by
  rcases lt_or_ge b 0 with hb | hb
  · have := subsingleton_H_zero_twist_of_neg k b hb
    infer_instance
  · rw [← Int.toNat_of_nonneg hb]
    obtain ⟨e⟩ := nonempty_H_zero_twist_equiv k b.toNat
    have := finiteDimensional_homogeneousSubmodule k b.toNat
    exact e.symm.finiteDimensional

lemma finiteDimensional_H_one_twist (a : ℤ) : FiniteDimensional k ((𝒪(a)).H 1) := by
  rcases lt_or_ge a (-1) with ha | ha
  · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
    have := finiteDimensional_homogeneousSubmodule k (-a - 2).toNat
    exact e.symm.finiteDimensional
  · have := subsingleton_H_one_twist k a ha
    infer_instance

/-- `H⁰(ℙ¹_k, Hom(𝒪(a), Ω¹)) ≅ H⁰(ℙ¹_k, 𝒪(-a - 2))`. -/
noncomputable def homObjTwistHZeroLinearEquiv (a : ℤ) :
    H (homObj (𝒪(a)) ω) 0 ≃ₗ[k] (𝒪(-a + -2)).H 0 :=
  ((cohomologyFunctor k 0).mapIso (nonempty_homObj_twist_iso k a).some).toLinearEquiv

/-- **The dimension count for the twists.** `H⁰(ℙ¹_k, Hom(𝒪(a), Ω¹))` and `H¹(ℙ¹_k, 𝒪(a))^∨`
have the same dimension, `max(0, -a - 1)`. -/
lemma finrank_H_zero_homObj_twist (a : ℤ) :
    Module.finrank k (H (homObj (𝒪(a)) ω) 0) = Module.finrank k (Module.Dual k ((𝒪(a)).H 1)) := by
  have := finiteDimensional_H_one_twist k a
  rw [(homObjTwistHZeroLinearEquiv k a).finrank_eq, Subspace.dual_finrank_eq]
  rcases lt_or_ge a (-1) with ha | ha
  · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
    have := finiteDimensional_homogeneousSubmodule k (-a - 2).toNat
    rw [e.finrank_eq, Subspace.dual_finrank_eq]
    have hb : -a + -2 = (((-a - 2).toNat : ℕ) : ℤ) := by omega
    rw [hb]
    obtain ⟨e'⟩ := nonempty_H_zero_twist_equiv k (-a - 2).toNat
    exact e'.finrank_eq
  · have := subsingleton_H_one_twist k a ha
    have := subsingleton_H_zero_twist_of_neg k (-a + -2) (by omega)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- For the twists, surjectivity of the duality pairing implies bijectivity, by the dimension
count `finrank_H_zero_homObj_twist`. -/
lemma bijective_dualPairing_twist_of_surjective (t : Module.Dual k ((ω).H 1)) (a : ℤ)
    (h : Function.Surjective (dualPairing t (𝒪(a)))) :
    Function.Bijective (dualPairing t (𝒪(a))) := by
  rw [← bijective_dualPairingH_iff]
  have hs : Function.Surjective (dualPairingH t (𝒪(a))) := fun y ↦ by
    obtain ⟨φ, rfl⟩ := h y
    exact ⟨(homObjHZeroAddEquiv _ _).symm φ, by rw [dualPairingH_apply, AddEquiv.apply_symm_apply]⟩
  have := finiteDimensional_H_one_twist k a
  have : FiniteDimensional k (H (homObj (𝒪(a)) ω) 0) := by
    have := finiteDimensional_H_zero_twist k (-a + -2)
    exact (homObjTwistHZeroLinearEquiv k a).symm.finiteDimensional
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_H_zero_homObj_twist k a)).2 hs, hs⟩

lemma finrank_dual_H_one_twist_neg_two :
    Module.finrank k (Module.Dual k ((𝒪(-2)).H 1)) = 1 := by
  obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k (-2) le_rfl
  have := finiteDimensional_homogeneousSubmodule k 0
  have := finiteDimensional_H_one_twist k (-2)
  rw [Subspace.dual_finrank_eq, e.finrank_eq, Subspace.dual_finrank_eq]
  exact finrank_homogeneousSubmodule_zero k

/-- `H¹(ℙ¹_k, Ω¹)` is nonzero, so it has a nonzero linear form. -/
lemma exists_dual_H_one_relativeDifferentials_ne_zero :
    ∃ t : Module.Dual k ((ω).H 1), t ≠ 0 := by
  let ι := (nonempty_relativeDifferentials_iso_twist k).some
  let e : (ω).H 1 ≃ₗ[k] (𝒪(-2)).H 1 := ((cohomologyFunctor k 1).mapIso ι).toLinearEquiv
  have := finiteDimensional_H_one_twist k (-2)
  have : FiniteDimensional k ((ω).H 1) := e.symm.finiteDimensional
  have h : Module.finrank k (Module.Dual k ((ω).H 1)) = 1 := by
    rw [Subspace.dual_finrank_eq, e.finrank_eq, ← Subspace.dual_finrank_eq]
    exact finrank_dual_H_one_twist_neg_two k
  have : Nontrivial (Module.Dual k ((ω).H 1)) := Module.nontrivial_of_finrank_eq_succ h
  exact exists_ne 0

/-- The base case `𝒪(-2) ≅ Ω¹` of the duality on the twists: the pairing is nonzero on the
isomorphism `𝒪(-2) ≅ Ω¹`, and `H¹(ℙ¹_k, 𝒪(-2))^∨` is one-dimensional. -/
lemma surjective_dualPairing_twist_neg_two (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) :
    Function.Surjective (dualPairing t (𝒪(-2))) := by
  let ι := (nonempty_relativeDifferentials_iso_twist k).some
  obtain ⟨c, hc⟩ : ∃ c, t c ≠ 0 := by
    by_contra! h
    exact ht (LinearMap.ext h)
  have hne : dualPairingH t (𝒪(-2)) ((homObjHZeroAddEquiv _ _).symm ι.inv) ≠ 0 := by
    rw [dualPairingH_apply, AddEquiv.apply_symm_apply]
    intro h0
    refine hc ?_
    have := LinearMap.congr_fun h0 (H.map ι.hom 1 c)
    rwa [dualPairing_apply, ← H.map_comp_apply, ι.hom_inv_id, H.map_id_apply] at this
  have hd := finrank_dual_H_one_twist_neg_two k
  have := finiteDimensional_H_one_twist k (-2)
  have hr : LinearMap.range (dualPairingH t (𝒪(-2))) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    refine le_antisymm (Submodule.finrank_le _) ?_
    rw [hd, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    have hmem := LinearMap.mem_range_self (dualPairingH t (𝒪(-2)))
      ((homObjHZeroAddEquiv _ _).symm ι.inv)
    exact fun h ↦ hne (by rw [h] at hmem; exact (Submodule.mem_bot k).1 hmem)
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.1 hr y
  exact ⟨_, rfl⟩

/-- **Duality on the projective line for the twists.** For every `a`, the duality pairing
`Hom(𝒪(a), Ω¹) → H¹(ℙ¹_k, 𝒪(a))^∨` is bijective. For `a ≥ -1` both sides vanish. For `a ≤ -2`
we argue by descending induction from `a = -2`: the Koszul sequence
`0 → 𝒪(a) → 𝒪(a + 1)² → 𝒪(a + 2) → 0` and `H⁰(𝒪(a + 2)) = 0` show that `H¹(𝒪(a)) → H¹(𝒪(a + 1)²)`
is injective, which transports surjectivity from `𝒪(a + 1)²` to `𝒪(a)`, and the dimension count
gives bijectivity. -/
theorem bijective_dualPairing_twist (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) (a : ℤ) :
    Function.Bijective (dualPairing t (𝒪(a))) := by
  refine bijective_dualPairing_twist_of_surjective k t a ?_
  rcases le_or_gt (-1) a with ha | ha
  · have := subsingleton_H_one_twist k a ha
    intro y
    refine ⟨0, LinearMap.ext fun z ↦ ?_⟩
    rw [Subsingleton.elim z 0, map_zero, map_zero]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -2 - n := ⟨(-2 - a).toNat, by omega⟩
    clear ha
    induction n with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      exact surjective_dualPairing_twist_neg_two k t ht
    | succ n ih =>
      have hb := bijective_dualPairing_twist_of_surjective k t _ ih
      have e : -2 - ((n + 1 : ℕ) : ℤ) + 1 = -2 - n := by push_cast; ring
      rw [← e] at hb
      set m : ℤ := -2 - ((n + 1 : ℕ) : ℤ)
      have : Subsingleton ((koszul (Spec (.of k)) m).X₃.H 0) := by
        rw [koszul_X₃]
        exact subsingleton_H_zero_twist_of_neg k _ (by simp only [m]; omega)
      exact surjective_dualPairing_of_injective t (koszulLeft (Spec (.of k)) m)
        (H.injective_map_f_one (S := koszul (Spec (.of k)) m) (koszul_shortExact _ m))
        (bijective_dualPairing_biprod t _ _ hb hb).2

/-- **Duality on the projective line for coherent modules.** For a coherent `𝒪_{ℙ¹_k}`-module
`𝒢`, the duality pairing `Hom(𝒢, Ω¹) → H¹(ℙ¹_k, 𝒢)^∨` is bijective. Write `𝒢` as a cokernel of a
map `ℰ₁ ⟶ ℰ₀` of finite sums of twists (`ProjectiveSpace.exists_epi_sigma_twist`, applied twice);
both sides are left exact in `𝒢` (for `H¹(-)^∨` because `H²` vanishes on `ℙ¹_k`), and the
pairing is bijective on `ℰ₀` and `ℰ₁` by `bijective_dualPairing_twist`. -/
theorem bijective_dualPairing_of_isCoherent (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0)
    (G : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) G] :
    Function.Bijective (dualPairing t G) := by
  have hsig (ι : Type u) [Finite ι] (e : ι → ℕ) :=
    bijective_dualPairing_sigma t _ fun j ↦ bijective_dualPairing_twist k t ht (-(e j : ℤ))
  obtain ⟨ι₀, _, e₀, φ₀, hφ₀, hK₀, hK₀'⟩ := ProjectiveSpace.exists_epi_sigma_twist k G
  obtain ⟨ι₁, _, e₁, φ₁, hφ₁, -, -⟩ := ProjectiveSpace.exists_epi_sigma_twist k (kernel φ₀)
  have hS : (ShortComplex.mk (kernel.ι φ₀) φ₀ (kernel.condition φ₀)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ₀))
      inferInstance hφ₀
  have : Subsingleton ((kernel φ₀).H (1 + 1)) := subsingleton_H_of_two_le k (kernel φ₀) le_rfl
  exact bijective_dualPairing_of_epi t φ₀ φ₁ (hsig ι₀ e₀) (hsig ι₁ e₁).1
    (H.surjective_map_g (S := ShortComplex.mk (kernel.ι φ₀) φ₀ (kernel.condition φ₀)) hS 1)

/-- **Duality on the projective line, `H¹`.** For coherent `𝒪_{ℙ¹_k}`-modules `𝒢`, there is an
isomorphism `H¹(ℙ¹_k, 𝒢)^∨ ≅ Hom(𝒢, Ω¹_{ℙ¹_k/k})`, natural in `𝒢`.

The isomorphism is the inverse of the duality pairing `φ ↦ t ∘ H¹(φ)` for a nonzero linear form
`t` on `H¹(ℙ¹_k, Ω¹) ≅ k` (`Scheme.Modules.dualPairingH`). It is bijective on the twists
(`bijective_dualPairing_twist`, by descending induction along the Koszul sequences and a
dimension count), hence on finite sums of twists, hence on every coherent `𝒢` by left exactness
of both sides and a presentation by sums of twists (`bijective_dualPairing_of_isCoherent`).

(blueprint: `thm-sc-p1-duality`, first isomorphism) -/
theorem nonempty_dual_H_one_iso :
    Nonempty ((Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k ≅
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⋙
        Scheme.Modules.cohomologyFunctor k 0) := by
  obtain ⟨t, ht⟩ := exists_dual_H_one_relativeDifferentials_ne_zero k
  let η : (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj ω ⋙
        Scheme.Modules.cohomologyFunctor k 0 ⟶
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k :=
    { app G := ModuleCat.ofHom (dualPairingH t G.unop.obj)
      naturality G G' f := by
        ext x : 2
        refine LinearMap.ext fun z ↦ ?_
        change dualPairing t _ (homObjHZeroAddEquiv _ _ (H.map
            (SheafOfModules.homObjMap (R := (ProjectiveLine (Spec (.of k))).sheaf) f.unop.hom
              (𝟙 _)) 0 x)) z =
          dualPairing t _ (homObjHZeroAddEquiv _ _ x) (H.map f.unop.hom 1 z)
        rw [homObjHZeroAddEquiv_map, dualPairing_comp]
        rfl }
  have (G : (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).FullSubcategoryᵒᵖ) :
      IsIso (η.app G) := by
    have := G.unop.property.1
    have := G.unop.property.2
    have hb := (bijective_dualPairingH_iff t G.unop.obj).2
      (bijective_dualPairing_of_isCoherent k t ht G.unop.obj)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hb
  have := NatIso.isIso_of_isIso_app η
  exact ⟨(asIso η).symm⟩

/-- **Duality on the projective line, `H⁰`.** For a coherent `𝒪_{ℙ¹_k}`-module `𝒢`,
`H⁰(ℙ¹_k, 𝒢)^∨ ≅ Ext¹(𝒢, Ω¹_{ℙ¹_k/k})`.

Choose an epimorphism `ℰ = ⨁ 𝒪(-dⱼ) ⟶ 𝒢` with all `dⱼ ≥ 1`: one from a sum of twists
`𝒪(-eⱼ)`, `eⱼ ≥ 0` (`ProjectiveSpace.exists_epi_sigma_twist`), precomposed with the Koszul
surjections `𝒪(-eⱼ - 1)² ⟶ 𝒪(-eⱼ)`. Its kernel `𝒦` is coherent, `H⁰(ℰ) = 0`, and
`Ext¹(𝒪(-d), ω) ≅ H¹(ℙ¹_k, 𝒪(d) ⊗ ω) = H¹(ℙ¹_k, 𝒪(d - 2)) = 0` for `d ≥ 1`
(`Scheme.Modules.nonempty_ext_addEquiv_H`). The `H¹`-duality on `𝒦` and `ℰ`
(`bijective_dualPairing_of_isCoherent`) then gives the `H⁰`-duality on `𝒢`
(`Scheme.Modules.nonempty_dual_H_zero_addEquiv_ext_of_shortExact`).

(blueprint: `thm-sc-p1-duality`, second isomorphism) -/
theorem nonempty_dual_H_zero_addEquiv_ext [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    Nonempty (Module.Dual k (𝒢.H 0) ≃+
      Scheme.Modules.Ext 𝒢 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials
        1) := by
  obtain ⟨t, ht⟩ := exists_dual_H_one_relativeDifferentials_ne_zero k
  obtain ⟨ι, _, e, φ₀, hφ₀, -, -⟩ := ProjectiveSpace.exists_epi_sigma_twist k 𝒢
  -- `ℰ = ⨁_{j, i} 𝒪(-eⱼ - 1)`, mapping onto `⨁ⱼ 𝒪(-eⱼ)` by the Koszul maps `xᵢ`
  let m : ι → ℤ := fun j ↦ -(e j : ℤ) - 2
  have hm (j : ι) : 𝒪(m j + 1 + 1) = 𝒪(-(e j : ℤ)) := by
    congr 1
    simp only [m]
    omega
  let E := ∐ fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)
  let ψ : E ⟶ ∐ fun j ↦ 𝒪(-(e j : ℤ)) := Sigma.desc fun p ↦
    mulX (Spec (.of k)) (m p.1 + 1) p.2.down ≫ eqToHom (hm p.1) ≫
      Sigma.ι (fun j ↦ 𝒪(-(e j : ℤ))) p.1
  have hψ : Epi ψ := by
    refine ⟨fun {Z} g h hgh ↦ Sigma.hom_ext _ _ fun j ↦ ?_⟩
    have : Epi (koszulRight (Spec (.of k)) (m j)) :=
      (koszul_shortExact (Spec (.of k)) (m j)).epi_g
    rw [← cancel_epi (koszulRight (Spec (.of k)) (m j) ≫ eqToHom (hm j))]
    simp only [Category.assoc]
    refine biprod.hom_ext' _ _ ?_ ?_
    · have h₀ := Sigma.ι (fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)) (j, ULift.up 0) ≫= hgh
      simpa [koszulRight, ψ, E] using h₀
    · have h₁ := Sigma.ι (fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)) (j, ULift.up 1) ≫= hgh
      simpa [koszulRight, ψ, E] using h₁
  let S := ShortComplex.mk (kernel.ι (ψ ≫ φ₀)) (ψ ≫ φ₀) (kernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      inferInstance (epi_comp ψ φ₀)
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_sigma fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)
  have := isFinitePresentation_sigma fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)
  have : SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf)
      S.X₁ := isQuasicoherent_kernel _
  have : SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf)
      S.X₁ := isFinitePresentation_kernel _
  have : ∀ p : ι × ULift.{u} (Fin 2), Subsingleton ((𝒪(m p.1 + 1)).H 0) := fun p ↦
    subsingleton_H_zero_twist_of_neg k _ (by simp only [m]; omega)
  have : Subsingleton (S.X₂.H 0) := subsingleton_H_sigma _ 0
  have (p : ι × ULift.{u} (Fin 2)) : Subsingleton (Ext (𝒪(m p.1 + 1)) ω 1) := by
    obtain ⟨eE⟩ := nonempty_ext_addEquiv_H (𝒪(m p.1 + 1)) ω 1
    obtain ⟨eω⟩ := nonempty_relativeDifferentials_iso_twist k
    have : (ω).IsInvertible := IsInvertible.of_iso eω.symm
    let i := asIso (dualTensorHom (𝒪(m p.1 + 1)) ω) ≪≫
      (nonempty_homObj_twist_iso k (m p.1 + 1)).some
    have := subsingleton_H_one_twist k (-(m p.1 + 1) + -2) (by simp only [m]; omega)
    have : Subsingleton (((𝒪(m p.1 + 1))ᵛ ⊗ ω).H 1) :=
      (H.mapLinearEquiv i 1).toEquiv.subsingleton
    exact eE.toEquiv.subsingleton
  have : Subsingleton (Ext S.X₂ ω 1) := Abelian.Ext.subsingleton_sigma _ ω 1
  exact nonempty_dual_H_zero_addEquiv_ext_of_shortExact t hS
    (bijective_dualPairing_of_isCoherent k t ht S.X₁)
    (bijective_dualPairing_sigma t _ fun p ↦ bijective_dualPairing_twist k t ht _).2

end ProjectiveLine

end AlgebraicGeometry
