/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.TorsionFree
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Universal coefficient sequences

Let `R` be a commutative ring and `x ∈ R`. For a distinguished triangle
`C ⟶[x] C ⟶ D ⟶ C⟦1⟧` of `D(R)` whose first map is the multiplication by `x` (for example
`D = C ⊗ᴸ R/(x)` when `x` is a nonzerodivisor), the long exact homology sequence breaks up into
the *universal coefficient sequences*

`0 ⟶ Hⁱ(C) ⊗_R R/(x) ⟶ Hⁱ(D) ⟶ Hⁱ⁺¹(C)[x] ⟶ 0`,

where `M[x]` is the `x`-torsion of `M`; for a nonzerodivisor `x` it is `Tor₁^R(M, R/(x))`.

## Main definitions

- `ModuleCat.universalCoefficientShortComplex`: the short complex
  `A ⊗ R/(x) ⟶ B ⟶ A'[x]` attached to maps `A ⟶ B ⟶ A'` with `A ⟶[x] A ⟶ B` and
  `B ⟶ A' ⟶[x] A'` zero.
- `DerivedCategory.universalCoefficientSequence`: the universal coefficient sequence of a
  triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧`.

## Main statements

- `ModuleCat.universalCoefficientShortComplex_shortExact`: the short complex is short exact
  when `A ⟶[x] A ⟶ B ⟶ A' ⟶[x] A'` is exact.
- `DerivedCategory.universalCoefficientSequence_shortExact`: the universal coefficient sequence
  of a distinguished triangle is short exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R] (x : R)

section

variable {A B A' : ModuleCat.{u} R} (f : A ⟶ B) (g : B ⟶ A')

lemma smul_span_singleton_top_le_ker (hf : (x • 𝟙 A) ≫ f = 0) :
    Ideal.span {x} • (⊤ : Submodule R A) ≤ LinearMap.ker f.hom := by
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨a, -, rfl⟩
  have := congr($(hf).hom a)
  exact this

lemma smul_apply_eq_zero (hg : g ≫ (x • 𝟙 A') = 0) (b : B) : x • g.hom b = 0 := by
  have := congr($(hg).hom b)
  exact this

/-- The map `A ⊗_R R/(x) ⟶ B` induced by `f : A ⟶ B` when `f ∘ x = 0`. -/
noncomputable def tensorQuotLift (hf : (x • 𝟙 A) ≫ f = 0) :
    A ⊗[R] (R ⧸ Ideal.span {x}) →ₗ[R] B :=
  (Submodule.liftQ _ f.hom (smul_span_singleton_top_le_ker x f hf)) ∘ₗ
    (TensorProduct.tensorQuotEquivQuotSMul A (Ideal.span {x})).toLinearMap

@[simp]
lemma tensorQuotLift_tmul (hf : (x • 𝟙 A) ≫ f = 0) (a : A) :
    tensorQuotLift x f hf (a ⊗ₜ 1) = f.hom a := by
  simp [tensorQuotLift, TensorProduct.tensorQuotEquivQuotSMul]

lemma range_tensorQuotLift (hf : (x • 𝟙 A) ≫ f = 0) :
    LinearMap.range (tensorQuotLift x f hf) = LinearMap.range f.hom := by
  rw [tensorQuotLift, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_liftQ]

/-- The universal coefficient short complex `A ⊗_R R/(x) ⟶ B ⟶ A'[x]` attached to maps
`f : A ⟶ B` and `g : B ⟶ A'` with `f g = 0`, `f ∘ x = 0` and `x ∘ g = 0`: the first map is
induced by `f`, the second is `g`, which lands in the `x`-torsion of `A'`. -/
noncomputable def universalCoefficientShortComplex (hf : (x • 𝟙 A) ≫ f = 0) (hfg : f ≫ g = 0)
    (hg : g ≫ (x • 𝟙 A') = 0) : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R (A ⊗[R] (R ⧸ Ideal.span {x}))
  X₂ := B
  X₃ := ModuleCat.of R (Submodule.torsionBy R A' x)
  f := ofHom (tensorQuotLift x f hf)
  g := ofHom (g.hom.codRestrict _ fun b ↦
    (Submodule.mem_torsionBy_iff _ _).2 (smul_apply_eq_zero x g hg b))
  zero := by
    refine hom_ext (TensorProduct.ext' fun a r ↦ ?_)
    induction r using Submodule.Quotient.induction_on with | H r => ?_
    have h₁ : a ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {x}) r) = (r • a) ⊗ₜ 1 := by
      rw [TensorProduct.smul_tmul]
      congr 1
      exact Algebra.algebraMap_eq_smul_one (A := R ⧸ Ideal.span {x}) r
    have h₂ := congr($(hfg).hom a)
    apply Subtype.ext
    simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply, hom_zero,
      LinearMap.zero_apply] at h₂ ⊢
    simp [h₁, tensorQuotLift_tmul, h₂]

/-- The universal coefficient short complex is short exact as soon as the sequence
`A ⟶[x] A ⟶ B ⟶ A' ⟶[x] A'` is exact. -/
theorem universalCoefficientShortComplex_shortExact (hf : (x • 𝟙 A) ≫ f = 0)
    (hfg : f ≫ g = 0) (hg : g ≫ (x • 𝟙 A') = 0) {a : A ⟶ A} (ha : a = x • 𝟙 A)
    {a' : A' ⟶ A'} (ha' : a' = x • 𝟙 A') {haf : a ≫ f = 0} {hga : g ≫ a' = 0}
    (h₁ : (ShortComplex.mk _ _ haf).Exact) (h₂ : (ShortComplex.mk _ _ hfg).Exact)
    (h₃ : (ShortComplex.mk _ _ hga).Exact) :
    (universalCoefficientShortComplex x f g hf hfg hg).ShortExact := by
  subst ha ha'
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h₁ h₂ h₃
  refine ModuleCat.shortComplex_shortExact _ (fun b ↦ ?_) ?_ ?_
  · change g.hom.codRestrict _ _ b = 0 ↔ b ∈ Set.range (tensorQuotLift x f hf)
    rw [← LinearMap.mem_ker, LinearMap.ker_codRestrict, LinearMap.mem_ker]
    erw [h₂ b]
    rw [← LinearMap.coe_range, ← LinearMap.coe_range, range_tensorQuotLift]
  · have hker : LinearMap.ker f.hom ≤ Ideal.span {x} • ⊤ := by
      intro a ha
      obtain ⟨a₀, rfl⟩ := (h₁ a).1 ha
      rw [Submodule.ideal_span_singleton_smul]
      exact ⟨a₀, trivial, by simp⟩
    exact (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ f.hom
      (smul_span_singleton_top_le_ker x f hf) hker)).comp
      (LinearEquiv.injective _)
  · rintro ⟨a', ha'⟩
    obtain ⟨b, hb⟩ := (h₃ a').1 ((Submodule.mem_torsionBy_iff _ _).1 ha')
    exact ⟨b, Subtype.ext hb⟩

end


section Tor

open MonoidalCategory ZeroObject

/-- The terms of the projective resolution `0 ⟶ R ⟶[x] R` of `R/(x)`. -/
noncomputable def quotSpanSingletonResolutionX : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | 1 => ModuleCat.of R R
  | _ + 2 => 0

/-- The differentials of the projective resolution `0 ⟶ R ⟶[x] R` of `R/(x)`. -/
noncomputable def quotSpanSingletonResolutionD :
    ∀ n, quotSpanSingletonResolutionX (R := R) (n + 1) ⟶ quotSpanSingletonResolutionX n
  | 0 => ofHom (x • LinearMap.id : R →ₗ[R] R)
  | _ + 1 => 0

/-- The complex `0 ⟶ R ⟶[x] R`, concentrated in degrees `1` and `0`. -/
noncomputable def quotSpanSingletonResolutionComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of _ (quotSpanSingletonResolutionD x) fun n ↦ by
    simp [quotSpanSingletonResolutionD]

lemma isZero_quotSpanSingletonResolutionComplex_X (n : ℕ) :
    IsZero ((quotSpanSingletonResolutionComplex x).X (n + 2)) :=
  isZero_zero (ModuleCat.{u} R)

instance (n : ℕ) : Projective ((quotSpanSingletonResolutionComplex x).X n) := by
  match n with
  | 0 => exact inferInstanceAs (Projective (ModuleCat.of R R))
  | 1 => exact inferInstanceAs (Projective (ModuleCat.of R R))
  | n + 2 => exact (isZero_quotSpanSingletonResolutionComplex_X x n).projective

variable {x}

variable [Small.{u} R]

end Tor

end ModuleCat

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] (x : R)

lemma homologyFunctor_map_smul_id (C : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) n).map (x • 𝟙 C) = x • 𝟙 _ := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

variable {x} {C D : DerivedCategory (ModuleCat.{u} R)} {g : C ⟶ D} {h : D ⟶ C⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (x • 𝟙 C) g h ∈ distTriang _) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)

include hT in
lemma universalCoefficientSequence_hf :
    (x • 𝟙 _) ≫ (homologyFunctor (ModuleCat.{u} R) n₀).map g = 0 := by
  have h₀ : (x • 𝟙 C) ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [← homologyFunctor_map_smul_id, ← Functor.map_comp, h₀, Functor.map_zero]

include hT in
lemma universalCoefficientSequence_hg :
    HomologySequence.δ (Triangle.mk (x • 𝟙 C) g h) n₀ n₁ hn ≫ (x • 𝟙 _) = 0 := by
  rw [← homologyFunctor_map_smul_id]
  exact HomologySequence.δ_comp _ hT n₀ n₁ hn

/-- Blueprint `prop-pod-integral-degreewise-form` (the universal coefficient sequence): for a
distinguished triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧` of `D(R)` whose first map is the multiplication
by `x`, the short complex

`Hⁿ(C) ⊗_R R/(x) ⟶ Hⁿ(D) ⟶ Hⁿ⁺¹(C)[x]`

of the long exact homology sequence, for `n₁ = n₀ + 1`. -/
noncomputable def universalCoefficientSequence : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.universalCoefficientShortComplex x ((homologyFunctor (ModuleCat.{u} R) n₀).map g)
    (HomologySequence.δ (Triangle.mk (x • 𝟙 C) g h) n₀ n₁ hn)
    (universalCoefficientSequence_hf hT n₀) (HomologySequence.comp_δ _ hT n₀ n₁ hn)
    (universalCoefficientSequence_hg hT n₀ n₁ hn)

/-- Blueprint `prop-pod-integral-degreewise-form` (the universal coefficient sequence): the
universal coefficient sequence `0 ⟶ Hⁿ(C) ⊗_R R/(x) ⟶ Hⁿ(D) ⟶ Hⁿ⁺¹(C)[x] ⟶ 0` of a
distinguished triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧` is short exact. -/
theorem universalCoefficientSequence_shortExact :
    (universalCoefficientSequence hT n₀ n₁ hn).ShortExact :=
  ModuleCat.universalCoefficientShortComplex_shortExact _ _ _ _ _ _
    (homologyFunctor_map_smul_id x C n₀) (homologyFunctor_map_smul_id x C n₁)
    (HomologySequence.exact₂ _ hT n₀) (HomologySequence.exact₃ _ hT n₀ n₁ hn)
    (HomologySequence.exact₁ _ hT n₀ n₁ hn)

end DerivedCategory

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C) {A₁ A₂ A₃ : C}
  (e₁ : S.X₁ ≅ A₁) (e₂ : S.X₂ ≅ A₂) (e₃ : S.X₃ ≅ A₃)

/-- The short complex `A₁ ⟶ A₂ ⟶ A₃` obtained from `S` by transport along isomorphisms
`S.Xᵢ ≅ Aᵢ` of its objects. -/
@[simps]
def transport : ShortComplex C where
  X₁ := A₁
  X₂ := A₂
  X₃ := A₃
  f := e₁.inv ≫ S.f ≫ e₂.hom
  g := e₂.inv ≫ S.g ≫ e₃.hom
  zero := by simp

/-- A short complex is isomorphic to its transport along isomorphisms of its objects. -/
@[simps!]
def transportIso : S ≅ S.transport e₁ e₂ e₃ :=
  isoMk e₁ e₂ e₃ (by simp) (by simp)

variable {S} in
lemma ShortExact.transport (h : S.ShortExact) : (S.transport e₁ e₂ e₃).ShortExact :=
  shortExact_of_iso (S.transportIso e₁ e₂ e₃) h

end CategoryTheory.ShortComplex
