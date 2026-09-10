/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import WeilConjectures.AlgebraicGeometry.Cohomology.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The long exact cohomology sequence of a short exact sequence of sheaves of modules

Let `X` be a scheme and let `0 ⟶ M' ⟶ M ⟶ M'' ⟶ 0` be a short exact sequence of
`𝒪_X`-modules, encoded as a short complex `S : ShortComplex X.Modules` together with
`hS : S.ShortExact`. This file constructs the connecting homomorphism
`H^{n₀}(X, M'') ⟶ H^{n₁}(X, M')` (for `n₀ + 1 = n₁`) and proves that the resulting sequence

`⋯ ⟶ H^n(X, M') ⟶ H^n(X, M) ⟶ H^n(X, M'') ⟶ H^{n+1}(X, M') ⟶ ⋯`

is exact. The connecting homomorphism is `Γ(X, 𝒪_X)`-linear, and is natural in the short
exact sequence.

The cohomology `Scheme.Modules.H` is defined in `WeilConjectures.AlgebraicGeometry.Cohomology.Basic`
as an `Ext`-group in the category of abelian sheaves on `X`, so everything here is deduced
from Mathlib's long exact sequences for `Ext`, once we know that the forgetful functor
`Scheme.Modules.toSheafAb` from `𝒪_X`-modules to abelian sheaves is exact.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.H.δ` — the connecting homomorphism
  `H^{n₀}(X, S.X₃) →ₗ[Γ(X, 𝒪_X)] H^{n₁}(X, S.X₁)`.

## Main results

- `CategoryTheory.ShortComplex.ShortExact.map_toSheafAb` — a short exact sequence of
  `𝒪_X`-modules stays short exact after forgetting the module structures.
- `AlgebraicGeometry.Scheme.Modules.H.exact₁`, `H.exact₂`, `H.exact₃` — the exactness of the
  long exact sequence at its three kinds of spot, and `H.injective_map_f` for its left end.
- `AlgebraicGeometry.Scheme.Modules.H.δ_naturality` — naturality of the connecting
  homomorphism in the short exact sequence, and `H.δ_smul_over` for its `R`-linearity when
  `X` is a scheme over `Spec R`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-! ### Exactness of the forgetful functor to abelian sheaves -/

noncomputable instance toSheafAb_preservesFiniteLimits :
    PreservesFiniteLimits (toSheafAb X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))

instance toSheafAb_preservesEpimorphisms : (toSheafAb X).PreservesEpimorphisms :=
  inferInstanceAs ((SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms)

/-- The forgetful functor from `𝒪_X`-modules to sheaves of abelian groups sends short exact
sequences to short exact sequences. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.map_toSheafAb
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toSheafAb X)).ShortExact :=
  ShortComplex.ShortExact.map_toSheaf (R := X.ringCatSheaf) hS

variable {S S₁ S₂ : ShortComplex X.Modules}

lemma H.mapAddHom_apply_eq_comp (φ : M ⟶ N) (n : ℕ) (x : M.H n) :
    H.mapAddHom φ n x = x.comp (Ext.mk₀ ((toSheafAb X).map φ)) (add_zero n) :=
  rfl

/-! ### Multiplication by a global section as an endomorphism of a short complex -/

variable (S) in
/-- Multiplication by a global section `r` of `𝒪_X`, as an endomorphism of a short complex
of `𝒪_X`-modules. -/
@[simps]
noncomputable def smulShortComplex (r : Γ(X, ⊤)) : S ⟶ S where
  τ₁ := smulEnd S.X₁ r
  τ₂ := smulEnd S.X₂ r
  τ₃ := smulEnd S.X₃ r
  comm₁₂ := smulEnd_comp S.f r
  comm₂₃ := smulEnd_comp S.g r

/-! ### The connecting homomorphism -/

/-- The connecting homomorphism `H^{n₀}(X, S.X₃) →+ H^{n₁}(X, S.X₁)` of a short exact sequence
`S` of `𝒪_X`-modules. See `AlgebraicGeometry.Scheme.Modules.H.δ` for its `Γ(X, 𝒪_X)`-linear
refinement. -/
noncomputable def H.δAddHom (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.X₃.H n₀ →+ S.X₁.H n₁ :=
  hS.map_toSheafAb.extClass.postcomp _ h

lemma H.δAddHom_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : S.X₃.H n₀) :
    H.δAddHom hS n₀ n₁ h x = x.comp hS.map_toSheafAb.extClass h :=
  rfl

/-- The connecting homomorphism is natural in the short exact sequence. -/
lemma H.δAddHom_naturality (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : S₁.X₃.H n₀) :
    H.δAddHom h₂ n₀ n₁ h (H.mapAddHom φ.τ₃ n₀ x) =
      H.mapAddHom φ.τ₁ n₁ (H.δAddHom h₁ n₀ n₁ h x) := by
  have hnat := ShortComplex.ShortExact.extClass_naturality h₁.map_toSheafAb h₂.map_toSheafAb
    ((toSheafAb X).mapShortComplex.map φ)
  simp only [Functor.mapShortComplex_map_τ₁, Functor.mapShortComplex_map_τ₃] at hnat
  rw [H.mapAddHom_apply_eq_comp, H.mapAddHom_apply_eq_comp, H.δAddHom_apply, H.δAddHom_apply,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, ← hnat]

/-- The connecting homomorphism `H^{n₀}(X, S.X₃) → H^{n₁}(X, S.X₁)` of a short exact sequence
`S` of `𝒪_X`-modules, as a `Γ(X, 𝒪_X)`-linear map. -/
noncomputable def H.δ (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.X₃.H n₀ →ₗ[Γ(X, ⊤)] S.X₁.H n₁ where
  toFun := H.δAddHom hS n₀ n₁ h
  map_add' := AddMonoidHom.map_add _
  map_smul' r x := by
    simpa only [RingHom.id_apply, H.smul_def, smulShortComplex_τ₁, smulShortComplex_τ₃] using
      H.δAddHom_naturality hS hS (smulShortComplex S r) n₀ n₁ h x

@[simp]
lemma H.δ_apply (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : S.X₃.H n₀) :
    H.δ hS n₀ n₁ h x = x.comp hS.map_toSheafAb.extClass h :=
  rfl

/-- The connecting homomorphism is natural in the short exact sequence. -/
lemma H.δ_naturality (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : S₁.X₃.H n₀) :
    H.δ h₂ n₀ n₁ h (H.map φ.τ₃ n₀ x) = H.map φ.τ₁ n₁ (H.δ h₁ n₀ n₁ h x) :=
  H.δAddHom_naturality h₁ h₂ φ n₀ n₁ h x

/-! ### Exactness of the long exact sequence -/

/-- Exactness of the long exact cohomology sequence at `H^n(X, S.X₂)`. -/
lemma H.exact₂ (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (H.map S.f n) (H.map S.g n) := by
  intro x
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₂ _ hS.map_toSheafAb x hx
  · rintro ⟨y, rfl⟩
    rw [← LinearMap.comp_apply, ← H.map_comp, S.zero, H.map_zero, LinearMap.zero_apply]

/-- Exactness of the long exact cohomology sequence at `H^{n₀}(X, S.X₃)`. -/
lemma H.exact₃ (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (H.map S.g n₀) (H.δ hS n₀ n₁ h) := by
  intro x
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₃ _ hS.map_toSheafAb x h hx
  · rintro ⟨y, rfl⟩
    have hz : (Ext.mk₀ ((toSheafAb X).map S.g)).comp hS.map_toSheafAb.extClass (zero_add 1) = 0 :=
      hS.map_toSheafAb.comp_extClass
    rw [H.δ_apply, H.map_apply, H.mapAddHom_apply_eq_comp, Ext.comp_assoc_of_second_deg_zero, hz,
      Ext.comp_zero]

/-- Exactness of the long exact cohomology sequence at `H^{n₁}(X, S.X₁)`. -/
lemma H.exact₁ (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    Function.Exact (H.δ hS n₀ n₁ h) (H.map S.f n₁) := by
  intro x
  constructor
  · intro hx
    exact Ext.covariant_sequence_exact₁ _ hS.map_toSheafAb x hx h
  · rintro ⟨y, rfl⟩
    have hz : hS.map_toSheafAb.extClass.comp (Ext.mk₀ ((toSheafAb X).map S.f)) (add_zero 1) = 0 :=
      hS.map_toSheafAb.extClass_comp
    rw [H.map_apply, H.mapAddHom_apply_eq_comp, H.δ_apply, Ext.comp_assoc_of_third_deg_zero, hz,
      Ext.comp_zero]

/-- The long exact cohomology sequence starts with an injection `H^0(X, S.X₁) → H^0(X, S.X₂)`. -/
lemma H.injective_map_f (hS : S.ShortExact) : Function.Injective (H.map S.f 0) := by
  have hf : Mono ((toSheafAb X).map S.f) := hS.map_toSheafAb.mono_f
  intro a b hab
  exact Ext.postcomp_mk₀_injective_of_mono _ ((toSheafAb X).map S.f) hab

/-! ### Schemes over a base ring -/

section OverBase

variable (R : Type u) [CommRing R] [X.Over (Spec (.of R))]

/-- If `X` is a scheme over `Spec R`, the connecting homomorphism is `R`-linear; for `R` a
field, this is the linearity used to compute Euler characteristics. -/
lemma H.δ_smul_over (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (r : R)
    (x : S.X₃.H n₀) :
    H.δ hS n₀ n₁ h (r • x) = r • H.δ hS n₀ n₁ h x := by
  rw [H.smul_over_def R X, H.smul_over_def R X, LinearMap.map_smul]

end OverBase

end AlgebraicGeometry.Scheme.Modules
