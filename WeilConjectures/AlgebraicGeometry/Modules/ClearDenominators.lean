/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Clearing denominators for a section of an invertible module

Let `X` be a quasi-compact scheme, separated over an affine scheme, `ℒ` an invertible
`𝒪_X`-module and `s` a global section of `ℒ`, i.e. a morphism `s : 𝒪_X ⟶ ℒ`. Let `X_s` be the
complement of the zero scheme `Z(s)`. Every section `t` of a quasi-coherent module `ℱ` over
`X_s` becomes, after multiplication by a power of `s`, the restriction of a global section:
there are `m` and `u ∈ Γ(X, ℱ ⊗ ℒ^{⊗ m})` with `u|_{X_s} = t ⊗ s^m`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.tensorPowSection`: the power `s^{⊗ m} : 𝒪_X ⟶ ℒ^{⊗ m}` of
  a global section `s : 𝒪_X ⟶ ℒ`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_tensorPowSection_eq_restrict`: clearing denominators
  (blueprint `lem-pc-section-clearing-denominators`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The `m`-th power `s^{⊗ m} : 𝒪_X ⟶ ℒ^{⊗ m}` of a global section `s : 𝒪_X ⟶ ℒ`:
`s^{⊗ 0} = 𝟙` and `s^{⊗ (m + 1)} = s ⊗ s^{⊗ m}`, precomposed with `𝒪_X ≅ 𝒪_X ⊗ 𝒪_X`. -/
noncomputable def tensorPowSection {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) :
    (m : ℕ) → (𝟙_ X.Modules ⟶ L.tensorPow m)
  | 0 => 𝟙 _
  | m + 1 => (λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ tensorPowSection s m)

@[simp]
lemma tensorPowSection_zero {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) :
    tensorPowSection s 0 = 𝟙 _ :=
  rfl

lemma tensorPowSection_succ {L : X.Modules} (s : 𝟙_ X.Modules ⟶ L) (m : ℕ) :
    tensorPowSection s (m + 1) = (λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ tensorPowSection s m) :=
  rfl

/-- **Clearing denominators for a section of an invertible module.** Let `X` be a quasi-compact
scheme, separated over an affine scheme `S`, let `ℒ` be an invertible `𝒪_X`-module and
`s : 𝒪_X ⟶ ℒ` a global section of `ℒ`, and let `X_s` be the complement of the zero scheme
`Z(s)`. For every quasi-coherent `𝒪_X`-module `ℱ` and every `t ∈ Γ(X_s, ℱ)` there are `m ≥ 0`
and `u ∈ Γ(X, ℱ ⊗ ℒ^{⊗ m})` with `u|_{X_s} = t ⊗ s^m`.

Here `t ⊗ s^m` is the image of `t` under `ℱ ≅ ℱ ⊗ 𝒪_X ⟶ ℱ ⊗ ℒ^{⊗ m}`, the second map being
`ℱ ◁ s^{⊗ m}`.

On a finite affine cover `Vⱼ` of `X` on which `ℒ` has a basis `eⱼ`, with `s = fⱼ eⱼ`, one has
`X_s ∩ Vⱼ = D(fⱼ)`, so `fⱼ^a t` lifts to `tⱼ ∈ Γ(Vⱼ, ℱ)` for one `a`. The sections
`tⱼ ⊗ eⱼ^a` agree on `X_s ∩ Vⱼ ∩ Vₖ`; the overlaps `Vⱼ ∩ Vₖ` being affine, a further power
`s^b` makes them agree on the whole overlaps, and they glue to `u` with `m = a + b`.

(blueprint: `lem-pc-section-clearing-denominators`) -/
@[stacks 01PW]
theorem exists_tensorPowSection_eq_restrict {S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsAffine S] [CompactSpace X] (L : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} L]
    (s : 𝟙_ X.Modules ⟶ L) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    (t : Γ(F, (Hom.zeroLocus s).support.compl)) :
    ∃ (m : ℕ) (u : Γ(F ⊗ L.tensorPow m, ⊤)),
      (F ⊗ L.tensorPow m).presheaf.map (homOfLE le_top).op u =
        ((ρ_ F).inv ≫ F ◁ tensorPowSection s m).app _ t :=
  sorry

end AlgebraicGeometry.Scheme.Modules
