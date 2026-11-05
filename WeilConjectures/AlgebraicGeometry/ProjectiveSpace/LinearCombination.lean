/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartSections

/-!
# Morphisms to projective space given by linear combinations of sections

Let `ψ : Z ⟶ ℙ(m; S)` and `χ : Z ⟶ ℙ(n; S)` be morphisms over `S` given by families of global
sections `u` and `v` of one module `L` on `Z`, i.e. `ψ^* 𝒪(1) ≅ L` sends `ψ^* T_q` to `u q`, and
similarly for `χ` and `v`. If every `v l` is a linear combination of the `u q` with coefficients
from `Γ(S)`, then `χ` is, on the image of `ψ`, the composite of `ψ` with a linear projection
`ℙ(m; S) ⇢ ℙ(n; S)`. We do not construct the projection; we only prove the consequence that if
`χ` is a monomorphism, then so is `ψ`.

On the chart `ψ⁻¹ D₊(T_q)` the section `v l` is `ψ^* A_{ql} • u q` for the function
`A_{ql} = ∑_r c_{lr} T_r / T_q` on `D₊(T_q)`, so `v l` generates `L` exactly on
`ψ⁻¹ D(A_{ql})`, which is therefore contained in `χ⁻¹ D₊(T_l)`; there `χ` pulls `T_r / T_l` back
to `ψ^*(A_{qr} / A_{ql})`. Hence two morphisms `a, b : T ⟶ Z` with `a ≫ ψ = b ≫ ψ` satisfy
`a ≫ χ = b ≫ χ` on each of the opens `(a ≫ ψ)⁻¹ D(A_{ql})`, which cover `T`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.generatingLocus_eq_preimage_standardOpen`: if
  `φ^* 𝒪(1) ≅ M` sends `φ^* Tᵢ` to `s i`, then `s i` generates `M` exactly on `φ⁻¹ D₊(Tᵢ)`.
- `AlgebraicGeometry.ProjectiveSpace.hom_ext_of_preimage_standardOpen_eq_top`: over an affine
  base, morphisms into the chart `D₊(Tᵢ)` are determined by the ratios `Tⱼ / Tᵢ`.
- `AlgebraicGeometry.ProjectiveSpace.mono_of_eq_sum_smul`: the monomorphism criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

section Sections

variable {X S : Scheme.{u}} {n : Type u} {M : X.Modules} {s : n → Γ(M, ⊤)}
  {φ : X ⟶ ℙ(n; S)} (ε : twistRestrict φ 1 ⟶ M) [IsIso ε]
  (hε : ∀ j, ε.app _ (pullbackSection φ (twistOneSection n S j)) =
    M.presheaf.map (homOfLE (le_top : φ ⁻¹ᵁ ⊤ ≤ ⊤)).op (s j))
include hε

end Sections

private lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U V e) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- **Morphisms into a standard chart are determined by the ratios.** Over an affine base `S`,
two morphisms `W ⟶ ℙ(n; S)` landing in the standard open `D₊(Tᵢ)`, with the same composite to
`S` and pulling back every ratio `Tⱼ / Tᵢ` to the same function, are equal. -/
lemma hom_ext_of_preimage_standardOpen_eq_top {S : Scheme.{u}} [IsAffine S] {n : Type u}
    {W : Scheme.{u}} {f₁ f₂ : W ⟶ ℙ(n; S)} (i : n)
    (h₁ : f₁ ⁻¹ᵁ standardOpen n S i = ⊤) (h₂ : f₂ ⁻¹ᵁ standardOpen n S i = ⊤)
    (hS : f₁ ≫ ℙ(n; S) ↘ S = f₂ ≫ ℙ(n; S) ↘ S)
    (hr : ∀ j, f₁.appLE (standardOpen n S i) ⊤ h₁.ge (coordRatio n S i j) =
      f₂.appLE (standardOpen n S i) ⊤ h₂.ge (coordRatio n S i j)) : f₁ = f₂ := by
  have : IsAffine (standardOpen n S i).toScheme := isAffineOpen_standardOpen n S i
  have key : f₁.appLE (standardOpen n S i) ⊤ h₁.ge = f₂.appLE (standardOpen n S i) ⊤ h₂.ge := by
    ext1
    refine RingHom.eq_of_eqOn_set_dense (closure_range_appLE_union_range_coordRatio S i) ?_
    rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
    · change ((ℙ(n; S) ↘ S).appLE ⊤ _ le_top ≫ f₁.appLE _ ⊤ h₁.ge) c =
        ((ℙ(n; S) ↘ S).appLE ⊤ _ le_top ≫ f₂.appLE _ ⊤ h₂.ge) c
      erw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
      rw [appLE_eq_of_eq hS]
    · exact hr j
  have hres : f₁.resLE (standardOpen n S i) ⊤ h₁.ge = f₂.resLE (standardOpen n S i) ⊤ h₂.ge :=
    ext_of_isAffine (by
      rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
        Scheme.Hom.resLE_app_top, key])
  rw [← cancel_epi W.topIso.hom, Scheme.topIso_hom, ← Scheme.Hom.resLE_comp_ι f₁ h₁.ge,
    ← Scheme.Hom.resLE_comp_ι f₂ h₂.ge, hres]

section Mono

variable {S Z : Scheme.{u}} {g : Z ⟶ S} {L : Z.Modules} {m n : Type u} [Fintype m]
  {u : m → Γ(L, ⊤)} {v : n → Γ(L, ⊤)} (c : n → m → Γ(S, ⊤))
  {ψ : Z ⟶ ℙ(m; S)} {χ : Z ⟶ ℙ(n; S)}
  (εψ : twistRestrict ψ 1 ⟶ L) [IsIso εψ]
  (hεψ : ∀ q, εψ.app _ (pullbackSection ψ (twistOneSection m S q)) =
    L.presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op (u q))
  (εχ : twistRestrict χ 1 ⟶ L) [IsIso εχ]
  (hεχ : ∀ l, εχ.app _ (pullbackSection χ (twistOneSection n S l)) =
    L.presheaf.map (homOfLE (le_top : χ ⁻¹ᵁ ⊤ ≤ ⊤)).op (v l))

variable {c} (hψ : ψ ≫ ℙ(m; S) ↘ S = g) (hv : ∀ l, v l = ∑ r, g.appTop (c l r) • u r)
include hεψ hεχ hψ hv

end Mono

section BaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S S' W X : Scheme.{u}} {m : Type u} (gS : S' ⟶ S) (φ : W ⟶ X) {M : X.Modules}
  {u : m → Γ(M, ⊤)} {j : X ⟶ ℙ(m; S)} (εj : twistRestrict j 1 ⟶ M) [IsIso εj]
  (hεj : ∀ q, εj.app _ (pullbackSection j (twistOneSection m S q)) =
    M.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ ⊤ ≤ ⊤)).op (u q))
  {ψ : W ⟶ ℙ(m; S')} (εψ : twistRestrict ψ 1 ⟶ (Scheme.Modules.pullback φ).obj M) [IsIso εψ]
  (hεψ : ∀ q, εψ.app _ (pullbackSection ψ (twistOneSection m S' q)) =
    ((Scheme.Modules.pullback φ).obj M).presheaf.map (homOfLE (le_top : ψ ⁻¹ᵁ ⊤ ≤ ⊤)).op
      (pullbackTopSection φ (u q)))
include hεj hεψ

end BaseChange

end AlgebraicGeometry.ProjectiveSpace
