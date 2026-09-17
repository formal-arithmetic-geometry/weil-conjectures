/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FibrewiseCriteria
public import WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle

/-!
# The triviality criterion for a line bundle over a field

Let `K` be a field, let `X` be a proper geometrically integral `K`-scheme and let `L` be a line
bundle on `X`, with tensor inverse `N`. This file proves that `L` is trivial — isomorphic to the
structure sheaf — **if and only if** both `Γ(X, L)` and `Γ(X, N)` are non-zero. The field `K` is
not assumed algebraically closed, which is what makes the criterion applicable at *every* point
of a base scheme and not only at the rational ones.

The invertibility of `L` and of `N` is not a separate hypothesis: the criterion takes an
isomorphism `e : L ⊗ N ≅ 𝟙_ X.Modules`, from which `SheafOfModules.Invertible.left` and
`SheafOfModules.Invertible.right` recover `L.Invertible` and `N.Invertible`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_isField`: **the triviality
  criterion**, under the hypotheses that `X` is integral and that its ring of global functions is
  a field.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_universallyClosed` and
  `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral`: the
  same criterion for `X` integral and universally closed over a field `K`, and for `X` proper and
  geometrically integral over `K`, where those two hypotheses are automatic.

The key step of the proof is
`AlgebraicGeometry.Scheme.Modules.isIso_fiberMap_comp_of_ne_zero`.

## Blueprint

`lem:cube-triviality-criterion` of
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {L N : X.Modules}

/-- **The key step of the triviality criterion.** Let `e : L ⊗ N ≅ 𝒪ₓ` and let `g : 𝒪ₓ ⟶ L` and
`h : 𝒪ₓ ⟶ N` be two morphisms which are both non-zero on the fibre at `x`. Then the composite
`g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom` is an isomorphism on the fibre at `x`, because it is the
lower edge of the commuting square

```
              g ⊗ h
   𝟙 ⊗ 𝟙 ──────────────→ L ⊗ N
     ↑                      │
  λ⁻¹│                      │ e
     │                      ↓
     𝟙 ────────────────────→ 𝟙
```

whose three other edges have invertible fibres at `x`. -/
theorem isIso_fiberMap_comp_of_ne_zero (hL : L.Invertible) (hN : N.Invertible)
    (e : L ⊗ N ≅ 𝟙_ X.Modules) (g : 𝟙_ X.Modules ⟶ L) (h : 𝟙_ X.Modules ⟶ N) {x : X}
    (hg : fiberMap g x ≠ 0) (hh : fiberMap h x ≠ 0) :
    IsIso (fiberMap (g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom) x) := by
  have hone : (𝟙_ X.Modules).Invertible := invertible_tensorUnit X.sheaf
  have hgiso : IsIso (fiberMap g x) := isIso_fiberMap_of_ne_zero hone hL g hg
  have hhiso : IsIso (fiberMap h x) := isIso_fiberMap_of_ne_zero hone hN h hh
  have htensor : IsIso (fiberMap (g ⊗ₘ h) x) := by
    have hcomp : IsIso (fiberMap (g ⊗ₘ h) x ≫ (fiberTensorIso L N x).hom) := by
      rw [← fiberTensorIso_hom_naturality g h x]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (fiberTensorIso L N x).hom
  have hfac : g ≫ (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom
      = (λ_ (𝟙_ X.Modules)).inv ≫ (g ⊗ₘ h) ≫ e.hom := by
    rw [rightUnitor_inv_naturality_assoc, tensorHom_def, unitors_inv_equal]
    simp
  rw [hfac]
  simp only [fiberMap_comp]
  infer_instance

/-- **The triviality criterion for a line bundle.** Let `X` be an integral scheme whose ring of
global functions is a field, and let `L` and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is
isomorphic to the structure sheaf if and only if both `Γ(X, L)` and `Γ(X, N)` are non-zero.

This is `lem:cube-triviality-criterion` of the blueprint, stated under the two hypotheses on `X`
that the proof actually uses; see
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_iff_of_geometricallyIntegral` for the
form the blueprint gives it. -/
theorem nonempty_iso_tensorUnit_iff_of_isField [IsIntegral X] (hfield : IsField Γ(X, ⊤))
    (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(N, ⊤) := by
  have hL : L.Invertible := Invertible.left (R := X.sheaf) e
  have hN : N.Invertible := Invertible.right (R := X.sheaf) e
  have hone : (𝟙_ X.Modules).Invertible := invertible_tensorUnit X.sheaf
  have : Nontrivial Γ(X, ⊤) := ⟨hfield.exists_pair_ne⟩
  constructor
  · rintro ⟨f⟩
    exact ⟨nontrivial_sections_of_iso_unit (f ≪≫ tensorUnitIso X.sheaf),
      nontrivial_sections_of_iso_unit
        ((λ_ N).symm ≪≫ (f.symm ⊗ᵢ Iso.refl N) ≪≫ e ≪≫ tensorUnitIso X.sheaf)⟩
  · rintro ⟨hLnt, hNnt⟩
    -- a non-zero global section of a line bundle gives a morphism from `𝒪ₓ` which is non-zero
    -- on some fibre
    have key {M : X.Modules} (hM : M.Invertible) {m : Γ(M, ⊤)} (hm : m ≠ 0) :
        ∃ (u : 𝟙_ X.Modules ⟶ M) (x : X), fiberMap u x ≠ 0 := by
      obtain ⟨x, hx⟩ := exists_fiberMap_homOfSectionTop_ne_zero hM hm
      refine ⟨(tensorUnitIso X.sheaf).hom ≫ homOfSectionTop M m, x, ?_⟩
      rw [fiberMap_comp, Ne, Preadditive.IsIso.comp_left_eq_zero]
      exact hx
    obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L, ⊤))
    obtain ⟨v, hv⟩ := exists_ne (0 : Γ(N, ⊤))
    obtain ⟨g, x₁, hx₁⟩ := key hL hs
    obtain ⟨h, x₂, hx₂⟩ := key hN hv
    -- the two non-degeneracy loci are non-empty opens, and `X` is irreducible, so they meet
    obtain ⟨x₀, hx₀₁, hx₀₂⟩ := nonempty_preirreducible_inter
      (isClosed_setOf_fiberMap_eq_zero hone hL g).isOpen_compl
      (isClosed_setOf_fiberMap_eq_zero hone hN h).isOpen_compl
      ⟨x₁, by simpa using hx₁⟩ ⟨x₂, by simpa using hx₂⟩
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx₀₁ hx₀₂
    -- the composite `𝒪ₓ ⟶ L ⟶ 𝒪ₓ` is multiplication by a global function which does not vanish
    -- at `x₀`, hence is a unit because `Γ(X, 𝒪ₓ)` is a field
    obtain ⟨ψ, hψ⟩ : ∃ ψ : L ⟶ 𝟙_ X.Modules, ψ = (ρ_ L).inv ≫ (L ◁ h) ≫ e.hom := ⟨_, rfl⟩
    have hfib : IsIso (fiberMap (g ≫ ψ) x₀) := by
      rw [hψ]
      exact isIso_fiberMap_comp_of_ne_zero hL hN e g h hx₀₁ hx₀₂
    obtain ⟨χ, hχ⟩ : ∃ χ : X.structureModules ⟶ X.structureModules,
        χ = (tensorUnitIso X.sheaf).inv ≫ (g ≫ ψ) ≫ (tensorUnitIso X.sheaf).hom := ⟨_, rfl⟩
    have hχfib : IsIso (fiberMap χ x₀) := by
      rw [hχ, fiberMap_comp, fiberMap_comp]
      infer_instance
    have hc : endSection χ ≠ 0 := fun hz ↦
      fiberMap_ne_zero_of_isIso_fiberMap χ x₀ hχfib
        ((fiberMap_eq_zero_iff_evaluation_endSection χ x₀).2 (by simp only [hz, map_zero]))
    have hχIso : IsIso χ :=
      (isIso_iff_isUnit_endSection χ).2 (isUnit_iff_exists_inv.mpr (hfield.mul_inv_cancel hc))
    rw [hχ] at hχIso
    have hright : IsIso ((g ≫ ψ) ≫ (tensorUnitIso X.sheaf).hom) :=
      IsIso.of_isIso_comp_left (tensorUnitIso X.sheaf).inv _
    have : IsIso (g ≫ ψ) := IsIso.of_isIso_comp_right _ (tensorUnitIso X.sheaf).hom
    -- so `g` is non-zero on every fibre, and the fibrewise criterion makes it an isomorphism
    have hall (x : X) : fiberMap g x ≠ 0 := by
      intro hz
      have := nontrivial_fiber hone x
      exact fiberMap_ne_zero_of_isIso (g ≫ ψ) x (by rw [fiberMap_comp, hz, Limits.zero_comp])
    have : IsIso g := isIso_of_forall_fiberMap_ne_zero hone hL g hall
    exact ⟨(asIso g).symm⟩

/-- **The triviality criterion for a line bundle on an integral scheme, universally closed over a
field.** Let `K` be a field, let `π : X ⟶ Spec K` be universally closed with `X` integral and let
`L` and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is trivial if and only if both
`Γ(X, L)` and `Γ(X, N)` are non-zero. -/
theorem nonempty_iso_tensorUnit_iff_of_universallyClosed {K : Type u} [Field K]
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed π] (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(N, ⊤) :=
  nonempty_iso_tensorUnit_iff_of_isField (isField_of_universallyClosed K π) e

/-- **The triviality criterion for a line bundle on a proper geometrically integral scheme over a
field.** Let `K` be a field, let `X` be proper and geometrically integral over `K` and let `L`
and `N` be `𝒪ₓ`-modules with `L ⊗ N ≅ 𝒪ₓ`. Then `L` is trivial if and only if both `Γ(X, L)` and
`Γ(X, N)` are non-zero. The field `K` need not be algebraically closed.

This is `lem:cube-triviality-criterion` of the blueprint. -/
theorem nonempty_iso_tensorUnit_iff_of_geometricallyIntegral (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [IsProper (X ↘ Spec (.of K))]
    [GeometricallyIntegral (X ↘ Spec (.of K))] (e : L ⊗ N ≅ 𝟙_ X.Modules) :
    Nonempty (L ≅ 𝟙_ X.Modules) ↔ Nontrivial Γ(L, ⊤) ∧ Nontrivial Γ(N, ⊤) :=
  have : IsIntegral X := GeometricallyIntegral.isIntegral (X ↘ Spec (.of K))
  nonempty_iso_tensorUnit_iff_of_universallyClosed (X ↘ Spec (.of K)) e

end AlgebraicGeometry.Scheme.Modules
