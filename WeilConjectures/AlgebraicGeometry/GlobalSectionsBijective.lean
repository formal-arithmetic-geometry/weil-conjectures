/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Schemes over a field whose global functions are the constants

A `k`-scheme `X` satisfies `AlgebraicGeometry.Scheme.GlobalSectionsBijective k X` if the
structure map `k → Γ(X, 𝒪_X)` is bijective, i.e. `H⁰(X, 𝒪_X) = k`. This is the hypothesis
under which Riemann–Roch on a curve takes the form `χ(𝒪_X) = 1 - g`.

It does not hold for every proper connected `X`: `ℙ¹_ℂ` viewed as an `ℝ`-scheme has
`H⁰(X, 𝒪_X) = ℂ`. It holds for proper `X` that is geometrically connected and geometrically
reduced (Stacks 0BUG), hence for proper geometrically integral `X`, and for smooth proper
connected `X` over a separably closed field.

## Main definitions

- `AlgebraicGeometry.Scheme.GlobalSectionsBijective`: the structure map `k → Γ(X, 𝒪_X)` is
  bijective.

## Main statements

- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyConnected`: a proper,
  geometrically connected and geometrically reduced `k`-scheme has `H⁰(X, 𝒪_X) = k`.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral` and
  `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isSepClosed`: the geometrically integral
  case and the case of a smooth connected scheme over a separably closed field.
- `AlgebraicGeometry.Scheme.GlobalSectionsBijective.pullback`: `H⁰(X, 𝒪_X) = k` is stable under
  base change along a field extension `K/k`, for quasi-compact quasi-separated `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The structure map `k → Γ(X, 𝒪_X)` of a `k`-scheme `X` is bijective, i.e. `H⁰(X, 𝒪_X) = k`.

This is the hypothesis under which Riemann–Roch holds in the form `χ(𝒪_X) = 1 - g` with
`g = dim_k H¹(X, 𝒪_X)`. It fails for `ℙ¹_ℂ` viewed as an `ℝ`-scheme, which has `H⁰ = ℂ`, so
`χ(𝒪) = 2 ≠ 1 - 0` over `ℝ`. -/
class GlobalSectionsBijective : Prop where
  bijective_globalSectionsRingHom : Function.Bijective (globalSectionsRingHom k (X := X))

variable {k X}

/-- A proper `k`-scheme that is geometrically connected and geometrically reduced has
`H⁰(X, 𝒪_X) = k` (Stacks 0BUG). -/
instance GlobalSectionsBijective.of_geometricallyConnected [IsProper (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] [GeometricallyReduced (X ↘ Spec (.of k))] :
    GlobalSectionsBijective k X :=
  sorry

/-- A proper geometrically integral `k`-scheme has `H⁰(X, 𝒪_X) = k`. -/
theorem GlobalSectionsBijective.of_geometricallyIntegral [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] : GlobalSectionsBijective k X :=
  inferInstance

/-- A smooth proper connected scheme over a separably closed field `k` has
`H⁰(X, 𝒪_X) = k`. -/
theorem GlobalSectionsBijective.of_isSepClosed [IsSepClosed k] [Smooth (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] : GlobalSectionsBijective k X :=
  have := GeometricallyConnected.of_isSepClosed (k := k) X
  inferInstance

/-- **Flat base change of `H⁰(X, 𝒪_X) = k`.** If a quasi-compact quasi-separated `k`-scheme `X`
has `H⁰(X, 𝒪_X) = k`, then so does its base change `X_K = X ×_{Spec k} Spec K` along a field
extension `K/k`: `Γ(X_K, 𝒪_{X_K}) = Γ(X, 𝒪_X) ⊗_k K = K` since `K` is flat over `k`. -/
instance GlobalSectionsBijective.pullback (K : Type u) [Field K] [Algebra k K]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))]
    [GlobalSectionsBijective k X] :
    GlobalSectionsBijective K
      (Limits.pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  set f := Spec.map (CommRingCat.ofHom (algebraMap k K))
  set iX := X ↘ Spec (.of k)
  have H := IsPullback.of_hasPullback iX f
  -- `Γ(X_K, ⊤)` is the pushout of `Γ(X, ⊤) ← k → K`.
  have hUY : (⊤ : (Limits.pullback iX f).Opens) =
      Limits.pullback.fst iX f ⁻¹ᵁ ⊤ ⊓ Limits.pullback.snd iX f ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H
    (US := ⊤) (UT := ⊤) (UX := ⊤) le_top le_top hUY
    (isAffineOpen_top _) (isAffineOpen_top _) isCompact_univ isQuasiSeparated_univ
  have hX : IsIso (iX.appLE ⊤ ⊤ le_top) := by
    have h := GlobalSectionsBijective.bijective_globalSectionsRingHom (k := k) (X := X)
    rw [globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective] at h
    have : IsIso iX.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv _
    simpa [Hom.appTop, Hom.app_eq_appLE] using this
  -- The pushout of the isomorphism `k → Γ(X, ⊤)` along `k → K` is an isomorphism.
  have hY : IsIso ((Limits.pullback.snd iX f).appLE ⊤ ⊤ (hUY.trans_le inf_le_right)) := by
    have e : pushout.inr _ _ ≫ pushoutSection H (US := ⊤) le_top le_top hUY = _ :=
      pushout.inr_desc _ _ _
    rw [← e]
    exact IsIso.comp_isIso' inferInstance hiso
  constructor
  rw [globalSectionsRingHom, ← ConcreteCategory.isIso_iff_bijective]
  have : IsIso (Limits.pullback.snd iX f).appTop := by
    simpa [Hom.appTop, Hom.app_eq_appLE] using hY
  exact IsIso.comp_isIso' inferInstance this

end AlgebraicGeometry.Scheme
