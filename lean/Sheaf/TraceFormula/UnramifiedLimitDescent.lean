/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.RingTheory.ColimitUnramifiedAlgebra

/-! # Descent of unramified morphisms along affine-transition limits

Source: Stacks Project, Limits, Tag 0C4W (lemma-descend-unramified), in
Situation (situation-descent-property) (blueprint: lem-trf-unramified-limit-descent).

## Main definitions

- `AlgebraicGeometry.baseChangeHom` is the canonical morphism between the two
  pullbacks of a morphism along a common base map.

## Main statements

- `AlgebraicGeometry.unramified_limit_descent` states eventual unramifiedness at a
  stage of an affine-transition inverse system.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical base-change morphism induced by a commutative triangle.
Source: Stacks Project, Limits, Tag 0C4W, the induced maps `g_i` and `g` in the
proof of `lemma-descend-unramified` (blueprint: lem-trf-unramified-limit-descent). -/
noncomputable def baseChangeHom {S T U V : Scheme.{u}}
    (u : U ⟶ S) (v : V ⟶ S) (g : U ⟶ V) (t : T ⟶ S)
    (hg : g ≫ v = u) : pullback u t ⟶ pullback v t :=
  pullback.map u t v t g (𝟙 T) (𝟙 S) hg.symm (by simp)

/-- If a locally finite type morphism becomes unramified after passage to the
limit of a directed inverse system with affine transitions, it is unramified at
some stage. The maps at the stages and at the limit are the canonical pullback
maps supplied by `baseChangeHom`.

Source: Stacks Project, Limits, Tag 0C4W (lemma-descend-unramified), in
Situation (situation-descent-property). The proof is the following finite affine
descent argument (blueprint: lem-trf-unramified-limit-descent).

1. Write the initial stage as `i₀`, and denote the transition and limit maps to
   `D.obj (op i₀)` by `p_i` and `p`. Cover that stage by affine opens.  Pulling
   these back to `V₀`, quasi-compactness of `V₀` gives finitely many affine opens
   `Y_{j,0}` mapping into affine opens `W_{j,0}` of the base.  By
   `lem-weil-pbc-qcqs-morphism-permanence`, `g₀` is quasi-compact, so each
   inverse image `g₀ ⁻¹ Y_{j,0}` is quasi-compact.  Choose finite affine covers
   `X_{jk,0}` of those inverse images.  Writing the three affine charts as
   `Spec R₀`, `Spec B₀`, and `Spec C₀`, the restriction of `g₀` is induced by
   `B₀ ⟶ C₀`; `lem-weil-pbc-lft-affine-pairs` says this map is of finite type.

2. For every later stage and for the limit, pull back `W_{j,0}` and write the
   resulting affine schemes as `Spec R_i` and `Spec R`.  The affine-transition
   limit theorem `lem-weil-pbc-limit-affine-transition` identifies
   `R` with the filtered colimit of the `R_i`.  The affine fibre-product
   comparison `lem-weil-pbc-fibre-product-affine-spectra` identifies the pulled
   back charts with `Spec (R_i ⊗[R₀] B₀)` and
   `Spec (R_i ⊗[R₀] C₀)`, and similarly over `R`; the restrictions of `g_i`
   and `g` are induced by `id ⊗ (B₀ ⟶ C₀)`.  These charts cover the base changes
   of `U₀` and `V₀`, and each source chart maps into its corresponding target
   chart.

3. Fix `(j,k)`.  The restriction of the unramified limit morphism is unramified
   by clause (2) of `lem-weil-pbc-unramified-base-change-open`; the affine
   unramified criterion `lem-weil-pbc-unramified-ring-map-iff-unramified-affine`
   therefore makes `R ⊗[R₀] B₀ ⟶ R ⊗[R₀] C₀` unramified.  Apply
   `lem-trf-colimit-unramified-algebra` to obtain a stage `i_{jk}` where the
   corresponding ring map is unramified.  Directedness gives a common stage
   `i ≥ i_{jk}` for all finitely many pairs.  For `i_{jk} ≤ i`, associativity of
   tensor products identifies the chart at `i` with the base change of the chart
   at `i_{jk}`; clause (1) of `lem-weil-pbc-unramified-base-change-open` preserves
   unramifiedness under this base change.  Thus every affine chart of `g_i` is
   finite type with vanishing differentials, and the affine-cover characterization
   in `def-weil-unramified-morphism` shows that `g_i` is unramified. -/
theorem unramified_limit_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (U₀ V₀ : Scheme.{u})
    [CompactSpace U₀] [QuasiSeparatedSpace U₀]
    [CompactSpace V₀] [QuasiSeparatedSpace V₀]
    (u₀ : U₀ ⟶ D.obj (op i₀)) (v₀ : V₀ ⟶ D.obj (op i₀))
    (g₀ : U₀ ⟶ V₀) (hg₀ : g₀ ≫ v₀ = u₀) [LocallyOfFiniteType g₀]
    (hg : IsUnramified (baseChangeHom u₀ v₀ g₀ (c.π.app (op i₀)) hg₀)) :
    ∃ (i : I) (h : i₀ ≤ i),
      IsUnramified
        (baseChangeHom u₀ v₀ g₀ (D.map (homOfLE h).op) hg₀) := by
  sorry

end AlgebraicGeometry
