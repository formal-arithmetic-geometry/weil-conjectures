/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.RingTheory.Flat.TorsionFree

import WeilConjectures.AlgebraicGeometry.Curve.NonconstantCurveStalkTorsionFree
import WeilConjectures.AlgebraicGeometry.Curve.NormalCurveLocalPrincipalDomains

/-!
# Flatness of a nonconstant morphism to a normal curve

Source: Stacks Project, `literature/stacks-project/curves.tex`, Tag 0CCK, lemma-flat
(blueprint: lem-a1-nonconstant-normal-curve-map-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A morphism of integral curves over a field with at least two points in its image is flat
when its target is normal.

Source: Stacks Project, `curves.tex`, Tag 0CCK, lemma-flat
(blueprint: lem-a1-nonconstant-normal-curve-map-flat).

Proof:
1. `X` is integral and `Y ⟶ Spec k` is an integral curve. Since `f` has two points with
   distinct images, `lem-a1-nonconstant-curve-stalk-torsion-free` gives, for every `x : X`,
   that `A = 𝒪_{Y,f(x)}` and `B = 𝒪_{X,x}` are domains and that `B` is torsion free over `A`
   via the stalk map: `a ≠ 0` and `f(a) * b = 0` imply `b = 0`.
2. `Y` is a normal curve, so `lem-a1-normal-curve-local-principal-domains` at `f(x)` makes `A`
   a principal ideal domain (a field or a discrete valuation ring).
3. A torsion-free module over a principal ideal domain is flat
   (`lem-weil-pbc-pid-torsion-free-module-flat`; Mathlib
   `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`), with no finite-generation assumption.
   So every stalk map is flat, and stalkwise flatness is flatness of `f`
   (`def-weil-flat-morphism`, Mathlib `Flat.of_stalkMap`).
-/
theorem flat_of_nonconstant_of_isNormalCurve {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsIntegralCurve (X ↘ Spec (.of k))] [IsIntegralCurve (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (h_nonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂) (h_normal : IsNormalScheme Y) :
    Flat f := by
  apply Flat.of_stalkMap f
  intro x
  have h₁ := Scheme.Hom.nonconstant_curve_stalk_torsion_free
    (sY := (Y ↘ Spec (.of k))) f h_nonconstant
  have h₂ := IsIntegralCurve.stalk_local_principal_domains
    (f := (Y ↘ Spec (.of k))) h_normal (f x)
  let _ : IsDomain (Y.presheaf.stalk (f x)) := h₂.2.2.2.2.2.1
  let _ : IsPrincipalIdealRing (Y.presheaf.stalk (f x)) := h₂.2.2.2.2.2.2
  algebraize [(f.stalkMap x).hom]
  change Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  refine eq_bot_iff.mpr ?_
  rintro m ⟨⟨a, ha⟩, hma⟩
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  apply (h₁.2.2 x).2.2.2 a m ha0
  change (f.stalkMap x).hom a * m = 0 at hma
  exact hma

end AlgebraicGeometry
