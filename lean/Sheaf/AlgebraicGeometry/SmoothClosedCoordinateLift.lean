/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import Mathlib.RingTheory.Regular.Flat

/-!
# Lifting coordinates of a smooth closed subscheme

Source: Stacks Project, More on Morphisms, Tag 0FUE, first two proof paragraphs
(blueprint: lem-pur-smooth-closed-coordinate-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Lift étale coordinates from a smooth closed subscheme through an affine quotient,
keeping the prescribed regular equations as the last coordinates. No smoothness of the
ambient scheme is assumed, and no étaleness of the resulting ambient map is asserted.

Source: Stacks Project, More on Morphisms, Tag 0FUE, first two proof paragraphs
(blueprint: lem-pur-smooth-closed-coordinate-lift).

Proof. The given quotient-spectrum identification makes the inverse image of `U₀` affine.
Apply the smooth étale-local normal form to this inverse image at `y`. After restricting
the base to an affine open and the closed subscheme to the resulting coordinate chart,
use the closed embedding's subspace topology to choose a principal affine neighbourhood
of `i(y)` in `U₀` whose inverse image is inside that chart. The equations localize to a
regular sequence: flat localization preserves each multiplication injection, and the
quotient retains the point `y`. The restricted closed subscheme is affine, so its
coordinate functions lift through the surjection on global sections. Append the localized
`f` to these lifts and apply `AffineSpace.homOfVector`. The square with the zero-coordinate
inclusion is cartesian: on rings, tensoring with the polynomial ring modulo the last
variables is the quotient by the images of `f`. Its upper map is the chosen étale chart.
The kernel ideal on each affine open is the span of the restricted `f`: ideal sheaves
localize on affine opens. Flatness of the sections of an affine open over those of an
affine scheme transports the weak regularity to every such open, including opens missing
the closed subscheme. Finally compose both charts with the open immersion of affine spaces
induced by the base open. This preserves the cartesian square and the upper étaleness. -/
theorem Scheme.Hom.exists_coordinate_lift_of_regular_equations
    {S X Y : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (i : Y ⟶ X)
    [Smooth q] [IsClosedImmersion i] (hi : i ≫ p = q) (y : Y)
    (U₀ : X.Opens) (hy₀ : i y ∈ U₀) (A : CommRingCat.{u})
    (eA : U₀.toScheme ≅ Spec A) (f : List A)
    (hf : RingTheory.Sequence.IsRegular A f)
    (eY : pullback i U₀.ι ≅ Spec (CommRingCat.of (A ⧸ Ideal.ofList f)))
    (heY : eY.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList f))) =
      pullback.snd i U₀.ι ≫ eA.hom) :
    ∃ (a : ℕ) (U : X.Opens) (_ : U ≤ U₀) (_ : i y ∈ U)
      (h : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (a + f.length))) S)
      (v : pullback i U.ι ⟶ AffineSpace (ULift.{u} (Fin a)) S),
      h ≫ (AffineSpace (ULift.{u} (Fin (a + f.length))) S ↘ S) = U.ι ≫ p ∧
      IsPullback v (pullback.snd i U.ι)
        (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
          (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
            (fun _ ↦ 0) j.down)) h ∧
      Etale v ∧
      ∀ W : U.toScheme.affineOpens,
        (pullback.snd i U.ι).ker.ideal W = Ideal.span (Set.range (fun j : Fin f.length ↦
          U.toScheme.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
            (h.appTop (AffineSpace.coord S (ULift.up (Fin.natAdd a j)))))) ∧
        RingTheory.Sequence.IsWeaklyRegular Γ(U.toScheme, W)
          (List.ofFn (fun j : Fin f.length ↦
            U.toScheme.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
              (h.appTop (AffineSpace.coord S (ULift.up (Fin.natAdd a j)))))) := by
  sorry

end AlgebraicGeometry
