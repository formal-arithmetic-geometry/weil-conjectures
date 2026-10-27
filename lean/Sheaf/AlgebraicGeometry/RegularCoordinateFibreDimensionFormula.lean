/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Regular.RegularSequence
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Dimension formula on a regular coordinate fibre

Source: Stacks Project, More on Morphisms, Tag 0FUE, final paragraph
(blueprint: lem-pur-regular-coordinate-fibre-dimension-formula).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The local map on the base fibre satisfies the dimension formula needed for
miracle flatness. This asserts only a numerical equality of Krull dimensions.

Source: Stacks Project, More on Morphisms, Tag 0FUE, final paragraph, using
Divisors, Tag 0FUD, More on Algebra, Tag 07QP, and Algebra, Tag 00KW
(blueprint: lem-pur-regular-coordinate-fibre-dimension-formula).

Proof. Choose affine neighbourhoods of the base image and of i(y). The cartesian
square identifies the closed subscheme with the quotient by the last b coordinate
functions. Smoothness of p makes its coordinate algebra flat and finitely
presented over the affine base. The closed quotient is also flat over that base,
since v is etale and affine-space projection is smooth. Localizing at the point
turns weak regularity into regularity: each equation is in the maximal ideal,
and the final quotient has the point y. The relative regular-equation base-change
theorem preserves this sequence in the local ring L of the fibre of p.
Its quotient is the local ring D of the fibre of Y. In the local ring T of the
fibre of affine (a+b)-space, the last b coordinate variables are regular, and
their quotient is the local ring Q of affine a-space. The dimension-drop formula
for a nonzerodivisor, applied b times, gives dim L = b + dim D and
dim T = b + dim Q. The base change of v is etale, so dim D = dim Q.
Thus dim L = dim T. The closed fibre of T to L equals the closed fibre of
Q to D by the cartesian square. The local ring of this etale fibre is a finite
separable field extension and has dimension zero. Substituting these two
identities proves the displayed formula. When b = 0 both sequences are empty
and no dimension-drop step is required. -/
theorem Scheme.Hom.fibre_dimension_formula_of_regular_coordinate_fibre
    {S X Y : Scheme.{u}} (p : X ⟶ S) [Smooth p] (i : Y ⟶ X)
    [IsClosedImmersion i] (a b : ℕ)
    (h : X ⟶ AffineSpace (ULift.{u} (Fin (a + b))) S)
    (v : Y ⟶ AffineSpace (ULift.{u} (Fin a)) S) [Etale v]
    (hh : h ≫ (AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S) = p)
    (H : IsPullback v i
      (AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin a)) S ↘ S)
        (fun j ↦ Fin.addCases (fun k ↦ AffineSpace.coord S (ULift.up k))
          (fun _ ↦ 0) j.down)) h)
    (hreg : ∀ W : X.affineOpens,
      RingTheory.Sequence.IsWeaklyRegular Γ(X, W)
        (List.ofFn (fun j : Fin b ↦
          X.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op
            (h.appTop (AffineSpace.coord S (ULift.up (Fin.natAdd a j)))))))
    (y : Y) :
    let q := AffineSpace (ULift.{u} (Fin (a + b))) S ↘ S
    let s := p (i y)
    let m := pullback.map p (S.fromSpecResidueField s) q (S.fromSpecResidueField s)
      h (𝟙 _) (𝟙 S) (by simpa only [Category.comp_id] using hh.symm) (by simp)
    let z := p.asFiber (i y)
    ringKrullDim ((p.fiber s).presheaf.stalk z) =
      ringKrullDim ((q.fiber s).presheaf.stalk (m z)) +
        ringKrullDim (((p.fiber s).presheaf.stalk z) ⧸
          (IsLocalRing.maximalIdeal ((q.fiber s).presheaf.stalk (m z))).map
            (m.stalkMap z).hom) := by sorry

end AlgebraicGeometry
