/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.FiniteOverProjective

/-! # Smooth projective compactification of a normal finite-field curve

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-i-real-compactification,
lemma and proof lem-wf-curve-normal-smooth-compactification, paragraphs 1–3
(blueprint: lem-wf-curve-normal-smooth-compactification).

The boundary carries Mathlib's canonical reduced induced closed subscheme structure, defined
by the vanishing ideal sheaf of the complement of the open image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A normal geometrically connected finite-field curve has a smooth projective geometrically
connected compactification with reduced boundary finite over the base field.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-i-real-compactification,
lem-wf-curve-normal-smooth-compactification, paragraphs 1–3; Stacks Tags 00TV and 0B3I
(blueprint: lem-wf-curve-normal-smooth-compactification).

Proof:
1. Finite type gives Noetherianity. Geometric connectedness gives connectedness. The components
   of a normal Noetherian scheme are disjoint open and closed, hence U is integral. Its generic
   stalk is a field; at a closed point it is a one-dimensional normal Noetherian local domain,
   hence a DVR by lem-sc-normal-dim1-dvr. These rings are regular. The finite field is perfect,
   so lem-trf-regular-perfect-field-smooth gives smoothness of U.
2. Use lem-wf-finite-field-curve-quasi-projective to take an integral projective closure X of U.
   Normalize X using def-sc-normalization. By lem-sc-normalization-properties the normalization
   C is finite over X, has dimension one and agrees with U over the normal open. Thus U embeds
   densely and openly into C. By lem-fin-finite-over-projective, C is projective over the affine
   field spectrum; the perfect-field clause of lem-sc-normalization-properties makes C smooth.
3. The complement is a proper closed subset of an integral one-dimensional scheme. It has
   dimension at most zero, so lem-sc-dim0-finite makes it a finite set of closed points. Its
   reduced induced scheme, constructed using the subscheme of its vanishing ideal sheaf, is
   finite over the field: its residue fields are finite extensions. This is the reduction
   convention def-weil-pbc-scheme-reduction. After every field extension the given open remains
   dense and connected, so its closure is connected, giving geometric connectedness of C by
   def-pc-geometrically-irreducible.
-/
theorem exists_smooth_projectiveCompactification_normal
    {K : Type u} [Field K] [Finite K] {U : Scheme.{u}}
    (p : U ⟶ Spec (.of K)) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [GeometricallyConnected p]
    (hU : ∀ x : U,
      IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x))
    (hdim : U.IsPureDimension 1) :
    Smooth p ∧ ∃ (C : Scheme.{u}) (pC : C ⟶ Spec (.of K))
      (j : U ⟶ C) (_ : IsOpenImmersion j),
      j ≫ pC = p ∧ IsSmoothProjectiveCurve pC ∧ GeometricallyConnected pC ∧
        DenseRange j.base ∧
          IsFinite ((Scheme.IdealSheafData.vanishingIdeal
            ⟨(j.opensRange : Set C)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subschemeι ≫ pC) := by
  sorry

end AlgebraicGeometry
