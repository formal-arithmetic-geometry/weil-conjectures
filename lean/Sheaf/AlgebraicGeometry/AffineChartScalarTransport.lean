/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Sheaf.Paper.DerivedHomMayerVietoris

/-! # Scalar action calculation for an affine chart -/

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Transport along an affine chart and the slice equivalence carries the
coordinate-ring scalar action to the action on sections over the chart.
Source: Stacks Project, Tag 0098 (restriction of sheaves of modules),
Tag 01HV, Lemma 26.5.4 (7), and Tag 01IB.
(blueprint: lem-sc-affine-chart-scalar-transport).

Proof: Restriction along isoSpec evaluates a section map at the image open,
with scalars restricted through the inverse structure-ring isomorphism.
The inverse slice equivalence evaluates at the open of U corresponding to
the slice object U times U. Ordinary direct image uses the second projection
for its ring map. The canonical Spec scalar, pulled back along isoSpec, is
the restriction of a: on the top open this is isoSpec_hom_appTop and the
inverse identities of GammaSpecIso and U.topIso; on smaller opens it follows
by naturality. Thus the hypothesized scalar action becomes the restriction
of a along the second projection, which is precisely the scalar action in
the pushforward module. This works for arbitrary sheaves and their maps;
it needs neither a regular-module presentation nor a point or stalk. -/
theorem affine_chart_scalar_transport (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) (a : Γ(X, U))
    (M : (Spec Γ(X, U)).Modules) (f : M ⟶ M)
    (hf : ∀ (V : (Spec Γ(X, U)).Opens) (s : Γ(M, V)),
      (f.val.app (.op V)) s = a • s) :
    let T := Modules.restrictFunctor hU.isoSpec.hom ⋙ (Modules.overEquiv U).inverse
    let P := SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)
    ∀ m : (P.obj (T.obj M)).val.obj (.op U),
      (P.map (T.map f)).val.app (.op U) m = a • m := by sorry

end AlgebraicGeometry.Scheme
