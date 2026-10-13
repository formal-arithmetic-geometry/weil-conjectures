/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.AffineFreeBasisGerms

/-! # Bijectivity of the regular-module stalk comparison

Source: Stacks Project, Tags 01HV, 01IB and 0098.
(blueprint: lem-sc-affine-regular-stalk-comparison-bijective).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- The unit germ identifies the ambient stalk ring with the stalk of the sheafification
of the regular coordinate module, after ordinary open direct image.

Source: Stacks Project, Tag 01HV, Lemma 26.5.4 (6)-(7), and Tags 01IB and 0098.
(blueprint: lem-sc-affine-regular-stalk-comparison-bijective).

Proof: The explicit affineRegularSheafIso identifies the sheafification of the regular
module with the structure sheaf on the slice site. Each factor (tildeSelf,
restrictUnitIso, and the unit isomorphism of overEquiv) takes its unit to the unit
section. For any neighbourhood V contained in U, ordinary direct image of that
structure sheaf has sections O_X(V), with the same restrictions and scalar actions:
the slice object V times U is identified with V by the second projection because
V is contained in U. These neighbourhoods are cofinal at x. Taking their colimit
therefore identifies its stalk with O_{X,x}, taking the unit germ to 1. Multiplication
by the unit germ consequently identifies r with r in this colimit, and is bijective.
Composing with the direct image and stalk of affineRegularSheafIso gives precisely
affineRegularStalkComparison. No quasi-compactness hypothesis is used; an empty U
admits no x with hxU. -/
theorem affineRegularStalkComparison_bijective
    (X : Scheme.{u}) (x : X) (U : X.Opens) (hxU : x ∈ U) (hU : IsAffineOpen U) :
    Function.Bijective (affineRegularStalkComparison X x U hxU hU)  := by sorry

end AlgebraicGeometry.Scheme
