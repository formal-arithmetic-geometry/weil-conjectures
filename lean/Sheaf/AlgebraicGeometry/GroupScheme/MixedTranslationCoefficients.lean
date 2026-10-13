/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.InvariantCoefficients

/-!
# The mixed coefficient of a commutator of right translations

Source: the second coefficient step of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`, blueprint `sk-d-tangent`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- If the two-parameter commutator of v and w is the mixed lift of t, its invariant
coefficient is the commutator of the invariant coefficient operators of v and w.

Source: the second coefficient step of the Lie-ring paragraph in
`WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean`.
(blueprint: lem-ag-mixed-translation-coefficients)

Proof: Pull the three explicit right translations back to G[ε][δ]. On sections the
first two act as 1+εD_v and 1+δD_w, with derivations acting coefficientwise and fixing
both parameters. Their inverses act as 1-εD_v and 1-δD_w. Composition of comorphisms
in the order specified by v_ε w_δ v_ε⁻¹ w_δ⁻¹ gives
1+εδ(D_v D_w-D_w D_v), by ε²=δ²=0. The hypothesis identifies this translation with
the translation attached to t pulled back by η↦εδ, whose comorphism is 1+εδD_t.
Equality of the εδ coefficients gives the asserted equality on every open, and hence
of the families of additive endomorphisms. The construction uses right translation of
the universal point, so the coefficient identity is sheafwise without affine,
smoothness, nonemptiness, or characteristic hypotheses. -/
theorem invariantCoefficient_of_mixed_commutator (v w t : infPoints G)
    (h : Scheme.dualNumbersMulOver S ≫ t.1 =
      (Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1) *
        (Scheme.dualNumbersProjεOver S ≫ v.1)⁻¹ *
          (Scheme.dualNumbersProjδOver S ≫ w.1)⁻¹) :
    invariantCoefficient G t =
      invariantCoefficient G v * invariantCoefficient G w -
        invariantCoefficient G w * invariantCoefficient G v := by sorry

end AlgebraicGeometry.GrpObj
