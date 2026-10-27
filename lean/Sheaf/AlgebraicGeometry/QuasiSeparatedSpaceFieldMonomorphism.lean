/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Quasi-compact monomorphic field representatives

Source: Stacks Project, Decent Spaces, Tags 03JX and 03JV(4); for an arbitrary base,
Tags 03M5 and 0ABY (blueprint: lem-sfb-qs-space-field-monomorphism).

Quasi-separatedness is relative to the given base scheme. Both quasi-compactness
conditions use the existing representable scheme-test predicate; monomorphism is
cancellation against every algebraic space over that base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every point of a relatively quasi-separated algebraic space has a quasi-compact
monomorphic field representative, without any absolute quasi-separatedness of the base.

Source: Stacks Project, Decent Spaces, Tags 03JX and 03JV(4), with Tags 03M5 and 0ABY
for an arbitrary base scheme (blueprint: lem-sfb-qs-space-field-monomorphism).

Proof:
1. Choose a representable surjective etale scheme atlas V of X, using
   def-trf-algebraic-space. Cover S by affine opens B, and each V_B by affine opens W_i,
   using lem-weil-pbc-affine-opens-basis. The maps a_i : W_i -> X are representable
   etale by lem-weil-pbc-etale-composition-cancellation and jointly surjective on point
   classes by lem-trf-space-fibre-products-etale-covers: a field representative lifts
   to the atlas after a field extension and then lies in one of these opens.
2. Fix x. Each W_i is affine and maps through its chosen affine open B of S.
   Apply lem-sfb-relative-qs-affine-chart-point-fibres to the relative diagonal
   hypothesis. Both the W_i fibre over x and the W_i x_X W_i fibre over x are finite.
3. Apply lem-sfb-finite-chart-fibres-field-quasicompact to this covering and x.
   Every field-valued map representing x is quasi-compact on all affine scheme tests.
   Since x is arbitrary, every field-valued map to X is quasi-compact.
4. Apply lem-sfb-decent-quasicompact-monomorphic-points, namely Tag 03JV(6) implies (4).
   This gives a field representative j of x which is quasi-compact and cancels against
   all algebraic-space test objects over S. The affine-test and all-scheme-test notions
   of quasi-compactness agree: cover any quasi-compact open of a test scheme by finitely
   many affine opens and take the union of their quasi-compact inverse images.
   If X is empty there are no points x, so the conclusion is vacuous. -/
theorem exists_quasiCompact_monomorphic_field_representative_of_quasiSeparated
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))) (x : Point X.obj.obj) :
    ∃ (K : Type u) (_ : Field K) (b : Spec (CommRingCat.of K) ⟶ S)
      (j : yoneda.obj (Over.mk b) ⟶ X.obj.obj),
      schemePointMap j (IsLocalRing.closedPoint K) = x ∧
      (∀ (T : AlgebraicSpace S) (f g : T.obj.obj ⟶ yoneda.obj (Over.mk b)),
        f ≫ j = g ≫ j → f = g) ∧
      IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) j := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
