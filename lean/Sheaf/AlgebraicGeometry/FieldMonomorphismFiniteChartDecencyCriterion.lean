/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Field.Defs
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCompactFppfLocal
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits

/-! # Finite chart fibres imply quasi-compact field representatives

Source: Stacks Project, Decent Spaces, Tag 03JV, implication (3) to (6)
(blueprint: lem-sfb-field-monomorphism-finite-chart-decency-criterion).

The finite hypothesis concerns the projection to the field spectrum. The conclusion
concerns the entire scheme fibre product over every affine test, including tests whose
map to the algebraic space is not étale. Both fibre products are specified by actual
representing pullback squares, without choosing a representative scheme globally.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A monomorphic field representative with finite fibres on all affine étale charts
makes every field representative of the same point quasi-compact on arbitrary affine tests.
Monomorphy is cancellation on maps from every scheme. The base is the universe lift of
`Spec ℤ`, so its over-schemes are all schemes in the chosen universe.
Source: Stacks Project, Decent Spaces, Tag 03JV, (3) implies (4) implies (6);
Properties of Spaces, Tag 0H2X; Schemes, Tag 03DP
(blueprint: lem-sfb-field-monomorphism-finite-chart-decency-criterion).

Proof:
1. Choose an affine-component étale atlas by [lem-a1-space-affine-etale-cover].
   Each fibre over `Spec K` is finite by hypothesis, hence affine by
   [def-weil-finite-integral-morphism] and [lem-weil-pbc-affine-morphism-permanence](2).
   By [lem-weil-pbc-affine-scheme-qcqs] it is quasi-compact, and its affine chart is
   quasi-separated. Thus its projection to the chart is quasi-compact by
   [lem-weil-pbc-qcqs-morphism-permanence](1). Empty fibres cause no exception.
2. The atlas is jointly surjective, flat and locally finitely presented, by
   [def-weil-etale-morphism]. Apply [lem-sfb-space-quasicompact-fppf-local] and the
   representable compatibility in [lem-sfb-space-quasicompact-affine-tests] to conclude
   that `j` is quasi-compact, including after every arbitrary affine scheme test.
3. For another representative `q : Spec L → X` of `x`, the representable diagonal
   [def-trf-algebraic-space] makes `Y = Spec K ×_X Spec L` a scheme. Equality of point
   classes gives a common field and a point of `Y`, by [def-a1-algebraic-space-point-classes].
   Its projection to `Spec L` is monic: cancellation for `j` gives equality of the
   projections to `Spec K`, and the pullback property then gives equality of maps to `Y`.
   Apply [lem-sfb-monomorphism-into-field-coproduct] with one component. Nonemptiness
   rules out the empty subset, so `Y → Spec L` is an isomorphism. Its inverse gives
   `h : Spec L → Spec K` with `q = h ≫ j` (in the sheaf sense).
4. For any affine `T → X`, put `F = T ×_X Spec K` and `E = T ×_X Spec L`.
   The diagonal makes both schemes; step 2 makes `F` quasi-compact.
   The source of `h` is affine, hence quasi-compact, and its target is affine, hence
   quasi-separated, so `h` is quasi-compact by [lem-weil-pbc-qcqs-morphism-permanence](1).
   The factorization identifies `E` with `F ×_Spec K Spec L` by the pullback universal
   property. Parts (3) and (2) of that permanence node make `E → F` quasi-compact and
   then `E` quasi-compact. This uses no étaleness of `T → X` and no finiteness of `L/K`. -/
theorem quasiCompact_field_representatives_of_finite_etale_chart_fibres
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (x : Point X.obj.obj)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (.of (ULift.{u} ℤ)))
    (j : yoneda.obj (Over.mk b) ⟶ X.obj.obj)
    (hj : schemePointMap j (IsLocalRing.closedPoint K) = x)
    (hmono : ∀ H : Over (Spec (.of (ULift.{u} ℤ))),
      Function.Injective (fun a : yoneda.obj H ⟶ yoneda.obj (Over.mk b) ↦ a ≫ j))
    (hfinite : ∀ (U : Over (Spec (.of (ULift.{u} ℤ)))), IsAffine U.left →
      ∀ a : yoneda.obj U ⟶ X.obj.obj, IsEtale a →
        ∃ (V : Over (Spec (.of (ULift.{u} ℤ)))) (p : V ⟶ Over.mk b)
          (r : yoneda.obj V ⟶ yoneda.obj U),
          IsPullback r (yoneda.map p) a j ∧ IsFinite p.left) :
    ∀ (L : Type u) [Field L] (c : Spec (.of L) ⟶ Spec (.of (ULift.{u} ℤ)))
      (q : yoneda.obj (Over.mk c) ⟶ X.obj.obj),
      schemePointMap q (IsLocalRing.closedPoint L) = x →
      ∀ (T : Over (Spec (.of (ULift.{u} ℤ)))), IsAffine T.left →
        ∀ t : yoneda.obj T ⟶ X.obj.obj,
          ∃ (V : Over (Spec (.of (ULift.{u} ℤ)))) (p : V ⟶ T)
            (r : yoneda.obj V ⟶ yoneda.obj (Over.mk c)),
            IsPullback r (yoneda.map p) q t ∧ CompactSpace V.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
