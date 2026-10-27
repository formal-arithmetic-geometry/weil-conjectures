/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import WeilConjectures.AlgebraicGeometry.DensePoints

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.FiniteClosedSetRationalLifts
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.DescentNormAffineShrinking
import Sheaf.AlgebraicGeometry.InvariantOpenImagePullback
import Sheaf.AlgebraicGeometry.FpqcAffineDescent

/-!
# Affine neighbourhoods of finite subsets of a homogeneous scheme

Source: Milne, Algebraic Groups (2017), Appendix B, Theorem B.37, Step 2,
printed p.605; arbitrary finite point sets follow by closed specialization.
(blueprint: lem-sfb-homogeneous-scheme-finite-set-affine).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Every finite subset of an existing homogeneous scheme has an affine open neighbourhood.

Source: Milne, Algebraic Groups (2017), Appendix B, Theorem B.37, Step 2, printed p.605.
(blueprint: lem-sfb-homogeneous-scheme-finite-set-affine).

The tensor product in `Over (Spec (.of k))` is the fibre product over `k`, and its
unit is `Spec k` with identity structure morphism. Thus `o` is a rational point.
The two identities are the left action laws on every test scheme. The equation
`hq` identifies `q` with the actual orbit morphism of `o`, not an arbitrary cover.

Proof: (1) For a finite set E, choose a closed specialization of every point,
using lem-sc-lft-over-field-jacobson-space. Every open containing the resulting
finite closed set S contains E. For E empty use the empty affine open. By
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-finitely-many-components,
lem-weil-pbc-qcqs-over-affine and lemma-nagata-affine-neighbourhood-generic-points-exists,
choose a dense affine open U containing the component generic points of Y.
(2) Apply lem-sfb-finite-closed-set-rational-lifts to q and S: after a finite
extension K/k every point over S is rational and lifts to a rational point g_j of G_K.
(3) Scalar projection is finite flat and locally finitely presented, by the
finite-free tensor-product description and multiplication-table presentation of a
finite field extension (lem-sfb-finite-scalar-extension-generic-points).
Surjectivity survives base change (lem-weil-pbc-surjective-base-change), and flat
locally finitely presented maps are open (lem-weil-pbc-flat-lfp-open). Hence U_K
is dense and V = q_K⁻¹(U_K) is dense open in G_K.
(4) The intersection of the finitely many dense opens g_j V⁻¹ is dense and
nonempty, since G_K contains its identity. Finite type survives base change
(lem-sfb-finite-type-composition-base-change). The Jacobson property and
lem-kun-closed-point-field supply a point g in this intersection rational over
a finite extension L/K, hence finite over k; no separability assumption is needed.
(5) Write g_j = g v_j with v_j in V_L. The action laws imply that the affine
translate A = g U_L contains every point of Y_L over S. Translation is an
isomorphism with inverse translation by g⁻¹.
(6) Apply lem-pd-descent-norm-affine-shrinking to the canonical descent datum
(def-pd-descent-datum) along Spec L → Spec k, with V = Y_L. The relation object
is Y_L ×_Y Y_L (def-pc-fibre-product), and the finite set over S is saturated.
Obtain a saturated affine open W inside A containing that whole finite set.
(7) By lem-trf-invariant-open-image-pullback its image B in Y is open with
inverse image W, and contains S. The singleton Spec L → Spec k is an fpqc
cover (def-weil-pbc-fpqc-covering). By lem-weil-pbc-fpqc-descend-affine, B is
affine, since its scalar extension W is affine. Thus B contains E. -/
theorem exists_isAffineOpen_of_homogeneous_scheme_finite_set
    {k : Type u} [Field k] (G Y : Over (Spec (.of k))) [GrpObj G]
    [IsSeparated G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (a : G ⊗ Y ⟶ Y)
    (hone : ∀ (T : Over (Spec (.of k))) (y : T ⟶ Y),
      lift (1 : T ⟶ G) y ≫ a = y)
    (hmul : ∀ (T : Over (Spec (.of k))) (g h : T ⟶ G) (y : T ⟶ Y),
      lift g (lift h y ≫ a) ≫ a = lift (g * h) y ≫ a)
    (o : 𝟙_ (Over (Spec (.of k))) ⟶ Y) (q : G ⟶ Y)
    (hq : q = lift (𝟙 G) (toUnit G ≫ o) ≫ a)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (E : Set Y.left) (hE : E.Finite) :
    ∃ U : Y.left.Opens, IsAffineOpen U ∧ E ⊆ (U : Set Y.left) := by
  sorry

end AlgebraicGeometry
