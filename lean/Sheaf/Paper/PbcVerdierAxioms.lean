/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.PbcCommonStageCones
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Sheaf.CategoryTheory.StageSystemVerdier

/-! # Verdier axioms for the specified common-stage triangles

Source: blueprint `thm-weil-pbc-verdier-axioms`, order 1540.
(blueprint: thm-weil-pbc-verdier-axioms)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
    [∀ i, HasShift (C i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]
    [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, HasZeroObject (C i)]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
    [∀ i, Pretriangulated (C i)]
    [stageTriangulated : ∀ i, IsTriangulated (C i)]
    [transitionExact : ∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]

/-- Finite-stage inclusions preserve the already recorded common-stage addition.
Source: blueprint order 1540, exact stage inclusion
(blueprint: thm-weil-pbc-verdier-axioms).
Proof: both included sums are represented by the transition image of the same
sum at the original stage. Additivity of the transitions makes this the sum of
the two included representatives; pairPreadditiveNormalized identifies the classes. -/
@[instance] theorem qbarStageInclusionAdditive (i : I) : (S.ι i).Additive := by
  sorry

/-- The actual transition identification commutes with the induced pair shift.
Source: blueprint order 1540, exact transition identifications
(blueprint: thm-weil-pbc-verdier-axioms).
Proof: the components of transIso are finite-stage identity maps with the
specified associators. Expand the induced pair shift on those representatives.
The associator CommShift equation identifies the two resulting arrows at the
same common stage, so their classes agree. This is precisely NatTrans.CommShift. -/
@[instance] theorem qbarTransIsoCommShift {i j : I} (h : i ≤ j) :
    NatTrans.CommShift (S.transIso h).hom ℤ := by
  sorry

/-- The recorded Verdier theorem uniquely fixes the pretriangulation by the
recorded CommonStageDistinguished predicate. Its data is the specified triangle
set; the inherited HasShift and Hom group structures are retained.
Source: blueprint order 1540 (blueprint: thm-weil-pbc-verdier-axioms). -/
instance qbarPairPretriangulated : Pretriangulated S.PairCategory :=
  (commonStage_verdier_existsUnique S).exists.choose

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The finite stage is triangulated for exactly its integral-image triangles.
Source: blueprint order 1540, finite-stage input (blueprint: thm-weil-pbc-verdier-axioms).
Proof: apply raw scalar-localization triangulation to the inherited integral
triangulation. Its normalized shift agrees with the published rational shift;
its image-triangle characterization is qbarStagePretriangulated_exists, which
specifies the same distinguished set. Transport TR4 along these identifications. -/
@[instance] theorem qbarStageTriangulated (E : Padic.FiniteCoefficientFields l Qbar) :
    IsTriangulated (pbcStageCategory l Qbar T E) := by
  sorry

/-- The prescribed coefficient tensor preserves the integral-image triangles.
Source: blueprint order 1540, exact finite-stage input
(blueprint: thm-weil-pbc-verdier-axioms).
Proof: on K-flat complexes integral tensor takes cone triangles to cone triangles.
It preserves the defining integral subcategories. The normalized localization
square therefore takes every integral image triangle to a target integral image
triangle, with the actual tensor shift comparison. Isomorphism closure gives
exactness on every distinguished rational triangle, including identity fields. -/
@[instance] theorem qbarScalarExtensionExact {E F : Padic.FiniteCoefficientFields l Qbar}
    (h : E ≤ F) : (pbcScalarExtension l Qbar T hDim.out hInv.out h).IsTriangulated := by
  sorry

/-- The actual common-stage triangulation satisfies all four Verdier axioms.
Source: blueprint order 1540 (blueprint: thm-weil-pbc-verdier-axioms).
Proof: apply commonStage_verdier_existsUnique to the actual completed integral
rational stages and their exact scalar transitions. Its proof moves finitely
many representatives and equations to one common stage: finite-stage TR1 gives
cones and identity triangles, TR2 gives signed rotation, and TR3 completes
commutative squares. Cone independence and finite-stage TR4 give the octahedron.
Its distinguished set is exactly CommonStageDistinguished by construction.
The same theorem gives exactness of the stage inclusions, and the specified
shift comparisons give qbarTransIsoCommShift for every transition identification. -/
theorem pbcVerdierAxioms :
    CategoryTheory.IsTriangulated (PbcFiniteStagePairCategory l Qbar T hDim.out hInv.out) ∧
    (∀ E : Padic.FiniteCoefficientFields l Qbar,
      ((pbcScalarSystem l Qbar T hDim.out hInv.out).ι E).IsTriangulated) ∧
    ∀ {E F : Padic.FiniteCoefficientFields l Qbar} (h : E ≤ F),
      NatTrans.CommShift ((pbcScalarSystem l Qbar T hDim.out hInv.out).transIso h).hom ℤ := by
  sorry

end AlgebraicGeometry.Scheme
