/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.PbcCommonStageCones

/-! # Compatibility and independence of common-stage cone triangles

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
`prop-weil-pbc-cone-independence`; Stacks Project, Tags 014B and 014A.
(blueprint: prop-weil-pbc-cone-independence)

The assertion is packaged over the existing stage-system interface to keep its
formulas readable. The theorem specializes it to the recorded concrete PBC system,
with its actual categories, tensor transitions, associators and normalized shifts.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w v u c
open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]

/-- The scalar-extended cone with endpoints identified by the specified associators.
Its first arrow is transport of the representative, and its last arrow includes sigma.
Source: blueprint main-20261015, cone independence, first sentence
(blueprint: prop-weil-pbc-cone-independence). -/
def transportedCone {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (hr : r.k ≤ N) (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧) : Triangle (C N) :=
  Triangle.mk (S.tr hr r.u)
    ((S.assoc r.hY hr).inv.app Y.obj ≫ (S.T hr).map g)
    ((S.T hr).map h ≫ ((S.T hr).commShiftIso (1 : ℤ)).hom.app _ ≫
      (shiftFunctor (C N) (1 : ℤ)).map ((S.assoc r.hX hr).hom.app X.obj))

variable [∀ i, Preadditive (C i)] [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]
  [HasShift S.PairCategory ℤ] [∀ i, (S.ι i).CommShift ℤ]

/-- The four clauses of common-stage cone independence, for the specified stage system.
This is an assertion, not an additional choice of cones or of comparison maps.
Source: blueprint main-20261015, cone independence, all four sentences
(blueprint: prop-weil-pbc-cone-independence). -/
structure ConeIndependenceSpec : Prop where
  /-- Scalar extension and the endpoint associators identify a distinguished cone
  with a distinguished cone of exactly the transported arrow. -/
  scalarExtension : ∀ {X Y : S.PairCategory} (r : PairCategory.Rep X Y)
    {N : I} (hr : r.k ≤ N) (Z : C r.k) (g : Y.toStage r.hY ⟶ Z)
    (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧),
    Triangle.mk r.u g h ∈ distTriang (C r.k) →
      transportedCone S r hr Z g h ∈ distTriang (C N) ∧
        ∃ e : (S.T hr).mapTriangle.obj (Triangle.mk r.u g h) ≅
            transportedCone S r hr Z g h,
          e.hom.hom₁ = (S.assoc r.hX hr).hom.app X.obj ∧
            e.hom.hom₂ = (S.assoc r.hY hr).hom.app Y.obj ∧ e.hom.hom₃ = 𝟙 _
  /-- Equal pair morphisms have distinguished cones isomorphic at an agreement field. -/
  representatives : ∀ {X Y : S.PairCategory} (r s : PairCategory.Rep X Y),
    PairCategory.mkHom r.k r.hX r.hY r.u = PairCategory.mkHom s.k s.hX s.hY s.u →
    ∀ (Z : C r.k) (g : Y.toStage r.hY ⟶ Z) (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
      (Z' : C s.k) (g' : Y.toStage s.hY ⟶ Z')
      (h' : Z' ⟶ (X.toStage s.hX)⟦(1 : ℤ)⟧),
    Triangle.mk r.u g h ∈ distTriang (C r.k) →
    Triangle.mk s.u g' h' ∈ distTriang (C s.k) →
      ∃ (Q : I) (hr : r.k ≤ Q) (hs : s.k ≤ Q), S.tr hr r.u = S.tr hs s.u ∧
        ∃ e : transportedCone S r hr Z g h ≅ transportedCone S s hs Z' g' h',
          e.hom.hom₁ = 𝟙 _ ∧ e.hom.hom₂ = 𝟙 _
  /-- Two distinguished cones of one finite-stage arrow are isomorphic fixing endpoints. -/
  finiteStage : ∀ (M : I) {A B Z Z' : C M} (f : A ⟶ B)
    (g : B ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧) (g' : B ⟶ Z') (h' : Z' ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk f g h ∈ distTriang (C M) →
    Triangle.mk f g' h' ∈ distTriang (C M) →
      ∃ e : Triangle.mk f g h ≅ Triangle.mk f g' h',
        e.hom.hom₁ = 𝟙 A ∧ e.hom.hom₂ = 𝟙 B
  /-- Replacement preserves the pair cone fixing endpoints and every distinguishedness
  witness, in both directions. -/
  witnesses : ∀ {X Y : S.PairCategory} (r s : PairCategory.Rep X Y),
    PairCategory.mkHom r.k r.hX r.hY r.u = PairCategory.mkHom s.k s.hX s.hY s.u →
    ∀ (Z : C r.k) (g : Y.toStage r.hY ⟶ Z) (h : Z ⟶ (X.toStage r.hX)⟦(1 : ℤ)⟧)
      (Z' : C s.k) (g' : Y.toStage s.hY ⟶ Z')
      (h' : Z' ⟶ (X.toStage s.hX)⟦(1 : ℤ)⟧),
    Triangle.mk r.u g h ∈ distTriang (C r.k) →
    Triangle.mk s.u g' h' ∈ distTriang (C s.k) →
      (∃ e : commonStageCone S X Y r.k r.hX r.hY Z r.u g h ≅
          commonStageCone S X Y s.k s.hX s.hY Z' s.u g' h',
        e.hom.hom₁ = 𝟙 X ∧ e.hom.hom₂ = 𝟙 Y) ∧
      (∀ D : Triangle S.PairCategory,
        Nonempty (D ≅ commonStageCone S X Y r.k r.hX r.hY Z r.u g h) ↔
        Nonempty (D ≅ commonStageCone S X Y s.k s.hX s.hY Z' s.u g' h'))

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

/-- Common-stage cones in the actual PBC coefficient system are independent of the
representative, common field and chosen distinguished cone, in all four specified senses.
Source: blueprint main-20261015, cone independence; Stacks Tags 014B and 014A
(blueprint: prop-weil-pbc-cone-independence).
Proof:
1. Exactness from prop-weil-pbc-scalar-extension makes the mapped triangle, with
   its sigma last arrow, distinguished. Replace its endpoints by A_X and A_Y;
   the three squares give the required isomorphism, and TR1 preserves distinguishedness.
2. For one finite-stage arrow, TR3 extends the identity square; the third
   component is invertible by lem-sf-triangle-morphism-iso (Stacks 014A).
3. The equality criterion of prop-weil-pbc-common-stage-calculus supplies a
   finite agreement field Q. Apply Steps 1 and 2 there to compare the cones.
4. Identify each original pair cone with its extension at Q. The cone comparison
   is represented by identity at Q. Shift-associator coherence identifies the
   third-arrow representatives, including the sigma inverse of commonStageCone.
5. Represent the Step 3 cone isomorphism and its inverse at Q, and compose with
   the Step 4 comparisons. This gives a pair-triangle isomorphism fixing endpoints.
6. Compose any distinguishedness witness with this isomorphism or its inverse.
   Thus the witnesses in def-weil-pbc-common-stage-cones are interchangeable. -/
theorem pbcConeIndependence (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    StageSystem.ConeIndependenceSpec (pbcScalarSystem l Ω T hDim.out hInv.out) := by
  sorry

end AlgebraicGeometry.Scheme
