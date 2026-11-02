/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison

/-! # The strict reduction/reindexing tensor equation

Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03EL, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option quotPrecheck false in
set_option hygiene false in
local notation "R[" W "]" =>
  (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "I[" g "]" =>
  (integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "F[" g "]" => podReindexingComplexFunctor l E g none
set_option quotPrecheck false in
set_option hygiene false in
local notation "T[" W "]" => PodReindexingCoherence.total l E W none
set_option quotPrecheck false in
set_option hygiene false in
local notation "S[" W "]" => coefficientTotalTensor.{u, u + 1, u}
  (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)

/-- Scalar-generator normalization implies the tensor equation before localization.
There are no derived-category maps, adjunction mates, or completion data in this
assertion. The three beta maps are tested independently by their unary formulas.
Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03EL, 07A4, 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).

Proof: apply the sequence inverse-image adjunction to the proposed equality.
Check each degree and each total summand on scalar pure tensors. The finite
component formula for tensorReductionStrictMap sends b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The systemChain unit formula sends a tensor
to the tensor of its two inverse-image units. The three Generators hypotheses
send the scalar to its reindexed scalar and leave x and y as the same sections
at the postcomposed object. Finally hPure sends x tensor y to that same tensor
at the reindexed object. Both composites therefore give the same two reduced
factors, with reindex(b) on the first and 1 on the second. The scalar balancing
relations, sheafification universal property and total-summand injections extend
the equality to every section and every degree. These are equalities of maps on
the sequence site, so they already contain every horizontal quotient transition.
No faithfulness of finite derived evaluations is invoked. The equations still
hold for zero factors and the empty site. -/
theorem strict_tensor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P Q : CochainComplex (scalarReductionSource l E Y) ℤ)
    (t : (F[g]).obj ((T[Y]).obj (P, Q)) ≅
      (T[X]).obj ((F[g]).obj P, (F[g]).obj Q))
    (hPure : ∀ (p q k : ℤ) (hk : p + q = k) (U : X.ProEt)
      (x : (P.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (Q.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      ((t.hom.f k).val.app (op U))
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology Y)
          (podReindexingRing l E Y none) P Q p q k hk
          (op ((proEtaleIsoPostcompose g).obj U)) x y) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (podReindexingRing l E X none) ((F[g]).obj P) ((F[g]).obj Q)
        p q k hk (op U) x y)
    (βP : (I[g]).obj ((R[Y]).obj P) ≅ (R[X]).obj ((F[g]).obj P))
    (βQ : (I[g]).obj ((R[Y]).obj Q) ≅ (R[X]).obj ((F[g]).obj Q))
    (βT : (I[g]).obj ((R[Y]).obj ((T[Y]).obj (P, Q))) ≅
      (R[X]).obj ((F[g]).obj ((T[Y]).obj (P, Q))))
    (hβP : Generators l E g P βP) (hβQ : Generators l E g Q βQ)
    (hβT : Generators l E g ((T[Y]).obj (P, Q)) βT) :
    (I[g]).map (tensorReductionStrictMap l E Y P Q) ≫
        (systemChain l E g).hom.app ((R[Y]).obj P, (R[Y]).obj Q) ≫
        (S[X]).map (Prod.mkHom βP.hom βQ.hom) =
      βT.hom ≫ (R[X]).map t.hom ≫
        tensorReductionStrictMap l E X ((F[g]).obj P) ((F[g]).obj Q) := by
  sorry

end WeilConjectures.PodReductionRepresentatives
