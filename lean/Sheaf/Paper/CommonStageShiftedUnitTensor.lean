/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Tensoring with a shifted common-stage coefficient unit

Source: Stacks Project, more-algebra.tex, section-sign-rules, item-shift-tensor,
and sites-cohomology.tex, Tags 06YY and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Right tensor with the shifted coefficient unit is naturally the shift functor.
Source: Stacks Project, more-algebra.tex, section-sign-rules, item-shift-tensor;
sites-cohomology.tex, Tags 06YY and 0941
(blueprint: lem-wf-common-stage-shifted-unit-tensor).

Proof: at each positive finite coefficient quotient choose a flat-term K-flat
representative P. The regular module in degree zero represents the tensor unit.
For its shift by r, the signed total-tensor comparison sends a degree-a tensor
p tensor 1 to (-1)^(a*r) p in P[r]. Its inverse has the same sign. The Leibniz
rule verifies the chain-map identities, and naturality holds degreewise for every
chain map. The resolving localization descends this natural isomorphism to all
derived arrows, including inverses of quasi-isomorphisms. The maps commute with
coefficient quotient maps. Derived inverse limit and its signed shift comparison
therefore give the completed integral comparison. The reduction-normalized unit
is pullbackTensorIntegralUnit, and its right unitor is the same multiplication
map. Rationalize these natural comparisons and extend them over finite coefficient
fields. Represent any common-stage arrow at one common larger field; tensor and
shift have their specified scalar conjugations, so the rational naturality square
is exactly the common-stage square after cancelling these conjugations. The unit
scalar comparison identifies the coefficient unit from its least stage at that
field. The resulting isomorphisms and their inverses define the displayed natural
isomorphism. This argument treats r=0, negative r, zero objects, empty schemes,
and arbitrary ramification by the identical formulas. -/
theorem commonStageShiftedUnit_tensor (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) [∀ x : X, Invertible (l : X.residueField x)] (r : ℤ) :
    Nonempty (Functor.prod' (𝟭 _) ((Functor.const _).obj
        ((shiftFunctor _ r).obj (pullbackTensorCommonUnit l Ω X))) ⋙
      commonStageDerivedTensor l Ω X ≅ shiftFunctor _ r) := by sorry

end WeilConjectures
