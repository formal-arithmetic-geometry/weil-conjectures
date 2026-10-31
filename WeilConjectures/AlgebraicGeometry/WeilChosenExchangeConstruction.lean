/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilChosenDualityExchangeData

/-! # Normalized constructible Weil comparison data

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
thm-sf-verdier-exchange.proof.md Step 1, and lem-sf-tensor-hom.proof.md Step 1
(blueprint: lem-sf-weil-chosen-exchange-construction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
namespace WeilConjectures.WeilChosenDualityExchange
open PodConstructibleMate

/-- Construct the full Hom lifts, normalized constant pair, and specified composition
and projection isomorphisms. This assertion contains no exchange natural transformation,
no chosen structure adjoints, and no naturality assertion for the three transposes.
Source: cor-coef-verdier-weil-equivariance.proof.md, evaluation and dualizing paragraphs;
thm-sf-verdier-exchange.proof.md Step 1; lem-sf-tensor-hom.proof.md Step 1
(blueprint: lem-sf-weil-chosen-exchange-construction).

Proof:
1. On each of X, Y and the point, use integral constructible internal Hom and the
rational/common-stage object formulas to show every pair is permitted. Tensor and
pullback already have their recorded bounded constructible codomains. Compact support
preserves these domains by its integral constructibility and coefficient passage.
2. Use the evaluation-defined Frobenius Hom comparison. Give Hom(K,N) the structure
RHom(theta_K inverse,theta_N) after that comparison. Its naturality defines the Hom
bifunctor on pairs; the carrier object and map formulas are the original partial Hom.
3. Transpose the Weil equation for a pairing. Evaluation compatibility and cancellation
of theta_K identify it with the Weil equation for its transpose. This restricts both
inverse Hom bijections. Their naturality and triangles give the closed adjunction,
whose counit has precisely the original argument-first evaluation normalization.
4. Pullback of the constant coefficient unit at the model point has its canonical unit
comparison. Its unitor square is the tensor-unit coherence equation and gives Constant.
5. Lift the recorded compact-support composition using Frobenius composition coherence.
For the supplied W, its normalized support comparisons identify this with the same
carrier compositor; fiberCompositionCompactification supplies the base-change transport.
6. The projection formula is invertible for all field-coefficient second inputs. Its
Frobenius compatibility lifts it to the existing pair category with its actual carrier
compactSupportProjectionComponent. Package these constructions as Data, retaining the
Hom lift at the point as required. No data is chosen from arbitrary existence. -/
theorem weil_chosen_exchange_construction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (S : SixFunctorOperationDatum D C E 1 (Nat.le_refl 1))
    (W : CommonLifts D C S.closure.commonStage)
    (X Y : Models D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left]
    [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (cy : Compactification (structureMap D Y).hom.left)
    (cx : Compactification (f ≫ structureMap D Y).hom.left) :
    Nonempty (Data D C S.closure W X Y f cf cy cx) := by sorry

end WeilConjectures.WeilChosenDualityExchange
