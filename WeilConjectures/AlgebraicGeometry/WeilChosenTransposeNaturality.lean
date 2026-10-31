/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilChosenDualityExchangeData

/-! # Naturality of the normalized Weil transpose chain

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
thm-sf-verdier-exchange.proof.md Step 1, and lem-sf-tensor-hom.proof.md Step 1
(blueprint: lem-sf-weil-chosen-transpose-naturality).
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

/-- Contravariant naturality of the specified exceptional, tensor-Hom, ordinary
transpose chain, for every target pair. Only this chain is asserted; no chosen structure
adjoints, dualizing comparison, or final exchange transformation occurs in the statement.
Source: lem-sf-tensor-hom.proof.md, naturality of the chain in Steps 1--2
(blueprint: lem-sf-weil-chosen-transpose-naturality).

Proof:
1. Write A_M=Hom(FM,omega) and a=Hom(Fu,1) for u:M to N. The carrier formulas and
evaluation normalization in HomLift identify its evaluation with the recorded closed
structure. Evaluation dinaturality says that tensor(1,a) followed by evaluation at FM
is tensor(Fu,1) followed by evaluation at FN. This holds on carriers and hence on pairs.
2. The projection_carrier normalization identifies projection with the specified natural
projection formula. Naturality of its inverse and step 1 show b_M after F(1 tensor P(a))
equals b_N after F(u tensor 1), where b is inverse projection followed by evaluation.
3. Apply the exceptional Hom bijection and its source naturality to this equality.
The equality now compares the two exceptional transposes on M tensor P(A_N).
4. Apply tensor-Hom transposition. Its first-variable naturality follows from the same
normalized evaluation dinaturality, by injectivity of the inverse Hom bijection.
Naturality in the tensor parameter handles P(a). Thus the resulting equality compares
a followed by the transpose at M with the transpose at N followed by Hom(u,1).
5. Apply the ordinary Hom bijection, natural on source and target. This gives the
stated square for transposeComponent. All equalities take place in the pair categories:
their forgetful functors are faithful, and the restricted bijections preserve their
original carrier maps. No invertibility of transposeComponent is needed. -/
theorem weil_chosen_transpose_naturality
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
    (cx : Compactification (f ≫ structureMap D Y).hom.left)
    (d : Data D C S.closure W X Y f cf cy cx) (omega : Pair D C Y)
    {M N : (Pair D C X)ᵒᵖ} (v : M ⟶ N) :
    ((W.supportFunctor f cf (geometricCompactification D f cf)).op ⋙
        (Functor.curry.obj d.homY.hom).flip.obj omega).map v ≫
        transposeComponent
          (exceptionalAdjunction W f cf (geometricCompactification D f cf))
          (ordinaryAdjunction W f)
          (Functor.curry.obj (W.tensorFunctor X)) (Functor.curry.obj (W.tensorFunctor Y))
          d.homX.hom d.homY.hom d.homX.closed d.homY.closed d.projection omega N.unop =
      transposeComponent
          (exceptionalAdjunction W f cf (geometricCompactification D f cf))
          (ordinaryAdjunction W f)
          (Functor.curry.obj (W.tensorFunctor X)) (Functor.curry.obj (W.tensorFunctor Y))
          d.homX.hom d.homY.hom d.homX.closed d.homY.closed d.projection omega M.unop ≫
        ((Functor.curry.obj d.homX.hom).flip.obj
            ((W.exceptionalFunctor f cf (geometricCompactification D f cf)).obj omega) ⋙
          W.directFunctor f).map v := by sorry

end WeilConjectures.WeilChosenDualityExchange
