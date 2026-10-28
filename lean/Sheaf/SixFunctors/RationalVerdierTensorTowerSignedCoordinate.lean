/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.CompletedPullbackTowerRealizations
public import Sheaf.Paper.FinitePullbackTensorBraiding
public import Sheaf.Paper.IntegralAmbientOperationModels

/-! # Signed interchange in the strict finite tensor tower

Source: Stacks 03EL, 06YL, 07A4 and 0941.
(blueprint: lem-coef-rational-verdier-tensor-tower-signed-coordinate). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Restrict the coherent chain braiding to its actual strict quotient tower and
transport through the fixed finite tensor comparisons. It is defined before
completion and does not use any ordinary-to-completed augmentation.
Source: Stacks 06YL, 07A4, 0941.
(blueprint: lem-coef-rational-verdier-tensor-tower-signed-coordinate). -/
def strictTensorSignedSwap
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (integralOperationsTensorTowerFunctor l E X).obj (P, Q) ⟶
      (integralOperationsTensorTowerFunctor l E X).obj (Q, P) :=
  (pullbackTensorTensorTower l E X P Q).inv ≫
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
        (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P)
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj Q)).hom) ≫
    (pullbackTensorTensorTower l E X Q P).hom

/-- At one finite quotient, scalar extension of a signed chain map agrees with
interchange of the two quotient tensor factors. This assertion concerns only
finite quotient complexes, without a mapping fibre or derived localization.

Source: Stacks 03EL, 06YL and 07A4; blueprint signed transposition paragraph.
(blueprint: lem-coef-rational-verdier-tensor-tower-signed-coordinate).

Proof: the normalized balanced-tensor comparison sends the quotient generator
of a homogeneous tensor x tensor y with coefficient a to (a tensor x) tensor
(1 tensor y). The coherent signed swap interchanges these factors and multiplies
by (-1)^(ij). Moving the degree-zero coefficient a between the two factors by
balancedness gives exactly the image of the signed ordinary generator. The two
maps agree on all such generators; sheafification and the direct-sum summand
inclusions detect equality. This also applies to zero sections and an empty site. -/
theorem tensor_tower_signed_coordinate
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (s : (constructibleTensorTotal l E X).obj (P, Q) ⟶
      (constructibleTensorTotal l E X).obj (Q, P))
    (hs : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u}
        X (completedIntegralCommRingSheafUnrestricted l E X) P Q i j U x y) =
        (i * j).negOnePow •
          (eqToHom (congrArg
            (fun k : ℤ ↦ ((constructibleTensorTotal l E X).obj (Q, P)).X k)
              (add_comm j i))).val.app U
            (IntegralHom.totalPair.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l E X) Q P j i U y x))
    (n : ℕ) :
    ((IntegralOnSlice.tower l E X none).map s).app (op n) ≫
        ((IntegralAmbient.tensorTowerIso l E X).hom.app (Q, P)).app (op n) =
      ((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q)).app (op n) ≫
        (strictTensorSignedSwap l E X P Q).app (op n) := by sorry

end WeilConjectures.RationalVerdier
