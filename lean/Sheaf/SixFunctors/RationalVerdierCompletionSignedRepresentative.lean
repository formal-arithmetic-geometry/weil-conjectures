/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.SixFunctors.RationalVerdierModels
public import Sheaf.Paper.DerivedPullbackTensorConstraints

/-! # The signed completion square on good cochain representatives

Source: blueprint thm-coef-rational-verdier, paragraph 3, signed transposition.
(blueprint: lem-coef-rational-verdier-completion-signed-representative). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

/-- The ambient completed swap is the strict-system signed swap transported through
its recorded completed tensor model. This construction uses no constructibility or
choice of ordinary tensor presentation.
Source: Stacks 06YL and 08TC; blueprint signed transposition paragraph.
(blueprint: lem-coef-rational-verdier-completion-signed-representative). -/
def completedSignedSwap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    integralCompletedTensor l E X ≅ pullbackTensorSwap _ ⋙ integralCompletedTensor l E X :=
  (pullbackTensorIntegralTensorModel l E X) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((pullbackTensorCalculus l E X).reduction.prod
          (pullbackTensorCalculus l E X).reduction)
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (pullbackTensorCalculus l E X).systemClosed
          (pullbackTensorCalculus l E X).systemTensorModel))
      (coefficientSequenceLimit l E X) ≪≫
    Functor.isoWhiskerLeft (pullbackTensorSwap _)
      (pullbackTensorIntegralTensorModel l E X).symm

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- On two flat-term K-flat complexes, the quotient-normalized completion map
intertwines a chain map with the Koszul pure-section formula and the actual ambient
completed signed swap. No ordinary derived presentation, datum, naturality hypothesis,
constructibility, scalar extension or inverse completion map occurs in this assertion.
Source: Stacks 06YL, 08TC; blueprint thm-coef-rational-verdier paragraph 3.
(blueprint: lem-coef-rational-verdier-completion-signed-representative).

Proof: the homogeneous formula determines s by the pure tensor generators and the
summand inclusions of direct-sum totalization. At every positive quotient the same
formula determines the strict-system braiding. The quotient coordinate of completion
sends x tensor y to their two quotient images, hence intertwines these signed swaps;
the coefficient sign is (-1)^(ij) on both sides. The shifted mapping-fiber coordinate
of completion is zero on both sides. The two mapping-fiber coordinates, and then all
product projections, jointly detect equality. The equalities commute with the strict
quotient transitions, so they give the whole Roos complex square. Localize this square;
the recorded tensor-model comparisons and reduction/limit adjunction identify its
completed side with completedSignedSwap. Zero complexes and the empty site obey the
same generator and zero-coordinate equations. -/
theorem completion_signed_representative
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (s : (constructibleTensorTotal l E X).obj (P.obj, Q.obj) ⟶
      (constructibleTensorTotal l E X).obj (Q.obj, P.obj))
    (hs : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.obj.X i).val.obj U) (y : (Q.obj.X j).val.obj U),
      (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u}
        X (completedIntegralCommRingSheafUnrestricted l E X) P.obj Q.obj i j U x y) =
        (i * j).negOnePow •
          (eqToHom (congrArg
            (fun k : ℤ ↦ ((constructibleTensorTotal l E X).obj (Q.obj, P.obj)).X k)
              (add_comm j i))).val.app U
            (IntegralHom.totalPair.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l E X) Q.obj P.obj j i U y x)) :
    DerivedCategory.Q.map s ≫
        DerivedCategory.Q.map ((completionChain D l hl X E).app (Q.obj, P.obj)) =
      DerivedCategory.Q.map ((completionChain D l hl X E).app (P.obj, Q.obj)) ≫
        (integralCompletedTensorComparison l E X).inv.app (P, Q) ≫
        (completedSignedSwap l E X).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (Q, P) := by sorry

end WeilConjectures.RationalVerdier
