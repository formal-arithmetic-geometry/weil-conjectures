/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.NormalizedErrorTowerData

/-! # Strict normalized coefficient-fiber triangles

Source: blueprint main-20261015, sk-lem-sp-tower, coefficient-fiber calculation
(blueprint: lem-sp-normalized-strict-tensor-fiber).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open MonoidalCategory CochainComplex SheafOfModules.TotalTensorSigns
open WeilConjectures
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
variable [HasDerivedCategory.{w} (spErrorModules l E T)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T)]

/-- The strict tensor-fiber triangle, its signed K-flat comparison, and normalized
reduction to a constant tower. This is the chain-level portion of the error-tower
argument; no derived inverse limit occurs in the conclusion.

Source: blueprint main-20261015, sk-lem-sp-tower, proof paragraph, coefficient-fiber
triangles and normalized transitions; Bhatt--Scholze, Lemmas 3.5.4--3.5.7
(blueprint: lem-sp-normalized-strict-tensor-fiber).

Proof. Form adjacent tensor maps by scalar restriction and the given semilinear
transitions. Sheafification extends the balanced section formulas uniquely, and the
cocycle equations give natural transformations. The balanced maps
x tensor (b tensor k) ↦ bx tensor k and x tensor k ↦ x tensor (1 tensor k)
are inverse chain maps identifying the middle terms. Tensor the rotated coefficient
cone triangles and use the tensor-cone comparison, identity on target summands and
(-1)^p on source summands. These formulas commute with coefficient reduction, hence
give a distinguished triangle of complexes of strict towers. Tensor the coefficient
fiber quasi-isomorphisms with each K-flat Q_n and use the signed shift comparison.
The normalized coefficient equation makes the resulting maps natural from the
powered shift tower. Exact evaluation detects their quasi-isomorphism. The maps
x tensor b ↦ b q_(n,m)(x) commute with transitions by the cocycle law and have the
assumed quasi-isomorphism property. Finally l^(m+1) annihilates B_m, and therefore
S_n; the powered transition over a gap m+1 is zero. This includes m=0, when the gap
is one; no division by l or boundedness of Q is used. -/
theorem sp_normalized_strict_tensor_fiber
    (Q : ∀ n : ℕ,
      CochainComplex (SheafOfModules.{max u (t + 1)} (spCoefficientRing l E T n)) ℤ)
    (q : SpErrorTransitions l E T Q)
    (hq_id : ∀ (n : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n).X p).val.obj U),
      spErrorTransitionValue l E T Q q n n le_rfl p U x = x)
    (hq_comp : ∀ (n k m : ℕ) (hkn : k ≤ n) (hmk : m ≤ k)
      (p : ℤ) (U : T.ProEtᵒᵖ) (x : ((Q n).X p).val.obj U),
      spErrorTransitionValue l E T Q q k m hmk p U
        (spErrorTransitionValue l E T Q q n k hkn p U x) =
      spErrorTransitionValue l E T Q q n m (hmk.trans hkn) p U x)
    (hflat : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
      (R := (spCoefficientCommRings l E T).obj (op n)) (Q n))
    (hnorm : ∀ (n m : ℕ) (h : m ≤ n),
      ∃ ρ : spErrorReduction l E T Q n m h ⟶ (spErrorRestrict l E T m).obj (Q m),
        SpErrorReductionFormula l E T Q q n m h ρ ∧ QuasiIso ρ)
    (m : ℕ)
    :
  ∃ (A : ℕᵒᵖ ⥤ CochainComplex (spErrorModules l E T) ℤ),
  ∃ (s : ∀ j : ℕ, spErrorReduction l E T Q (m + (j + 1)) m (by omega) ⟶
    spErrorReduction l E T Q (m + j) m (by omega)),
  ∃ (t : ∀ j : ℕ, spErrorMiddle l E T Q (m + (j + 1)) m ⟶
    spErrorMiddle l E T Q (m + j) m),
  ∃ (a : spErrorTailM l E T Q m t ⟶ spErrorTailS l E T Q m s),
  ∃ (left : A ⟶ spErrorTailM l E T Q m t),
  ∃ (ρ : spErrorTailS l E T Q m s ⟶
    (Functor.const ℕᵒᵖ).obj ((spErrorRestrict l E T m).obj (Q m))),
  ∃ (assoc : ∀ j : ℕ, spErrorCoefficientTensor l E T Q (m + j) m ≅
    spErrorMiddle l E T Q (m + j) m),
  ∃ (fiber : ∀ j : ℕ, spErrorFiberTensor l E T Q (m + j) m (by omega) ≅ A.obj (op j)),
  ∃ (η : spErrorPoweredShift l E T Q m s ⟶ A),
  /- s_formula -/
  (∀ (j : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + (j + 1))).X p).val.obj U)
      (b : (spCoefficientRing l E T m).obj.obj U),
    ((s j).f p).val.app U
        (spErrorReductionGenerator l E T Q (m + (j + 1)) m (by omega) p U x b) =
      spErrorReductionGenerator l E T Q (m + j) m (by omega) p U
        (spErrorTransitionValue l E T Q q (m + (j + 1)) (m + j) (by omega) p U x) b) ∧
  /- t_formula -/
  (∀ (j : ℕ) (p z : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + (j + 1))).X p).val.obj U)
      (k : ((principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
        (spCompletedScalar l E T l) m).X z).val.obj U),
    ((t j).f (p + z)).val.app U
        (spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
          ((spErrorRestrict l E T (m + (j + 1))).obj (Q (m + (j + 1))))
          (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
            (spCompletedScalar l E T l) m) p z U x k) =
      spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T (m + j)).obj (Q (m + j)))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p z U
            (spErrorTransitionValue l E T Q q (m + (j + 1)) (m + j) (by omega) p U x) k) ∧
  /- a_left -/
  (∀ (j : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + j)).X p).val.obj U),
    (((a.app (op j)).f (p + -1)).val.app U
      (spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T (m + j)).obj (Q (m + j)))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p (-1) U x
            (spErrorConeLeft (spErrorKoszulScalar l E T m) U
              (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)))) = 0) ∧
  /- a_right -/
  (∀ (j : ℕ) (p : ℤ) (U : T.ProEtᵒᵖ)
      (x : ((Q (m + j)).X p).val.obj U),
    (((a.app (op j)).f (p + 0)).val.app U
      (spErrorGenerator (completedIntegralCommRingSheafUnrestricted l E T)
        ((spErrorRestrict l E T (m + j)).obj (Q (m + j)))
        (principalKoszul (completedIntegralCommRingSheafUnrestricted l E T)
          (spCompletedScalar l E T l) m) p 0 U x
            (spErrorConeRight (spErrorKoszulScalar l E T m) U
              (1 : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)))) =
      spErrorGenerator ((spCoefficientCommRings l E T).obj (op (m + j))) (Q (m + j))
        ((CochainComplex.singleFunctor _ 0).obj
          (spRelativeCoefficient l E T (m + j) m (by omega))) p 0 U x
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          (spRelativeCoefficient l E T (m + j) m (by omega))).inv.val.app U
            (1 : (spCoefficientRing l E T m).obj.obj U))) ∧
  /- assoc_formula -/
  (∀ j : ℕ, SpErrorAssociativityFormula l E T Q (m + j) m (assoc j)) ∧
  /- fiber_transition_formula -/
  (∀ j : ℕ,
    SpErrorFiberTransitionFormula l E T Q q (m + (j + 1)) (m + j) m (by omega) (by omega)
      ((fiber (j + 1)).hom ≫ A.map (homOfLE (Nat.le_succ j)).op ≫ (fiber j).inv)) ∧
  /- distinguished -/
  (∃ δ,
    Triangle.mk
      ((DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ spErrorModules l E T)).map
        (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) left))
      ((DerivedCategory.Q.{w} (C := ℕᵒᵖ ⥤ spErrorModules l E T)).map
        (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) a)) δ ∈
      distTriang (DerivedCategory.{w} (ℕᵒᵖ ⥤ spErrorModules l E T))) ∧
  /- η_quasiIso -/
  (QuasiIso
    (koszulTowerComplexMap (completedIntegralCommRingSheafUnrestricted l E T) η)) ∧
  /- η_levelwise -/
  (∀ j : ℕ, QuasiIso (η.app (op j))) ∧
  /- reduction_formula -/
  (∀ j : ℕ,
    SpErrorReductionFormula l E T Q q (m + j) m (by omega) (ρ.app (op j))) ∧
  /- reduction_quasiIso -/
  (∀ j : ℕ, QuasiIso (ρ.app (op j))) ∧
  /- powered_chain_zero -/
  (∀ n : ℕ, ∃ (n' : ℕ) (h : n ≤ n'),
    (spErrorPoweredShift l E T Q m s).map (homOfLE h).op = 0) := by sorry

end AlgebraicGeometry.ProEtale
