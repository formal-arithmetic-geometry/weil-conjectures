/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.IntegralHomReductionModels
public import Sheaf.Paper.SfIntegralReductionTower

/-! # Ordinary tensor contraction for coefficient quotients

Source: Stacks Project, Modules on Sites, Tag 03CZ, and Cohomology on Sites,
Tag 07A4; the coefficient calculation in the integral Verdier proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Ordinary total tensor admits the scalar-first contraction for every quotient.

Source: Stacks 03CZ, lemma-adjointness-tensor-restrict, and 07A4,
lemma-pullback-tensor-product; the coefficient-unit calculation in
thm-coef-integral-verdier.proof.md.

Proof: in bidegree (i,j) use the balanced map
x tensor (s tensor y) ↦ s tensor (x tensor y). It is linear over the completed
coefficient ring and commutes with restriction maps. Sheafify the balanced maps
and sum over i+j=k. Both differentials act on x and y only; s is in degree zero,
so the two signed total differentials commute with these maps. This constructs
b for arbitrary complexes, with the displayed formula. For the last equation,
precompose with every total summand and both sheafification units. Both routes
send x tensor (s tensor y) to q(s) tensor (x tensor y), by the defining pure-tensor
formula of sfReductionTransition. Tensor induction, sheafification adjunction,
and coproduct extensionality give equality. No flatness or derived category
occurs, and exponent one, zero complexes, and the empty site cause no exception.
(blueprint: lem-sf-integral-ordinary-tensor-quotient-contraction). -/
theorem ordinaryTensorQuotient_contractions :
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let F := fun n : ℕ ↦ (sfReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)
    let T := totalTensor.{u, u} X R
    ∃ b : ∀ (P Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ),
        (T.obj P).obj ((F n).obj Q) ⟶ (F n).obj ((T.obj P).obj Q),
      (∀ (P Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ)
          (i j : ℤ) (U : X.ProEtᵒᵖ)
          (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
          (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        ((b P Q n).f (i + j)).val.app U
            (totalPair.{u, u} X R P ((F n).obj Q) i j U x
              (sfReductionTensor l E X n (Q.X j) U s y)) =
          sfReductionTensor l E X n (((T.obj P).obj Q).X (i + j)) U s
            (totalPair.{u, u} X R P Q i j U x y)) ∧
      ∀ (P Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ),
        (T.obj P).map
            ((NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app Q) ≫
            b P Q n =
          b P Q (n + 1) ≫
            (NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app
              ((T.obj P).obj Q) := by sorry

end WeilConjectures.IntegralHom
