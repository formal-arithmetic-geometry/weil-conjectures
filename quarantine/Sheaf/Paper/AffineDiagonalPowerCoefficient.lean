/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions

/-! # Root-power coherence for the coefficient prefix

Source: smooth-purity, Agreement on the model, independence of the annihilating exponent.
(blueprint: lem-pur-affine-diagonal-power-coefficient).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback
  affineDiagonalPresentedTranspose affineDiagonalPowerComparison

/-- Normalized root powers commute with the coefficient prefix of a presented transpose.
This statement contains only coefficient pullback, descent and composition comparisons;
it contains no trace, integration, or exceptional inverse image.
Source: Agreement on the model, root/site comparisons in the annihilator clause.
(blueprint: lem-pur-affine-diagonal-power-coefficient).

Proof: the two kernel inclusion equations determine the power maps on U and B. Their
pullback square commutes because restriction of units preserves powers. On pure generators
the line comparisons therefore commute with normalized inverse image. The tensor pullback
comparison is natural in both factors, and shifts preserve these equalities. Induct on d:
at zero use naturality of the constant-unit pullback; at a successor tensor the induction
hypothesis with the shifted line square. This proves naturality of the base coefficient
pullback. Naturality of the inverse-image composition comparison transports the square
through the specified coordinate isomorphism. Conjugate the pulled-back base comparison
by the two coefficient descents c', c to obtain k. Cancelling the adjacent descent pairs
gives the stated prefix equation. No trace normalization enters; no permutation occurs.
The identity tensor in rank zero and all equalities over the empty base are included. -/
theorem affineDiagonalPower_coefficient (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r r' : ℕ) (hrr : r ≤ r')
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : P.Coefficient) = 0)
    (cU : U ≅ affineTraceTower B d) (hcU : cU.hom ≫ affineTraceProjection B d = f)
    (q : U.rootsOfUnitySheaf (P.coefficients.l ^ (r' + 1)) ⟶
      U.rootsOfUnitySheaf (P.coefficients.l ^ (r + 1)))
    (e : Scheme.finiteEtaleTateLine U (P.coefficients.l ^ (r' + 1)) P.Coefficient hA' ≅
      Scheme.finiteEtaleTateLine U (P.coefficients.l ^ (r + 1)) P.Coefficient hA)
    (hq : q ≫ kernel.ι ((P.coefficients.l ^ (r + 1)) • 𝟙 U.gmSheaf) =
      (P.coefficients.l ^ (r' + 1) / P.coefficients.l ^ (r + 1)) •
        kernel.ι ((P.coefficients.l ^ (r' + 1)) • 𝟙 U.gmSheaf))
    (he : ∀ (V : U.Etaleᵒᵖ) (a : P.Coefficient)
      (z : (U.rootsOfUnitySheaf (P.coefficients.l ^ (r' + 1))).obj.obj V),
      e.hom.hom.app V (Scheme.finiteEtaleTateOneGenerator P.Coefficient
        (P.coefficients.l ^ (r' + 1)) U hA' V a z) =
      Scheme.finiteEtaleTateOneGenerator P.Coefficient
        (P.coefficients.l ^ (r + 1)) U hA V a (q.hom.app V z))
    (qB : B.rootsOfUnitySheaf (P.coefficients.l ^ (r' + 1)) ⟶
      B.rootsOfUnitySheaf (P.coefficients.l ^ (r + 1)))
    (eB : Scheme.finiteEtaleTateLine B (P.coefficients.l ^ (r' + 1)) P.Coefficient hA' ≅
      Scheme.finiteEtaleTateLine B (P.coefficients.l ^ (r + 1)) P.Coefficient hA)
    (hqB : qB ≫ kernel.ι ((P.coefficients.l ^ (r + 1)) • 𝟙 B.gmSheaf) =
      (P.coefficients.l ^ (r' + 1) / P.coefficients.l ^ (r + 1)) •
        kernel.ι ((P.coefficients.l ^ (r' + 1)) • 𝟙 B.gmSheaf))
    (heB : ∀ (V : B.Etaleᵒᵖ) (a : P.Coefficient)
      (z : (B.rootsOfUnitySheaf (P.coefficients.l ^ (r' + 1))).obj.obj V),
      eB.hom.hom.app V (Scheme.finiteEtaleTateOneGenerator P.Coefficient
        (P.coefficients.l ^ (r' + 1)) B hA' V a z) =
      Scheme.finiteEtaleTateOneGenerator P.Coefficient
        (P.coefficients.l ^ (r + 1)) B hA V a (qB.hom.app V z)) :
    letI := P.noetherian aB
    let N := P.coefficients.l ^ (r + 1)
    let N' := P.coefficients.l ^ (r' + 1)
    let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
    let hN' := pow_pos P.coefficients.prime.out.pos (r' + 1)
    let t := Etale.ambientAffineTraceTransport N hN P.Coefficient hA
    let t' := Etale.ambientAffineTraceTransport N' hN' P.Coefficient hA'
    let hB := WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r
    let hB' := WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r'
    let p := affineTraceProjection B d
    let F := Etale.ordinaryFinitePullback P.Coefficient p
    let c := Etale.affineLinearCoefficientDescent P.Coefficient N hA t B hB d
    let c' := Etale.affineLinearCoefficientDescent P.Coefficient N' hA' t' B hB' d
    let k := c'.hom ≫ F.map (P.affineDiagonalPowerComparison B r r' hA hA' eB d).hom ≫ c.inv
    let E := Etale.ordinaryFinitePullback P.Coefficient cU.hom
    let preMap := (Etale.vectorIntegrationBaseCoefficientPullback
        P.Coefficient N hA t f hB d).inv ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        cU.hom p f hcU.symm).hom.app
          (Etale.affineLinearBaseCoefficient P.Coefficient N hA B d) ≫ E.map c.inv
    let preMapNext := (Etale.vectorIntegrationBaseCoefficientPullback
        P.Coefficient N' hA' t' f hB' d).inv ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        cU.hom p f hcU.symm).hom.app
          (Etale.affineLinearBaseCoefficient P.Coefficient N' hA' B d) ≫ E.map c'.inv
    (P.affineDiagonalPowerComparison U r r' hA hA' e d).hom ≫ preMap =
      preMapNext ≫ E.map k := by sorry

end WeilConjectures.PurityFiniteSetting
