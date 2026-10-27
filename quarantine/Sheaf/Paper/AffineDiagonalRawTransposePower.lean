/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions

/-! # Root-power compatibility of the raw ordered tower transpose

Source: smooth-purity, Agreement on the model, independence of the annihilating exponent.
(blueprint: lem-pur-affine-diagonal-raw-transpose-power).
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

/-- Root powers commute with the exceptional transpose of the raw ordered tower trace.
Only the base tower occurs: there is no coordinate presentation or dualizing base-change map.
Source: Agreement on the model, annihilator independence; ordered affine-space trace.
(blueprint: lem-pur-affine-diagonal-raw-transpose-power).

Proof: the monic root inclusion determines qB as the root-power map. The generator formula
fixes eB after scalar extension. Write N'=qN. The Kummer-sequence map has q-th power
on the middle G_m, identity on the right G_m, and qB on the roots. Its two squares
commute since Nq=N'. Naturality of the connecting morphism sends the N'-boundary
of a unit or Cartier transition function to its N-boundary. After scalar extension
this is exactly the supported coefficient Kummer class. Consequently the
projective-line decomposition commute with this map, acting by the shifted line map on its
first summand and identity on the Chern summand. Invert the decomposition and project to
the second summand to obtain trace compatibility. Naturality of the open counit restricts
it to the affine line. Iterate in coordinate order and paste compact-support comparisons.
The resulting source map on the tower coefficient is precisely c' followed by pullback of
the factorwise power comparison and then c inverse. Apply source naturality of the fixed
exceptional adjunction Hom bijection. The resulting adjunct equation is the one displayed.
At d=0 the tensor transition and ordered adjunction are identities. The empty base and
arbitrary ramified finite coefficients satisfy the same equations, without flatness. -/
theorem affineDiagonalRawTranspose_power (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (d r r' : ℕ) (hrr : r ≤ r')
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : P.Coefficient) = 0)
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
    let tr := (Etale.affineLinearCompactComparison N hN P.Coefficient hA B hB d).inv ≫
      Etale.affineTraceCounit P.Coefficient N hA t
        (Etale.ambientAffineTraceDatum N hN P.Coefficient hA) B hB d
    let tr' := (Etale.affineLinearCompactComparison N' hN' P.Coefficient hA' B hB' d).inv ≫
      Etale.affineTraceCounit P.Coefficient N' hA' t'
        (Etale.ambientAffineTraceDatum N' hN' P.Coefficient hA') B hB' d
    k ≫ (Etale.rightDerivedUpperShriekAdjunction
        (ModuleCat.{u + 1} P.Coefficient) p).homEquiv _ (𝟙_ _) tr =
      (Etale.rightDerivedUpperShriekAdjunction
        (ModuleCat.{u + 1} P.Coefficient) p).homEquiv _ (𝟙_ _) tr' := by sorry

end WeilConjectures.PurityFiniteSetting
