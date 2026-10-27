/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions
import Sheaf.Paper.AffineDiagonalRawTransposePower
import Sheaf.Paper.AffineDiagonalPowerCoefficient

/-! # Root-power compatibility of the presented integration transpose

Source: smooth-purity, Agreement on the model, independence of the annihilating exponent.
(blueprint: lem-pur-affine-diagonal-transpose-power).
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

private lemma transpose_power_transport {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {K L : D} {X X' Y : C} {W : D}
    (a : K ⟶ L) (p : L ⟶ F.obj X) (p' : K ⟶ F.obj X')
    (k : X' ⟶ X) (z : X ⟶ Y) (z' : X' ⟶ Y) (b : F.obj Y ⟶ W)
    (hp : a ≫ p = p' ≫ F.map k) (hz : k ≫ z = z') :
    a ≫ (p ≫ F.map z ≫ b) = p' ≫ F.map z' ≫ b := by
  rw [← Category.assoc a p, hp]
  simp only [Category.assoc, ← F.map_comp_assoc, hz]

/-- A normalized root-power comparison commutes with the presented exceptional transpose.
Source: Agreement on the model, annihilator independence, with the prescribed ordered trace.
(blueprint: lem-pur-affine-diagonal-transpose-power).

Proof: the normalized finite Tate exponent comparison supplies qB and eB on the base.
Apply the coefficient-prefix compatibility theorem to the supplied q,e on U and qB,eB on B.
Apply the raw ordered-transpose compatibility theorem with qB,eB. In the defining formula
for the presented transpose, substitute the prefix equation, combine the adjacent pullback
maps, substitute the raw transpose equation, and append the same dualizing base-change mate.
The private categorical transport lemma proves exactly this pasting calculation. The zero
rank and empty base are covered by the two step statements; no orientation scalar is chosen.
Neither root comparison existence on U nor the integration equation is asserted here. -/
theorem affineDiagonalTranspose_powerCompatible (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r r' : ℕ) (hrr : r ≤ r')
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : P.Coefficient) = 0)
    (c : U ≅ affineTraceTower B d) (hc : c.hom ≫ affineTraceProjection B d = f)
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
        (P.coefficients.l ^ (r + 1)) U hA V a (q.hom.app V z)) :
    (P.affineDiagonalPowerComparison U r r' hA hA' e d).hom ≫
      P.affineDiagonalPresentedTranspose d f aB r hA c hc =
        P.affineDiagonalPresentedTranspose d f aB r' hA' c hc := by
  let := P.noetherian aB
  let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpower⟩ :=
    (Scheme.finiteEtaleTwistPullbackData P.Coefficient
      (P.coefficients.l ^ (r + 1)) hN hA).laws
  obtain ⟨qB, lineB, hqB, heB, _⟩ := hpower
    (P.coefficients.l ^ (r' + 1))
    (pow_pos P.coefficients.prime.out.pos (r' + 1))
    (pow_dvd_pow _ (Nat.add_le_add_right hrr 1)) B
    (WeilConjectures.PurityConventions.coefficientPower_isUnit P B aB r')
  have hp := P.affineDiagonalPower_coefficient d f aB r r' hrr hA hA' c hc
    q e hq he qB (lineB 1) hqB heB
  have hz := P.affineDiagonalRawTranspose_power B aB d r r' hrr hA hA'
    qB (lineB 1) hqB heB
  unfold affineDiagonalPresentedTranspose
  simpa only [Category.assoc, Etale.ordinaryFinitePullback] using
    transpose_power_transport
    (Etale.ordinaryFinitePullback P.Coefficient c.hom)
    (P.affineDiagonalPowerComparison U r r' hA hA' e d).hom _ _ _ _ _
    (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_horiz_isIso ⟨hc.trans (Category.comp_id f).symm⟩)) hp hz

end WeilConjectures.PurityFiniteSetting
