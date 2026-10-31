/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncEtaleBeta
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncEtaleDualizing

/-! # Local inverse square for diagonal DNC etale naturality

This is the local-inverse part of the component square.  The coefficient
pullback is first transported through the two restriction comparison
isomorphisms; the remaining assertion is the compatibility of the local
inverse with the transported dualizing comparison.
(blueprint: lem-pur-diagonal-dnc-etale-naturality-twist-square-local-inverse).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Local inverse compatibility obtained by pasting two squares at the actual normal
section object. Source: diagonal-dualizing proof Steps 1--2 and final canonicity paragraph.
Factor the local inverse as Tate restriction followed by inverse beta, followed by
inverse delta, alpha, inverse rho and the unit comparison. Apply the beta square
and then the DNC/dualizing square; reassociate the composite. All the geometric
compatibility assumptions are confined to these two separate squares.
(blueprint: lem-pur-diagonal-dnc-etale-naturality-twist-square-local-inverse). -/
theorem diagonalDncEtaleNaturality_localInverse (P : PurityFiniteSetting.{u})
    {X Z Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    [IsNoetherian X] [IsNoetherian Z] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification g]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens)
    (C : OrientationRefinement.Chart P f aY d V)
    (E : OrientationRefinement.Chart P g aY d V)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ Z) [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ g = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ g)]
    (O : U.Opens) (jO : O.toScheme ⟶ (f ⁻¹ᵁ V.1).toScheme)
    (vO : O.toScheme ⟶ (g ⁻¹ᵁ V.1).toScheme)
    (hj : jO ≫ (f ⁻¹ᵁ V.1).ι = O.ι ≫ j)
    (hv : vO ≫ (g ⁻¹ᵁ V.1).ι = O.ι ≫ v) :
    let νU := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
    let T := OrientationRefinement.pull P O.ι
    let cj := OrientationCounit.restrictionAlong P j (f ⁻¹ᵁ V.1) O jO hj
    let cv := OrientationCounit.restrictionAlong P v (g ⁻¹ᵁ V.1) O vO hv
    let a :=
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit (g ≫ aY)) d).inv
    let B := (P.diagonalEtaleLocality N v g) ≪≫
      (P.diagonalDualizingCongr w) ≪≫ (P.diagonalEtaleLocality N j f).symm
    let m := (cj.app (P.diagonalTwistEtale X d)).hom ≫
      T.map (νU.map a) ≫
      (cv.app (P.diagonalTwistEtale Z d)).inv
    m ≫ (OrientationRefinement.pull P vO).map
          (OrientationCounit.localInverse P d g aY V E).hom =
      (OrientationRefinement.pull P jO).map
          (OrientationCounit.localInverse P d f aY V C).hom ≫
        (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
        (T.mapIso (νU.mapIso B)).inv ≫
        (cv.app (P.diagonalOrdinaryDualizing g)).inv := by
  have hβ := diagonalDncEtaleNaturality_beta P d f g aY V C E t U j v w O jO vO hj hv
  have hδ := diagonalDncEtaleNaturality_dncDualizing P d f g aY V C.geometry E.geometry N U j v w
    O jO vO hj hv
  dsimp only at hβ hδ ⊢
  rw [DiagonalEtaleComparison.localInverse_factors P d f aY V C,
    DiagonalEtaleComparison.localInverse_factors P d g aY V E]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  have h := congrArg
    (fun k => k ≫ (OrientationRefinement.pull P vO).map
      (DiagonalEtaleComparison.normalToDualizing P d g aY V E.geometry).hom) hβ
  simp only [Category.assoc] at h
  rw [hδ] at h
  simpa only [Functor.map_comp, Category.assoc] using h

end WeilConjectures.PurityFiniteSetting
