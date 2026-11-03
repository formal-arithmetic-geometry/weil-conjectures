/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncEtaleNaturalityLocalInverse

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

set_option linter.unusedVariables false in
/-- Component square of diagonal DNC etale naturality.
(blueprint: lem-pur-diagonal-dnc-etale-naturality). -/
theorem diagonalDncEtaleNaturality_twist (P : PurityFiniteSetting.{u})
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
    let b := B.hom
    let q :=
      (OrientationRefinement.pull P jO).map
          (OrientationCounit.localInverse P d f aY V C).hom ≫
        (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
        (T.mapIso (νU.mapIso B)).inv ≫
        (cv.app (P.diagonalOrdinaryDualizing g)).inv
    T.map (νU.map a) ≫
        (cv.app (P.diagonalTwistEtale Z d)).inv ≫
        (OrientationRefinement.pull P vO).map
          (OrientationCounit.localInverse P d g aY V E).hom =
      (cj.app (P.diagonalTwistEtale X d)).inv ≫ q := by
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
  have h := diagonalDncEtaleNaturality_localInverse P d f g aY V C E t N U j v w O jO vO
    hj hv
  dsimp only at h ⊢
  calc
    T.map (νU.map a) ≫
          (cv.app (P.diagonalTwistEtale Z d)).inv ≫
          (OrientationRefinement.pull P vO).map
            (OrientationCounit.localInverse P d g aY V E).hom =
        (cj.app (P.diagonalTwistEtale X d)).inv ≫
          m ≫ (OrientationRefinement.pull P vO).map
            (OrientationCounit.localInverse P d g aY V E).hom := by
      simp only [m, Category.assoc, Iso.inv_hom_id_assoc]
    _ = (cj.app (P.diagonalTwistEtale X d)).inv ≫
        ((OrientationRefinement.pull P jO).map
          (OrientationCounit.localInverse P d f aY V C).hom ≫
          (cj.app (P.diagonalOrdinaryDualizing f)).hom ≫
          (T.mapIso (νU.mapIso B)).inv ≫
          (cv.app (P.diagonalOrdinaryDualizing g)).inv) := by
      rw [h]

end WeilConjectures.PurityFiniteSetting
