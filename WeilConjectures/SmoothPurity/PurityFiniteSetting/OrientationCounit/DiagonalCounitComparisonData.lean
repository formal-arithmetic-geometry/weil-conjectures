/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalOrientationRefinement

/-! # The affine counit read on a diagonal DNC chart

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
thm-pur-diagonal-dualizing-object.proof.md, Steps 1--2 and canonicity paragraph.
(blueprint: def-pur-diagonal-counit-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
namespace OrientationCounit

/-- Canonical commutation of ordinary pullback with the site comparison.
Source: finite coefficient inverse image (blueprint: def-pur-diagonal-counit-comparison-data). -/
@[irreducible]
def comparisonPull (P : PurityFiniteSetting.{u}) {U X : Scheme.{u}} (j : U ⟶ X) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory ⋙
        OrientationRefinement.pull P j ≅
      Etale.ordinaryFinitePullback P.Coefficient j ⋙
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j) ≪≫
    ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) j ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) j).symm _

/-- Read the same restriction through the two sides of the open square.
Source: inverse-image composition (blueprint: def-pur-diagonal-counit-comparison-data). -/
@[irreducible]
def restriction (P : PurityFiniteSetting.{u}) {U X : Scheme.{u}}
    (j : U ⟶ X) (W : X.Opens) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory ⋙
        OrientationRefinement.pull P W.ι ⋙ OrientationRefinement.pull P (j ∣_ W) ≅
      Etale.ordinaryFinitePullback P.Coefficient j ⋙
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory ⋙
        OrientationRefinement.pull P (j ⁻¹ᵁ W).ι :=
  Functor.isoWhiskerLeft _
      ((ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) (j ∣_ W) W.ι).symm ≪≫
        ProEtale.leftDerivedUpperStarCongr
          (ModuleCat.{u + 1} P.Coefficient) (by simp) ≪≫
        ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) (j ⁻¹ᵁ W).ι j) ≪≫
    Functor.isoWhiskerRight (comparisonPull P j) _

/-- Convert the monoidal-unit dualizing presentation to the coefficient-unit one.
Source: exceptional inverse image (blueprint: def-pur-diagonal-counit-comparison-data). -/
def unitChange (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    Etale.dualizingComplex P.Coefficient f ≅
      P.diagonalOrdinaryDualizing f :=
  (Etale.rightDerivedUpperShriek P.Coefficient f).mapIso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).symm

/-- The coordinate counit transported back through source-etale locality.
Source: normalized affine trace (blueprint: def-pur-diagonal-counit-comparison-data). -/
@[irreducible]
def coordinate (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k))
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ affineTraceTower Y d) [Etale v] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ affineTraceProjection Y d = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ affineTraceProjection Y d)] :
    (Etale.ordinaryFinitePullback P.Coefficient j).obj (P.diagonalTwistEtale X d) ⟶
      (Etale.ordinaryFinitePullback P.Coefficient j).obj (P.diagonalOrdinaryDualizing f) := by
  letI := affineTraceNoetherian Y d
  exact
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t v
        (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) d) d).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient v).map
      (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) ≫
    (P.diagonalEtaleLocality N v (affineTraceProjection Y d)).hom ≫
    (P.diagonalDualizingCongr w).hom ≫ (P.diagonalEtaleLocality N j f).inv

/-- Read a target-open restriction on any open of the coordinate scheme.
The square is specified by its actual arrows and commutativity equation.
Source: inverse-image composition
(blueprint: def-pur-diagonal-counit-comparison-data). -/
@[irreducible]
def restrictionAlong (P : PurityFiniteSetting.{u}) {U X : Scheme.{u}}
    (j : U ⟶ X) (W : X.Opens) (O : U.Opens) (k : O.toScheme ⟶ W.toScheme)
    (hk : k ≫ W.ι = O.ι ≫ j) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory ⋙
        OrientationRefinement.pull P W.ι ⋙ OrientationRefinement.pull P k ≅
      Etale.ordinaryFinitePullback P.Coefficient j ⋙
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory ⋙
        OrientationRefinement.pull P O.ι :=
  Functor.isoWhiskerLeft _
      ((ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) k W.ι).symm ≪≫
        ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) hk ≪≫
        ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) O.ι j) ≪≫
    Functor.isoWhiskerRight (comparisonPull P j) _

/-- The inverse four-factor DNC orientation, with coefficient-unit endpoints.
Source: diagonal-dualizing proof, Steps 1--3
(blueprint: def-pur-diagonal-counit-comparison-data). -/
@[irreducible]
def localInverse (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] [HasCompactification f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (V : Y.affineOpens) (C : OrientationRefinement.Chart P f aY d V) :
    (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
            (P.diagonalTwistEtale X d)) ≅
      (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
            (P.diagonalOrdinaryDualizing f)) :=
  OrientationRefinement.tate P (f ⁻¹ᵁ V.1).ι (f ≫ aY) d ≪≫
    (OrientationRefinement.theta P f aY d V C.geometry C.betaEtale).symm ≪≫
    (OrientationRefinement.pull P (f ⁻¹ᵁ V.1).ι).mapIso
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso (unitChange P f))

end OrientationCounit

end WeilConjectures.PurityFiniteSetting
