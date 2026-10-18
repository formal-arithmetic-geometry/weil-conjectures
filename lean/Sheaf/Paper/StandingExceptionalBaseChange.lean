/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.ChosenFixedCompactSupportExchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# Base change for the standing exceptional inverse image

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-purity-bc,
pur9-cs-def-bc, order 2360, with the reviewed etale-origin correction
(blueprint: pur9-cs-def-bc).

The arrow is the class-restricted transpose of the inverse compact-support exchange
followed by the pulled-back counit. The etale antecedent and its isomorphism are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- The base-change arrow b_{v,K} for the unconditional exceptional inverse image.
The source datum is K in D^b_ctf, with its specified bounded constructible etale
antecedent G for M=f^!K and alpha:nu_X^*G≅M. Both compactifications are arbitrary
fixed choices. The pulled-back antecedent and its isomorphism are constructed using
the canonical comparison square. The counit is the inverse Hom image of id_M.
The resulting arrow is the f' Hom image of (Ex^circ)^{-1} followed by v^* of that
counit. No ambient pro-etale exceptional adjunction is an input.
Source: blueprint main-20261015, pur9-cs-def-bc, both displayed formulas,
with the reviewed etale-origin formulation (blueprint: pur9-cs-def-bc). -/
def standingExceptionalBaseChange (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}}
    [X'.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [g'.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : ChosenCartesianSquare g' f' f g)
    (c : Compactification f) (cf' : Compactification f') :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  let hsq := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  letI : QuasiCompact f' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  let A := ModuleCat.{u + 1} P.Coefficient
  fun (R : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (adj : Etale.rightDerivedLowerShriekOfCompactification A c ⊣ R)
    (H : ComparisonClassAdjunction P.Coefficient f c R adj
      (DerivedCategory.plusEtaleOrigin A X) _root_.DerivedCategory.TStructure.t.plus)
    (R' : _root_.DerivedCategory (Sheaf Y'.smallEtaleTopology A) ⥤
      _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (adj' : Etale.rightDerivedLowerShriekOfCompactification A cf' ⊣ R')
    (H' : ComparisonClassAdjunction P.Coefficient f' cf' R' adj'
      (DerivedCategory.plusEtaleOrigin A X') _root_.DerivedCategory.TStructure.t.plus)
    (K : DerivedCategoryFiniteTor A Y)
    (G : Etale.DerivedCategoryBoundedConstructible A X)
    (alpha : (comparisonUpperStar A X).mapDerivedCategory.obj G.obj ≅
      ((comparisonLowerStar A Y).rightDerivedFunctor ⋙ R ⋙
        (comparisonUpperStar A X).mapDerivedCategory).obj K.obj) ↦
    let M := ((comparisonLowerStar A Y).rightDerivedFunctor ⋙ R ⋙
      (comparisonUpperStar A X).mapDerivedCategory).obj K.obj
    let hM := (DerivedCategory.plusEtaleOrigin A X).prop_of_iso alpha
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj G.property.1.1)
    let W : Scheme.FixedEtaleOriginWitness X P.Coefficient ⟨M, hM.plus⟩ :=
      ⟨⟨G.obj, G.property.1.1⟩, alpha⟩
    let G' := (Etale.upperStar A g').mapDerivedCategoryPlus.obj W.complex
    let alpha' := (sfDerivedComparisonPullbackIso P.Ring g').symm.app G.obj ≪≫
      (sfFixedDerivedPullback P.Ring g').mapIso W.iso
    let hM' := (DerivedCategory.plusEtaleOrigin A X').prop_of_iso alpha'
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj G'.property)
    let W' : Scheme.FixedEtaleOriginWitness X' P.Coefficient
        ⟨(sfFixedDerivedPullback P.Ring g').obj M, hM'.plus⟩ := ⟨G', alpha'⟩
    let theta := (H'.comparison (c.ofIsPullback hsq) cf').app
      ⟨(sfFixedDerivedPullback P.Ring g').obj M,
        (DerivedCategory.plusEtaleOrigin A X').prop_of_iso W'.iso
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj W'.complex.property)⟩
    let thetaL := (rightDerivedLowerShriekOfCompactification A (c.ofIsPullback hsq)).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory A g').app M) ≪≫ theta ≪≫
      (rightDerivedLowerShriekOfCompactification A cf').mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory A g').symm.app M)
    let exchange := fixedCompactSupportExchangeChosenComponent P.Coefficient hsq c cf' M thetaL
    letI := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app P.Coefficient
      hsq c M hM
    letI : IsIso exchange := inferInstanceAs (IsIso
      ((rightDerivedLowerShriekOfCompactificationBaseChangeMap A hsq c).app M ≫ thetaL.hom))
    let counit := (H.homEquiv c M hM K.obj K.property.plus).symm (𝟙 M)
    let pulledK := (upperStar A g).mapDerivedCategoryPlus.obj ⟨K.obj, K.property.plus⟩
    (H'.homEquiv cf' ((sfFixedDerivedPullback P.Ring g').obj M) hM'
      ((sfFixedDerivedPullback P.Ring g).obj K.obj) pulledK.property)
        ((rightDerivedLowerShriekOfCompactification A cf').map
            ((leftDerivedUpperStarIsoMapDerivedCategory A g').inv.app M) ≫
          (asIso exchange).inv ≫
          (leftDerivedUpperStarIsoMapDerivedCategory A g).hom.app
            ((rightDerivedLowerShriekOfCompactification A c).obj M) ≫
          (sfFixedDerivedPullback P.Ring g).map counit)

end AlgebraicGeometry.ProEtale
