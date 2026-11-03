/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedProperScalarNormalization
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedOpenScalarNormalization

/-! # Fixed-module normalization of the recorded intrinsic coefficient arrow

Source: Stacks Project, Tags 00YV, 03D3 and 0GL6, and Step 3 of
lem-sp-transported-compact-scalar-site-square. This is a comparison of the two
pro-etale presentations only; no etale input or boundedness is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] transportedRecordedReductionDirectImageComparison
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  sfIntrinsicModuleEquivalence scalarPresentation directImagePresentation
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  directImageScalarComparison reductionOpenScalarIso OpenScalarSite.scalarOpen
  supportPresentation FiniteCompactScalar.openRealizationIso
attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence
  Equivalence.mapDerivedCategory sfIntrinsicExtensionByZero
  proEtaleConstantRingMap scalarExtensionFunctor

set_option maxHeartbeats 600000 in
-- The pasted square elaborates several derived presentation and adjunction types.
end AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

private theorem supportPresentation_hom_app
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (supportPresentation A c).hom.app K =
      (directImageConstantPush A c.g).map
          ((FiniteCompactScalar.openRealizationIso A c.i).hom.app K) ≫
        (directImagePresentation A c.g).hom.app
          ((openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K) := by
  unfold supportPresentation FiniteCompactScalar.openRealizationIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
