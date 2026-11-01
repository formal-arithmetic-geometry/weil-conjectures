/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionTensorOrdinaryData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionUnitIntegration
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionUnitTraceCoordinates
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.AffineBaseTraceExponent

/-! # The unit mate expressed using the ordered integration trace

Source: projection purity agreement, exponent normalization.
(blueprint: lem-pur-projection-unit-ordered-trace)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
open ProEtale ProEtale.AffineSpacePurity ProEtale.VectorIntegrationSite

/-- The independently defined unit integration is the ordinary adjunct of the
ordered integration trace pulled back along the inverse root transition.

Source: projection purity agreement, normalized projective-line integration.
(blueprint: lem-pur-projection-unit-ordered-trace)

Proof: affineBaseTrace_exponent gives Rf!(u) followed by the small-exponent
trace equal to the large-exponent trace. Precompose by Rf!(u inverse), then use
functoriality and the inverse-isomorphism equations. The result identifies the
small-exponent trace with the ordered trace after the inverse root map.
The recursive tower and projection pairs coincide by induction. Transport the
trace equation along that pair equality; the HEq specifications of ordinaryTrace
and projectionUnitIntegration pin both arrows. Finally take the ordinary adjunct
and its exact site comparison. This includes rank zero and empty schemes. -/
theorem projectionUnitIntegration_orderedTrace
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ) :
    let P := projectionSetting F C E n
    letI := (projection_geometry Y d).2
    letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
    let p := iteratedAffineLineProj Y d
    let u := projectionCoefficientRootIso F C E n (iteratedAffineLine Y d)
      (towerBase aY d) d
    projectionUnitIntegration P Y aY d =
      (comparison P.Coefficient (iteratedAffineLine Y d)).map
        ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient p).homEquiv _ _
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) p).map u.hom ≫
            ProEtale.AffineOrderedIntegration.ordinaryTrace P Y aY d)) ≫
      (P.diagonalDualizingComparison p).inv := by
  intro P
  let := (projection_geometry Y d).2
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  have hp : (⟨affineTraceTower Y d, affineTraceProjection Y d⟩ :
      Σ X : Scheme.{u}, X ⟶ Y) =
      ⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ :
            Σ X : Scheme.{u}, X ⟶ Y)) ih
  let := affineTraceNoetherian Y d
  have hr := affineBaseTrace_exponent C.l E n Y
    (AffineLinePurity.primeUnit P Y aY) n (n + 1) (Nat.le_succ n)
      P.diagonalExponent_annihilates (annihilates P) d
  let ur := projectionCoefficientRootIso F C E n (affineTraceTower Y d)
    ((affineTraceProjection Y d) ≫ aY) d
  have hu : projectionUnitTraceRaw P Y aY d =
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceProjection Y d)).map ur.hom ≫
          ProEtale.AffineOrderedIntegration.ordinaryTraceRaw P Y aY d := by
    change (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      (affineTraceProjection Y d)).map ur.inv ≫ projectionUnitTraceRaw P Y aY d =
        ProEtale.AffineOrderedIntegration.ordinaryTraceRaw P Y aY d at hr
    have h := congrArg (fun q ↦
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceProjection Y d)).map ur.hom ≫ q) hr
    exact ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      (affineTraceProjection Y d)).mapIso ur).hom_inv_id_assoc
        (projectionUnitTraceRaw P Y aY d) |>.symm.trans h
  have transport (X X' : Scheme.{u}) (f : X ⟶ Y) (g : X' ⟶ Y)
      [HasCompactification f] [HasCompactification g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ Y) = ⟨X', g⟩)
      (s : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
        (Etale.affineLinearBaseCoefficient P.Coefficient
          (ProEtale.AffineOrderedIntegration.exponent P) (annihilates P) X d) ⟶
            Etale.ordinaryFiniteUnit P.Coefficient Y)
      (s' : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) g).obj
        (Etale.affineLinearBaseCoefficient P.Coefficient
          (ProEtale.AffineOrderedIntegration.exponent P) (annihilates P) X' d) ⟶
            Etale.ordinaryFiniteUnit P.Coefficient Y) (hs : HEq s s') :
      HEq ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).map
          (projectionCoefficientRootIso F C E n X (f ≫ aY) d).hom ≫ s)
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) g).map
          (projectionCoefficientRootIso F C E n X' (g ≫ aY) d).hom ≫ s') := by
    cases h
    cases eq_of_heq hs
    rfl
  obtain ⟨t, ht, he⟩ := projectionUnitIntegration_trace P Y aY d
  have ho := (ProEtale.AffineOrderedIntegration.ordinaryTrace_existsUnique
    P Y aY d).exists.choose_spec
  have hu' := transport _ _ _ _ hp
    (ProEtale.AffineOrderedIntegration.ordinaryTraceRaw P Y aY d)
    (ProEtale.AffineOrderedIntegration.ordinaryTrace P Y aY d) ho.symm
  have ht' : t =
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
        (iteratedAffineLineProj Y d)).map
          (projectionCoefficientRootIso F C E n (iteratedAffineLine Y d)
            (towerBase aY d) d).hom ≫
      ProEtale.AffineOrderedIntegration.ordinaryTrace P Y aY d := by
    exact eq_of_heq (ht.trans ((heq_of_eq hu).trans hu'))
  rw [he, ht']
  rfl

end WeilConjectures.PurityFiniteSetting
