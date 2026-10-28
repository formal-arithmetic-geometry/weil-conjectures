module

public import Sheaf.Paper.OrderedAffineTransposeProjection
public import Sheaf.Paper.FiniteForwardProductSymmetry
public import Sheaf.Paper.BaseChangedLineTraceEvaluation
public import Sheaf.Paper.RelativeKunneth
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.AffineLineCompositeTranspose

/-! # Binary factorization of the actual affine-space exceptional transpose

Source: current blueprint sec-smooth-purity/sk-prop-an, Integration paragraph,
and the expanded ordered trace argument (blueprint: def-pur-affine-space-binary-trace-coordinates).

The integration is the published actual exceptional transpose, not a recursively chosen map.
The supplied binary isomorphism is pinned to the native forward compact-support product.
The imported construction data are recorded by def-pur-ordered-affine-trace-data,
def-pur-finite-forward-product, def-pur-normalized-line-trace-base-change and
def-pur-compared-coefficient-left-unitor; their theorem modules supply the existing data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpaceTrace
open AffineLinePurity AffineSpacePurity VectorIntegrationSite OrderedAffineTranspose

/-- Pullback of the ordered shifted Tate power, including the pullback of the unit.
Source: canonical Tate pullback in the Integration paragraph
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def pullTate (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (inverseImage (Ring P) f).obj ((twistAction P Y d).obj (unit (Ring P) Y)) ≅
      (twistAction P X d).obj (unit (Ring P) X) := by
  unfold twistAction
  exact actionPullbackIso
    ((tensor (Ring P) Y).flip.obj (shiftedLine P Y))
    ((tensor (Ring P) X).flip.obj (shiftedLine P X)) (inverseImage (Ring P) f)
    (fun M ↦ inverseImageTensorIso (Ring P) f M (shiftedLine P Y) ≪≫
      tensorIso (Ring P) X (Iso.refl _) (shiftedLinePullback P f aY))
    (unit (Ring P) Y) d ≪≫
    (action ((tensor (Ring P) X).flip.obj (shiftedLine P X)) d).mapIso
      (unitPull (Ring P) f)

/-- Append one shifted Tate factor, cancelling the coefficient unit in that factor.
Source: T_m boxtimes T_1 = T_(m+1), with its ordered tensor and shift identifications
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def appendTate (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) (W : C A X) (d : ℕ) :
    ((tensor A X).obj ((action ((tensor A X).flip.obj W) d).obj (unit A X))).obj
      (((tensor A X).obj (unit A X)).obj W) ≅
    (action ((tensor A X).flip.obj W) (d + 1)).obj (unit A X) :=
  ((tensor A X).obj ((action ((tensor A X).flip.obj W) d).obj (unit A X))).mapIso
    (AffineLineEvaluation.comparedLeftUnit (ModuleCat.{u + 1} A) X W)

/-- The ordered external coefficient product on the literal Cartesian last-coordinate square.
Source: T_m boxtimes T = T_(m+1) in the Integration paragraph
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def externalTate (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u}) (d : ℕ) :=
  ((tensor (Ring P) (iteratedAffineLine Y (d + 1))).obj
    ((inverseImage (Ring P) (lastProjection Y d)).obj (tate P Y d))).obj
    ((inverseImage (Ring P) (AffineSpace.map PUnit.{u + 1} (iteratedAffineLineProj Y d))).obj
      (tate P Y 1))

/-- The canonical product identification, in coordinate order m followed by the last factor.
Source: the canonical twist, shift and pullback identifications of the binary product
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def externalTateIso (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) :
    externalTate P Y d ≅ tate P Y (d + 1) := by
  have e := tensorIso (Ring P) (iteratedAffineLine Y (d + 1))
    (pullTate P (lastProjection Y d) (towerBase aY d) d)
    (pullTate P (AffineSpace.map PUnit.{u + 1} (iteratedAffineLineProj Y d))
      (towerBase aY 1) 1)
  have e' := appendTate (Ring P) (iteratedAffineLine Y (d + 1))
      (shiftedLine P (iteratedAffineLine Y (d + 1))) d
  unfold twistAction at e
  unfold externalTate tate twistAction
  exact e ≪≫ e'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified native forward binary product. Its factors are tensor symmetry,
projection, tensor symmetry, compact-support exchange, projection and the normalized
compact-support compositor, followed only by the canonical Tate identification.
Source: thm-sf-kunneth-relative's explicit relative product construction
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def binaryForward (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ)
    (h : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
      (iteratedAffineLine Y (d + 2)) (externalTate P Y (d + 1))) :
    ((tensor (Ring P) Y).obj ((compact P Y (d + 1)).obj (tate P Y (d + 1)))).obj
      ((compact P Y 1).obj (tate P Y 1)) ⟶
        (compact P Y (d + 2)).obj (tate P Y (d + 2)) := by
  letI compactM := (projection_geometry Y (d + 1)).2
  letI compactOne := (projection_geometry Y 1).2
  have sq : IsPullback (lastProjection Y (d + 1))
      (AffineSpace.map PUnit.{u + 1} (iteratedAffineLineProj Y (d + 1)))
      (iteratedAffineLineProj Y (d + 1)) (iteratedAffineLineProj Y 1) := by
    simpa only [iteratedAffineLineProj, iteratedAffineLine, lastProjection,
      Category.comp_id] using (AffineSpace.isPullback_map (n := PUnit.{u + 1})
        (iteratedAffineLineProj Y (d + 1))).flip
  letI : HasCompactification
      (AffineSpace.map PUnit.{u + 1} (iteratedAffineLineProj Y (d + 1))) :=
    HasCompactification.of_isPullback sq
  letI : QuasiCompact
      (AffineSpace.map PUnit.{u + 1} (iteratedAffineLineProj Y (d + 1))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  let e := sq.w.symm.trans (iteratedAffineLineProj_succ Y (d + 1)).symm
  letI compactNext := (projection_geometry Y (d + 2)).2
  letI : HasCompactification
      (AffineSpace.map PUnit.{u + 1} (iteratedAffineLineProj Y (d + 1)) ≫
        iteratedAffineLineProj Y 1) :=
    HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 2)) e.symm
  exact finiteForwardProduct (Ring P) sq (tate P Y (d + 1)) (tate P Y 1) h ≫
    (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (Ring P)) e).hom.app _ ≫
    (compact P Y (d + 2)).map (externalTateIso P Y aY (d + 1)).hom

/-- Pin the supplied kappa to the inverse of the specified relative product.
The existential is only the origin proof needed to evaluate its canonical compositor.
Source: kappa_(m,1) in the Integration paragraph
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def BinaryProductSpecified (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ)
    (κ : (compact P Y (d + 2)).obj (tate P Y (d + 2)) ≅
      ((tensor (Ring P) Y).obj ((compact P Y (d + 1)).obj (tate P Y (d + 1)))).obj
        ((compact P Y 1).obj (tate P Y 1))) : Prop :=
  ∃ h : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Ring P))
    (iteratedAffineLine Y (d + 2)) (externalTate P Y (d + 1)),
    κ.inv = binaryForward P Y aY d h

/-- The trace base-change equation for any map of separated finite-type k-schemes.
All operation-domain instances follow from the two structure maps and the over-k equation.
Source: the universal base-change hypothesis in the Integration paragraph
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def LineBaseChangeEquation (P : WeilConjectures.PurityFiniteSetting.{u})
    {X B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (v : X ⟶ B) (hv : v ≫ aB = aX) : Prop := by
  letI : IsNoetherian B := isNoetherian_of_locallyOfFiniteType aB
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  letI : QuasiCompact v := inferInstance
  letI : LocallyOfFiniteType (v ≫ aB) := hv.symm ▸ inferInstance
  letI : QuasiCompact (v ≫ aB) := hv.symm ▸ inferInstance
  exact BaseChangedLineTrace.TraceCompatible (Ring P) (P.coefficients.l ^ (P.level + 1))
    (annihilates P) v (BaseChangedLineTrace.trace P P.level (annihilates P) B aB)
    (BaseChangedLineTrace.normalizedPulledTrace P v P.level (annihilates P) aB)

/-- Base change of normalized integration over every separated finite-type base over Y,
including identity base change, with the canonical unit and Tate pullback identifications.
Source: the iterated base-change assumption in the Integration paragraph
(blueprint: def-pur-affine-space-binary-trace-coordinates). -/
def UniversalLineBaseChange (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k)) : Prop :=
  ∀ (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (b : B ⟶ Y) (_hb : b ≫ aY = aB)
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    (v : X ⟶ B) (hv : v ≫ aB = aX), LineBaseChangeEquation P aB aX v hv

end AlgebraicGeometry.ProEtale.AffineSpaceTrace
