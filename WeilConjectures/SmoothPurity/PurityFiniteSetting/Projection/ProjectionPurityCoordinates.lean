/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerMap
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTensorCoordinates
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalBaseChangeCompared
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.PuritySectionInvariantIntrinsic
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Coordinates for comparison of the affine-space purity maps

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement (blueprint: lem-pur-projection-purity-agreement).
The comparison maps below change only coefficient, tensor and identity coordinates.

## Main declarations

* `projectionSourceIso` and `projectionTargetMap`: explicit normalized coordinates.
* `projectionAffineInPresentation`: the ordered affine map in the smooth coordinates.
* `ProjectionIntrinsicHom`: the common intrinsic source and target.
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
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AffineSpacePurity

/-- The source of the smooth comparison in fixed-scalar coordinates.
Source: the displayed Lp* K(d)[2d]
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothSource (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C P.Coefficient Y)
    (d : ℕ) :=
  (((smoothPurityTensor P.Coefficient (iteratedAffineLine Y d)).obj
    ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K)).obj
      ((P.diagonalTwist (iteratedAffineLine Y d) d)⟦-(2 * (d : ℤ))⟧))⟦2 * (d : ℤ)⟧

attribute [local irreducible] projectionTensorActionIso projectionTensorActionGeneric
  projectionTensorStep projectionLineIso projectionUnitRaw

/-- The literal canonical source-coordinate map, retaining its computed endpoints.
Source: tensor, shift, and identity normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionSourceRaw
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) :
    (d : ℕ) → Σ M N : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient (iteratedAffineLine Y d), M ≅ N
  | 0 => ⟨_, _,
    (projectionSetting F C E n).smoothPurityReassociation Y 0
      (((projectionSetting F C E n).smoothPurityPullback (𝟙 Y)).obj K) ≪≫
    projectionTensorActionIso F C E n Y aY _ 0 ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.upperStarId
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y) ≪≫
        Functor.mapDerivedCategoryIdIso _).app K⟩
  | d + 1 => ⟨_, _,
    (projectionSetting F C E n).smoothPurityReassociation (iteratedAffineLine Y (d + 1))
      (d + 1) (((projectionSetting F C E n).smoothPurityPullback
        (iteratedAffineLineProj Y (d + 1))).obj K) ≪≫
    projectionTensorActionIso F C E n (iteratedAffineLine Y (d + 1))
      (towerBase aY (d + 1)) _ (d + 1) ≪≫
    (action ((tensor (projectionSetting F C E n).Coefficient
      (iteratedAffineLine Y (d + 1))).flip.obj
        (shiftedLine (projectionSetting F C E n) (iteratedAffineLine Y (d + 1))))
      (d + 1)).mapIso
      (((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient)
          (iteratedAffineLineProj Y (d + 1))).app K).symm)⟩

/-- The common source-coordinate isomorphism type.
Source: purity source presentations (blueprint: lem-pur-projection-purity-agreement). -/
def ProjectionSourceIsoType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :=
  projectionSmoothSource (projectionSetting F C E n) Y K d ≅
    (orderedSource (projectionSetting F C E n) Y d).obj K

/-- The raw composite has exactly the recorded smooth and ordered affine endpoints.
The heterogeneous equality fixes its hom, so it cannot be chosen using a purity map.
Source: source presentations (blueprint: lem-pur-projection-purity-agreement).
Proof: unfold the two endpoints, the positive-level coefficient index, and orderedSource.
At zero, exact identity pullback, the tensor unit and zero shift give K. At a successor,
the exact/derived comparison followed by the ordered action gives orderedSource.
Transport the raw isomorphism along these endpoint equalities. Its hom is the specified
raw hom. Any two such isomorphisms have equal homs by transitivity of HEq, hence are equal. -/
theorem projectionSourceIso_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ∃! e : ProjectionSourceIsoType F C E n Y K d,
      HEq e (projectionSourceRaw F C E n Y aY K d).2.2 := by
  cases d with
  | zero =>
    unfold ProjectionSourceIsoType orderedSource
    refine ⟨(projectionSourceRaw F C E n Y aY K 0).2.2, HEq.refl _, ?_⟩
    intro e he
    exact eq_of_heq he
  | succ d =>
    unfold ProjectionSourceIsoType orderedSource twistAction
    refine ⟨(projectionSourceRaw F C E n Y aY K (d + 1)).2.2, HEq.refl _, ?_⟩
    intro e he
    exact eq_of_heq he

/-- The uniquely transported canonical source isomorphism, independent of either
purity arrow. Source: source-coordinate normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionSourceIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ProjectionSourceIsoType F C E n Y K d :=
  projectionChooseUnique (projectionSourceIso_existsUnique F C E n Y aY K d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local semireducible] AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptional

end WeilConjectures.PurityFiniteSetting
