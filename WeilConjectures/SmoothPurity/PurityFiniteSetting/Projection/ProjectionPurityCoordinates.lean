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

/-- The standard projection is smooth of the indicated pure relative dimension.
Source: polynomial charts; sbc-lem-affine-space-smooth
(blueprint: lem-pur-projection-purity-agreement).
Proof: the zero projection is the identity. Each successor adjoins one polynomial
variable and is smooth of pure dimension one. Relative dimensions add under
composition, giving dimension d, including the empty base. -/
theorem projection_smooth (Y : Scheme.{u}) (d : ℕ) :
    SmoothOfRelativeDimension d (iteratedAffineLineProj Y d) := by
  induction d with
  | zero => exact inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 Y))
  | succ d ih =>
    let := ih
    change SmoothOfRelativeDimension (d + 1)
      (lastProjection Y d ≫ iteratedAffineLineProj Y d)
    have h : SmoothOfRelativeDimension (1 + d)
        (lastProjection Y d ≫ iteratedAffineLineProj Y d) := by
      have hline : SmoothOfRelativeDimension 1 (lastProjection Y d) := by
        simpa using (inferInstance : SmoothOfRelativeDimension
          (Nat.card PUnit.{u + 1}) (lastProjection Y d))
      let := hline
      infer_instance
    simpa [Nat.add_comm] using h

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

/-- The recorded exceptional target of the smooth map.
Source: finite exceptional conventions (blueprint: lem-pur-projection-purity-agreement). -/
def projectionSmoothTarget (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C P.Coefficient Y)
    (d : ℕ) :=
  letI := (projection_geometry Y d).1
  (P.smoothPurityExceptionalOver (iteratedAffineLineProj Y d) aY).obj K

/-- The literal exceptional-coordinate map. At a positive rank it is identity;
at zero it is the ordinary exceptional identity comparison followed by the
comparison-adjunction counit, restricted later to the etale-origin class.
Source: exceptional identity normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionTargetRaw
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) :
    (d : ℕ) → Σ M N : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient (iteratedAffineLine Y d), M ⟶ N
  | 0 =>
    ⟨_, _,
      (ProEtale.VectorIntegrationSite.comparison (projectionSetting F C E n).Coefficient
        Y).map
          (((Etale.rightDerivedUpperShriekIsoOfIso
            (projectionSetting F C E n).Coefficient (Iso.refl Y)) ≪≫
              Etale.leftDerivedUpperStarId
                (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y).hom.app
                  ((ProEtale.comparisonLowerStar
                    (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient)
                      Y).rightDerivedFunctor.obj K)) ≫
        (ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y).counit.app K⟩
  | d + 1 =>
    letI := (projection_geometry Y (d + 1)).1
    letI := (projection_geometry Y (d + 1)).2
    ⟨_, _, 𝟙 (projectionSmoothTarget (projectionSetting F C E n) Y aY K (d + 1))⟩

/-- The common exceptional-coordinate map type.
Source: finite exceptional conventions (blueprint: lem-pur-projection-purity-agreement). -/
def ProjectionTargetMapType
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :=
  projectionSmoothTarget (projectionSetting F C E n) Y aY K d ⟶
    (AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptional
      (projectionSetting F C E n) Y d).obj K

/-- The raw exceptional normalization has the required source and target.
Source: the fixed finite exceptional functor and p_0=id
(blueprint: lem-pur-projection-purity-agreement).
Proof: at positive rank both definitions are nu* f^times Rnu_* at the same standing
compactification. The left-adjoint instances are propositions. At zero unfold the
identity exceptional functor; the raw comparison ends at K, the normalized target. -/
theorem projectionTargetMap_existsUnique
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ∃! t : ProjectionTargetMapType F C E n Y aY K d,
      HEq t (projectionTargetRaw F C E n Y aY K d).2.2 := by
  cases d with
  | zero =>
    unfold ProjectionTargetMapType
    unfold AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptional
    refine ⟨(projectionTargetRaw F C E n Y aY K 0).2.2, HEq.refl _, ?_⟩
    intro t ht
    exact eq_of_heq ht
  | succ d =>
    unfold ProjectionTargetMapType
    unfold AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptional
    refine ⟨(projectionTargetRaw F C E n Y aY K (d + 1)).2.2, HEq.refl _, ?_⟩
    intro t ht
    exact eq_of_heq ht

/-- The canonical exceptional-coordinate map, fixed independently of purity.
Source: identity and positive-rank normalization
(blueprint: lem-pur-projection-purity-agreement). -/
def projectionTargetMap
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : AlgebraicGeometry.ProEtale.AffineSpacePurity.C
      (projectionSetting F C E n).Coefficient Y) (d : ℕ) :
    ProjectionTargetMapType F C E n Y aY K d :=
  projectionChooseUnique (projectionTargetMap_existsUnique F C E n Y aY K d)

private theorem projectionCounit_isIso
    {B D : Type*} [Category B] [Category D] {L : B ⥤ D} {R : D ⥤ B}
    (adj : L ⊣ R) (M : B) (N : D) (e : L.obj M ≅ N)
    [IsIso (adj.unit.app M)] : IsIso (adj.counit.app N) := by
  have htri : IsIso (L.map (adj.unit.app M) ≫ adj.counit.app (L.obj M)) := by
    have hid : IsIso (𝟙 (L.obj M)) := inferInstance
    exact (adj.left_triangle_components M).symm ▸ hid
  have : IsIso (adj.counit.app (L.obj M)) :=
    IsIso.of_isIso_comp_left (L.map (adj.unit.app M)) _
  have hn : IsIso ((R ⋙ L).map e.hom ≫ adj.counit.app N) := by
    rw [adj.counit.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left ((R ⋙ L).map e.hom) _

/-- On the stated etale-origin class the target normalization is invertible.
Source: bounded site comparison and exceptional identity
(blueprint: lem-pur-projection-purity-agreement).
Proof: at positive rank the raw map is identity. At zero the ordinary exceptional
identity comparison is invertible. For bounded-below Ke the comparison unit is
invertible; the adjunction triangle therefore makes the counit invertible at nu*Ke.
Transport across eK gives invertibility at K, including zero and empty-scheme objects. -/
theorem projectionTarget_isIso
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅ K.obj) (d : ℕ) :
    IsIso (projectionTargetMap F C E n Y aY K.obj d) := by
  classical
  have ht : HEq (projectionTargetMap F C E n Y aY K.obj d)
      (projectionTargetRaw F C E n Y aY K.obj d).2.2 :=
    (projectionTargetMap_existsUnique F C E n Y aY K.obj d).exists.choose_spec
  cases d with
  | zero =>
    let hu := ProEtale.isIso_derivedComparisonAdjunction_unit_app
      (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y Ke hKe.1.1.1
    let hc := projectionCounit_isIso
      (ProEtale.derivedComparisonAdjunction
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y) Ke K.obj eK
    have hraw : IsIso (projectionTargetRaw F C E n Y aY K.obj 0).2.2 := by
      dsimp only [projectionTargetRaw]
      let e := (Etale.rightDerivedUpperShriekIsoOfIso
        (projectionSetting F C E n).Coefficient (Iso.refl Y) ≪≫
        Etale.leftDerivedUpperStarId
          (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y).app
        ((ProEtale.comparisonLowerStar
          (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y).rightDerivedFunctor.obj
            K.obj)
      let hm := (ProEtale.VectorIntegrationSite.comparison
        (projectionSetting F C E n).Coefficient Y).map_isIso e.hom
      exact IsIso.comp_isIso
    have he : projectionTargetMap F C E n Y aY K.obj 0 =
        (projectionTargetRaw F C E n Y aY K.obj 0).2.2 := eq_of_heq ht
    rw [he]
    exact hraw
  | succ d =>
    have he : projectionTargetMap F C E n Y aY K.obj (d + 1) =
        (projectionTargetRaw F C E n Y aY K.obj (d + 1)).2.2 := eq_of_heq ht
    rw [he]
    change IsIso (𝟙 _)
    infer_instance

/-- The existing ordered affine-line composite, in the smooth source and target
coordinates. The source and target comparisons use no orientation map.
Source: Gamma_(p_d,K) (blueprint: lem-pur-projection-purity-agreement). -/
def projectionAffineInPresentation
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring (projectionSetting F C E n)) Y)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient Y)
    (hKe : etaleFiniteTor (projectionSetting F C E n).Coefficient Y Ke)
    (eK : (ProEtale.VectorIntegrationSite.comparison
      (projectionSetting F C E n).Coefficient Y).obj Ke ≅ K.obj) (d : ℕ) :
    projectionSmoothSource (projectionSetting F C E n) Y K.obj d ⟶
      projectionSmoothTarget (projectionSetting F C E n) Y aY K.obj d :=
  letI : IsIso (projectionTargetMap F C E n Y aY K.obj d) :=
    projectionTarget_isIso F C E n Y aY K Ke hKe eK d
  (projectionSourceIso F C E n Y aY K.obj d).hom ≫
    affineSpacePurityComparison (projectionSetting F C E n) Y aY K Ke hKe eK d ≫
      inv (projectionTargetMap F C E n Y aY K.obj d)

/-- The Hom type on the original intrinsic pro-etale object, with the specified
smooth source and the transported exceptional target.
Source: displayed Hom in the item (blueprint: lem-pur-projection-purity-agreement). -/
def ProjectionIntrinsicHom (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) (d : ℕ) :=
  (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor.obj
    (projectionSmoothSource P Y
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) d) ⟶
  (Scheme.sfIntrinsicDerivedEquivalence (iteratedAffineLine Y d) P.Ring).functor.obj
    (projectionSmoothTarget P Y aY
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K) d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local semireducible] AlgebraicGeometry.ProEtale.AffineSpacePurity.exceptional

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end WeilConjectures.PurityFiniteSetting
