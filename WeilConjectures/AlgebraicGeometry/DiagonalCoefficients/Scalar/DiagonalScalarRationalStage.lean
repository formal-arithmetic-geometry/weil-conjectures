/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback
import all WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientTracePullback
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientClassPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalBaseSquares
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarClosedSourceExchange
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedPullbackScalarNormalization

/-! # A step of diagonal scalar pullback propagation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
attribute [local instance 20000] ProEtale.sheafBraidedCategory ProEtale.sheafMonoidalCategory
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal SymmetricCategory.ofCurried

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory CondensedRing.upperStar CondensedRing.lowerStar
  upperStarFromPoint upperStarFromPointComp monoidal_upperStarFromPoint
  monoidal_pointUpperStar oplaxMonoidal_pointUpperStar
  CondensedRing.upperStarLowerStarAdjunction
  ProEtale.upperStar ProEtale.lowerStar ProEtale.upperStarLowerStarAdjunction
  ProEtale.upperStarComp

private theorem scalar_comparison_eq
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    scalarPullbackComparison a f = (CondensedRing.derivedPullIso a f).hom := by
  have h := CondensedRing.mateEquiv_derivedPullIso_hom a f
  have he : (CondensedRing.derivedComapLeftDerivedUpperStarIso a f).hom =
      (scalarRestrictionPullbackIso a f).inv := by
    simp only [CondensedRing.derivedComapLeftDerivedUpperStarIso,
      scalarRestrictionPullbackIso, CondensedRing.derivedComapUpperStarIso,
      CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc]
  rw [he] at h
  let e := mateEquiv (G := derivedUpper R f) (H := derivedUpper T f)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
  exact congrArg TwoSquare.natTrans ((e.symm_apply_eq).mpr h.symm)

private theorem scalar_endpoint_square
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules R S} {N : Modules R X} {M' : Modules T S} {N' : Modules T X}
    {v : M.X ⟶ M'.X} {v' : N.X ⟶ N'.X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    {m' : (upperStar Ab.{u + 1} f).obj M'.X ⟶ N'.X}
    (p : PullEndpoint R f M N m) (e : Endpoint a M M' v)
    (e' : Endpoint a N N' v') (p' : PullEndpoint T f M' N' m')
    (h : (upperStar Ab.{u + 1} f).map v ≫ m' = m ≫ v') :
    ScalarPullbackEndpointSquare a f p e e' p' := by
  constructor
  rw [scalar_comparison_eq]
  exact RationalP1.endpoint_pull_square_shift a f e e' p p' h

private def canonical_endpoints
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (L : ∀ X : Scheme.{u}, Modules R X)
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (p : PullEndpoint R (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP)
    (w : PullEndpoint R (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW) :
    PullbackEndpoints R g L mP mW :=
  ⟨RationalP1.nativeUnitPullEndpoint R g, RationalP1.nativeUnitPullEndpoint R (baseP g), p, w⟩

set_option maxHeartbeats 1000000 in
-- Normalize the canonical supported map against the fixed endpoint instances.
private def canonical_source_pullback
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (L : ∀ X : Scheme.{u}, Modules R X)
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (p : PullEndpoint R (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP)
    (w : PullEndpoint R (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW) :
    SourcePullback R g L mP mW := by
  haveI := diagonalScalar_source_map_isIso R g (diagonalBaseSquares g)
    (canonical_endpoints R g L p w).cP
  exact {
    geometry := diagonalBaseSquares g
    endpoints := canonical_endpoints R g L p w
    supported := asIso (sourcePullbackMap R g (diagonalBaseSquares g).diagonal_square
      (canonical_endpoints R g L p w).cP)
    supported_normalization := rfl }

attribute [local irreducible] canonical_source_pullback

private def scalar_pullback
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsNoetherian Y] [IsNoetherian Y']
    {L₀ : ∀ X : Scheme.{u}, Modules R X} {L : ∀ X : Scheme.{u}, Modules T X}
    {v : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L X).X}
    {d₀ : Diagram R Y L₀} {d₀' : Diagram R Y' L₀}
    {d : Diagram T Y L} {d' : Diagram T Y' L}
    {m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X}
    {m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X}
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (old : PullbackCompatibility R g L₀ d₀ d₀' m₀P m₀W)
    (scalar : ScalarCompatibility a Y L₀ L v d₀ d)
    (scalar' : ScalarCompatibility a Y' L₀ L v d₀' d')
    (p : PullEndpoint T (baseP g) (L (ProjectiveLine Y)) (L (ProjectiveLine Y')) mP)
    (w : PullEndpoint T (baseW g) (L (diagonalSurface Y)) (L (diagonalSurface Y')) mW)
    (hp : (upperStar Ab.{u + 1} (baseP g)).map (v (ProjectiveLine Y)) ≫ mP =
      m₀P ≫ v (ProjectiveLine Y'))
    (hw : (upperStar Ab.{u + 1} (baseW g)).map (v (diagonalSurface Y)) ≫ mW =
      m₀W ≫ v (diagonalSurface Y')) :
    PullbackCompatibility T g L d d' mP mW := by
  let s := canonical_source_pullback T g L p w
  have hP := scalar_endpoint_square a (baseP g) old.sourceData.endpoints.lineP
    scalar.lineP scalar'.lineP s.endpoints.lineP hp
  have hW := scalar_endpoint_square a (baseW g) old.sourceData.endpoints.lineW
    scalar.lineW scalar'.lineW s.endpoints.lineW hw
  have hs := diagonalSupported_pullbackScalarNormalization a g L₀ L m₀P m₀W mP mW
    old.sourceData s (scalar.units (ProjectiveLine Y))
    (scalar'.units (ProjectiveLine Y')) scalar.supported scalar'.supported
  refine ⟨s, (diagonal_scalar_paste_generic a g old scalar scalar' s hW hs).comm,
    ?_, ?_, ?_⟩
  · exact scalar_trace_transfer a _ _ _ _ _
      d₀.Rq d₀'.Rq d.Rq d'.Rq
      d₀.q_canonical d₀'.q_canonical d.q_canonical d'.q_canonical
      d₀.q_unit d₀'.q_unit d.q_unit d'.q_unit
      old.sourceData.endpoints.lineP s.endpoints.lineP
      old.sourceData.endpoints.cY s.endpoints.cY
      (scalar.units Y) (scalar'.units Y') scalar.lineP scalar'.lineP hP
      d₀.traceq d₀'.traceq d.traceq d'.traceq old.traceq scalar.q scalar'.q
  · exact scalar_trace_transfer a _ _ _ _ _
      d₀.R₁ d₀'.R₁ d.R₁ d'.R₁
      d₀.p₁_canonical d₀'.p₁_canonical d.p₁_canonical d'.p₁_canonical
      d₀.p₁_unit d₀'.p₁_unit d.p₁_unit d'.p₁_unit
      old.sourceData.endpoints.lineW s.endpoints.lineW
      old.sourceData.endpoints.cP s.endpoints.cP
      (scalar.units (ProjectiveLine Y)) (scalar'.units (ProjectiveLine Y'))
      scalar.lineW scalar'.lineW hW
      d₀.trace₁ d₀'.trace₁ d.trace₁ d'.trace₁ old.trace₁ scalar.p₁ scalar'.p₁
  · exact scalar_trace_transfer a _ _ _ _ _
      d₀.R₂ d₀'.R₂ d.R₂ d'.R₂
      d₀.p₂_canonical d₀'.p₂_canonical d.p₂_canonical d'.p₂_canonical
      d₀.p₂_unit d₀'.p₂_unit d.p₂_unit d'.p₂_unit
      old.sourceData.endpoints.lineW s.endpoints.lineW
      old.sourceData.endpoints.cP s.endpoints.cP
      (scalar.units (ProjectiveLine Y)) (scalar'.units (ProjectiveLine Y'))
      scalar.lineW scalar'.lineW hW
      d₀.trace₂ d₀'.trace₂ d.trace₂ d'.trace₂ old.trace₂ scalar.p₂ scalar'.p₂

attribute [local irreducible] scalar_pullback derivedUpper derivedLower derivedScalars
  singlePullback
attribute [local semireducible] ProEtale.upperStar
attribute [local irreducible] RationalP1.adicComparison

set_option maxHeartbeats 1000000 in
-- Epic cancellation identifies the supplied map with the normalized natural map.
private theorem rational_line_square (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) {X S : Scheme.{u}} (f : X ⟶ S)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : S, Invertible (l : S.residueField x)]
    (roots : CartesianAdicComparison l f) :
    (upperStar Ab.{u + 1} f).map (rationalLineMap l E S) ≫ roots.rational E =
      spIntegralComparison f l E ≫ rationalLineMap l E X := by
  have h : roots.rational E = (RationalP1.adicComparison l f).rational E := by
    apply (cancel_epi ((upperStar Ab.{u + 1} f).map
      (Mod.extendπ (padicIntegersToPadicSubfield S l E) (spIntegralTwist S l E)))).1
    exact (roots.rational_scalar E).trans ((RationalP1.adicComparison l f).rational_scalar E).symm
  rw [h]
  exact RationalP1.rational_root_scalar_square l E f

set_option maxHeartbeats 2000000 in
-- Check the scalar construction with its fixed endpoint instances.
/-- Propagate geometric diagonal pullback from integral coefficients to rational
coefficients, using the prescribed rational root comparisons.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), localization.
(blueprint: lem-diagonal-scalar-rational-stage).

Proof: For each E, extension from O_E to E is flat, hence the scalar/pullback mate
is the derivedPullIso. CartesianAdicComparison supplies the ordinary line endpoints.
Precompose rational_scalar with the extension unit: naturality of that unit and the
normalized tensor pullback comparison give the scalar/line endpoint square.
Construct normalized source pullback using closed-source exchange. The supported
scalar normalization gives its endpoint square. Paste the class square using
naturality and cancel its source isomorphism. For q, p1 and p2, the scalar exchange
cube and unit normalization transport the integral trace square, using toRational's
comparison_iso fields to cancel. All maps are the prescribed comparisons; no choice
of a different rational line comparison or trace is made. The result is independent
of the supplied Z_l record, which only fixes the compatible family parameters. -/
theorem diagonalScalar_rational_stage
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : ProjectiveLine Y', Invertible (l : (ProjectiveLine Y').residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    [∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x)]
    (family : Family l Y) (family' : Family l Y')
    (rootsP : CartesianAdicComparison l (baseP g))
    (rootsW : CartesianAdicComparison l (baseW g))
    (zl : PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
      (zlLine l) family.zl family'.zl
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l)))
    (hi : (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
        (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
        (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)))) :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (PullbackCompatibility (Profinite.continuousMapRingObj.{u} E.1) g
        (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E)
        (rootsP.rational E) (rootsW.rational E))) := by
  classical
  let _ := zl
  intro E
  let a := padicIntegersRingObjToContinuousMapRingObj l E
  let : ∀ S : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap a S)) :=
    fun S ↦ preservesFiniteLimits_extendScalars_padicIntegersToPadicSubfield l E S
  exact ⟨scalar_pullback a g (hi E).some (family.toRational E) (family'.toRational E)
    (RationalP1.cartesianPullEndpoint (Profinite.continuousMapRingObj.{u} E.1) (baseP g)
      (spRationalTwist (ProjectiveLine Y) l E)
      (spRationalTwist (ProjectiveLine Y') l E) (rootsP.rational E)
      ((rootsP.integral_rational_cartesian E).2))
    (RationalP1.cartesianPullEndpoint (Profinite.continuousMapRingObj.{u} E.1) (baseW g)
      (spRationalTwist (diagonalSurface Y) l E)
      (spRationalTwist (diagonalSurface Y') l E) (rootsW.rational E)
      ((rootsW.integral_rational_cartesian E).2))
    (rational_line_square l E (baseP g) rootsP) (rational_line_square l E (baseW g) rootsW)⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
