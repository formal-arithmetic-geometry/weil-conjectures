module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.Paper.FiniteTateSiteDescent
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.DegreeZeroDerivedMapGluing
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.Paper.FiniteSiteCoordinates
public import Sheaf.Paper.ProEtaleOrderedIntegration
public import Sheaf.Paper.ProEtaleFrameIntegration
public import Sheaf.Paper.ProEtaleVectorIntegration
public import Sheaf.AlgebraicGeometry.VectorProjectiveCompletion
import Sheaf.Paper.CompactSupportExchangeTransport
import Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent
import Sheaf.CategoryTheory.DerivedDegreeZeroNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence


/-! # Frame descent of finite-coefficient vector integration

Source: main-20261015, sec-smooth-purity/sk-prop-an,
def-amb-vector-integration.proof.md; Stacks Tags 06XS, 03EM and 04TQ.
(blueprint: lem-pur-vector-frame-integration-site-descent).

The sources below use the root-normalized comparison presentation of the finite Tate
coefficient and the ordered shifted tensor presentation. Compactification changes are
explicit, so the projective completion and the named integration have the same meaning.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v uB vB wB
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite


local notation3 "Γₛ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace X)))).obj
    (Opposite.op (α := Scheme.Opens _) U)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- Noetherianity on every open of a Noetherian base, including nonaffine overlaps.
Source: Stacks Tag 01OU (blueprint: lem-pur-vector-frame-integration-site-descent). -/
instance frameDescentOpenNoetherian (S : Scheme.{u}) [IsNoetherian S] (U : S.Opens) :
    IsNoetherian U.toScheme :=
  letI : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  { toIsLocallyNoetherian := inferInstance
    isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }

/-- The prescribed ordinary ordered coordinate trace, using its Kummer normalization.
Source: blueprint affine-space top trace
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
abbrev frameDescentOrdinaryTrace (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γₛ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :=
  Etale.affineTraceCounit _ (l ^ (r + 1)) hA
    (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
    (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
    T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d

/-- The assumed ordered pro-etale traces are isomorphisms and compare with the ordinary
traces on every open. Their source is expressed through the iterated proper/open comparison,
so the displayed equality is exactly t_p B = C(t_e). Open compatibility follows from
this equality, ordinary trace base change, and the given comparison coherence.
Source: blueprint frame descent, hypotheses
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def FrameDescentTraceHypothesis (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γₛ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) : Prop :=
  ∀ U : S.Opens,
    IsIso (orderedIntegration l E n U.toScheme
      (by simpa using hS.map U.ι.appTop.hom) r hA d) ∧
    orderedIntegration l E n U.toScheme
      (by simpa using hS.map U.ι.appTop.hom) r hA d =
      (comparison (Scheme.finiteTateCoefficient l E n) U.toScheme).map
        (frameDescentOrdinaryTrace l E n U.toScheme
          (by simpa using hS.map U.ι.appTop.hom) r hA d)

variable (S : Scheme.{u}) [IsNoetherian S] (r : ℕ)
  (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
  (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]

/-- The ordinary source at the supplied projective completion.
Source: blueprint frame descent, M^e
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
abbrev frameDescentEtaleSource (c : Compactification (VectorBundleZeroSection.π S d F)) :=
  (Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) c).obj
      (Etale.vectorIntegrationCoefficient _ (l ^ (r + 1)) hA S d F)

/-- The pro-etale source at that same completion, in the specified root-comparison
coordinates. The coefficient is canonically A_V(d)[2d] by twistDerived and tensor pullback.
Source: blueprint frame descent, M^p
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
abbrev frameDescentProSource (c : Compactification (VectorBundleZeroSection.π S d F)) :=
  (rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) c).obj
      ((comparison (Scheme.finiteTateCoefficient l E n) _).obj
        (Etale.vectorIntegrationCoefficient _ (l ^ (r + 1)) hA S d F))

/-- The actual proper-counit-mate/open-extension comparison, oriented opposite to B.
Source: Stacks 099R and 09AF; blueprint frame descent
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameDescentSite (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F)) :
    frameDescentProSource l E n S r hA d F c ≅
      (comparison (Scheme.finiteTateCoefficient l E n) S).obj
        (frameDescentEtaleSource l E n S r hA d F c) :=
  (compactSupportSiteComparison _ c).app
    ⟨_, vectorCoefficient_plus l E n S r hA d F hS⟩

/-- The ordinary normalized common-refinement comparison from the completion to the
compactification used by the prescribed global integration. This contains no trace.
Source: blueprint frame descent, proof Step 6
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameDescentEtaleChange (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F)) :
    frameDescentEtaleSource l E n S r hA d F c ≅
      Etale.vectorIntegrationSource _ (l ^ (r + 1)) hA S d F :=
  letI := (Etale.vectorIntegration_geometry S d F).1
  (Etale.rightDerivedLowerShriekOfCompactificationPlusιIso _ c
    (Etale.vectorBundlePurityCompactification S d F)).app
      ⟨_, vectorCoefficient_plus l E n S r hA d F hS⟩

/-- The same common-refinement comparison on the pro-etale side, retaining the actual
proper/open B on both boundaries. No trace is used in this source identification.
Source: blueprint frame descent, proof Step 6
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameDescentProChange (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F)) :
    frameDescentProSource l E n S r hA d F c ≅ vectorSource l E n S r hA d F :=
  frameDescentSite l E n S r hA d F hS c ≪≫
    (comparison (Scheme.finiteTateCoefficient l E n) S).mapIso
      (frameDescentEtaleChange l E n S r hA d F hS c) ≪≫
    (vectorSite l E n S r hA d F hS).symm

/-- The specified local integration at a frame, after the actual source change, open
restriction, and inverse-frame prefix. Both endpoints are derived restrictions of the
fixed global endpoints, so ordinary degree-zero map gluing applies without casts.
Source: blueprint frame descent, a_i^p
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameDescentLocal (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F))
    (U : S.Opens) (e : VectorBundleZeroSection.Trivialization S d F U) :
    (upperStar
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) U.ι).mapDerivedCategory.obj
        (frameDescentProSource l E n S r hA d F c) ⟶
      (upperStar
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) U.ι).mapDerivedCategory.obj
        (unit (Scheme.finiteTateCoefficient l E n) S) :=
  (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) U.ι).inv.app _ ≫
    (upperStar
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) U.ι).leftDerivedFunctor.map
        ((frameDescentProChange l E n S r hA d F hS c).hom ≫
          (vectorSite l E n S r hA d F hS).hom) ≫
    (pullback (Scheme.finiteTateCoefficient l E n) U.ι).inv.app _ ≫
    localIntegration l E n S hS r hA d F U e ≫
    (pullbackUnit (Scheme.finiteTateCoefficient l E n) U.ι).inv ≫
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) U.ι).hom.app _

/-- The named global pro-etale integration in projective-completion coordinates.
Source: blueprint frame descent, t_pi^p
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameDescentGlobal (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F)) :
    frameDescentProSource l E n S r hA d F c ⟶ unit (Scheme.finiteTateCoefficient l E n) S :=
  (frameDescentProChange l E n S r hA d F hS c).hom ≫
    vectorIntegration l E n S r hA d F hS

/-- Canonical degree-zero identification, specified by its identity H^0 normalization.
The degree-zero gluing theorem supplies naturality and restriction compatibility.
Source: Stacks 06XS and 0118; blueprint frame descent, proof Step 5
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def FrameDescentDegreeZero {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasDerivedCategory.{wB} B] (M : DerivedCategory B) : Prop :=
  DerivedCategory.homologyConcentratedIn 0 0 M ∧
  ∃! e : M ≅ (DerivedCategory.singleFunctor B 0).obj
      ((DerivedCategory.homologyFunctor B 0).obj M),
    (DerivedCategory.homologyFunctor B 0).map e.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).hom.app
        ((DerivedCategory.homologyFunctor B 0).obj M) = 𝟙 _

/-- The full frame-descent conclusion in the fixed source coordinates.
Source: blueprint vector-integration proof, all conclusion clauses
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def FrameDescentConclusion (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F))
    {I : Type v} (U : I → S.Opens)
    (e : ∀ i : I, VectorBundleZeroSection.Trivialization S d F (U i)) : Prop :=
    (∀ i j : I,
      DegreeZeroMapGluing.onSmallerOpen
        (fun T : Scheme.{u} ↦ Sheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))
        (fun {_ _} f ↦ upperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) f)
        (fun {_ _ _} f g ↦ upperStarComp
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) f g)
        S (frameDescentProSource l E n S r hA d F c)
        (unit (Scheme.finiteTateCoefficient l E n) S) inf_le_left
        (frameDescentLocal l E n S r hA d F hS c (U i) (e i)) =
      DegreeZeroMapGluing.onSmallerOpen
        (fun T : Scheme.{u} ↦ Sheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))
        (fun {_ _} f ↦ upperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) f)
        (fun {_ _ _} f g ↦ upperStarComp
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) f g)
        S (frameDescentProSource l E n S r hA d F c)
        (unit (Scheme.finiteTateCoefficient l E n) S) inf_le_right
        (frameDescentLocal l E n S r hA d F hS c (U j) (e j))) ∧
    FrameDescentDegreeZero (frameDescentEtaleSource l E n S r hA d F c) ∧
    FrameDescentDegreeZero (frameDescentProSource l E n S r hA d F c) ∧
    FrameDescentDegreeZero
      ((comparison (Scheme.finiteTateCoefficient l E n) S).obj
        (frameDescentEtaleSource l E n S r hA d F c)) ∧
    (∃! t : frameDescentProSource l E n S r hA d F c ⟶
        unit (Scheme.finiteTateCoefficient l E n) S,
      ∀ i : I, (upperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) (U i).ι).mapDerivedCategory.map
          t =
            frameDescentLocal l E n S r hA d F hS c (U i) (e i)) ∧
    IsIso (frameDescentGlobal l E n S r hA d F hS c) ∧
    (∀ (W : S.Opens) (f : VectorBundleZeroSection.Trivialization S d F W),
      (upperStar
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) W.ι).mapDerivedCategory.map
          (frameDescentGlobal l E n S r hA d F hS c) =
        frameDescentLocal l E n S r hA d F hS c W f) ∧
    (frameDescentSite l E n S r hA d F hS c).inv ≫
        frameDescentGlobal l E n S r hA d F hS c =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        ((frameDescentEtaleChange l E n S r hA d F hS c).hom ≫
          Etale.vectorBundleIntegration (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) _ hA S
            (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)


private theorem compared_vector_normalization (hS : IsUnit (l : Γₛ(S, ⊤)))
    (htrace : FrameDescentTraceHypothesis l E n S hS r hA d) :
    VectorNormalization l E n S r hA d F hS
      ((vectorSite l E n S r hA d F hS).hom ≫
        (comparison (Scheme.finiteTateCoefficient l E n) S).map
          (Etale.vectorBundleIntegration (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) _ hA S
            (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)) := by
  unfold FrameDescentTraceHypothesis at htrace
  unfold VectorNormalization
  intro V e
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  unfold localIntegration
  rw [(htrace V).2]
  have hn := (Etale.existsUnique_vectorIntegrationGluing (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F).2.exists.choose_spec.2
  have hh := hn (Etale.projectiveLineTraceTransport _
    (pow_pos (Fact.out : l.Prime).pos _) _ hA)
    (Etale.projectiveLineTraceDatum _ (pow_pos (Fact.out : l.Prime).pos _) _ hA) V e
  change _ ≫ (pullbackUnit _ V.ι).hom = _
  simp only [pullbackUnit, geoP1UnitPullback, Iso.trans_hom, Functor.mapIso_hom]
  erw [reassoc_of% (geoP1PullComparison
    (Scheme.finiteTateCoefficient l E n) V.ι).hom.naturality
      (Etale.vectorBundleIntegration (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hA S
      (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)]
  erw [← Functor.map_comp, hh]
  simp only [pullback, Iso.symm_inv, Etale.vectorIntegrationLocalTrace, chartPrefix,
    Functor.map_comp, Category.assoc]

private theorem vector_integration_comparison (hS : IsUnit (l : Γₛ(S, ⊤)))
    (htrace : FrameDescentTraceHypothesis l E n S hS r hA d) :
    vectorIntegration l E n S r hA d F hS =
      (vectorSite l E n S r hA d F hS).hom ≫
        (comparison (Scheme.finiteTateCoefficient l E n) S).map
          (Etale.vectorBundleIntegration (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) _ hA S
            (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F) := by
  exact ((existsUniqueVectorIntegration l E n S r hA d F hS).unique
    (by simpa only [vectorIntegration] using
      (existsUniqueVectorIntegration l E n S r hA d F hS).exists.choose_spec)
    (compared_vector_normalization l E n S r hA d F hS htrace))


attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Etale.vectorBundleIntegration Etale.vectorIntegrationGluing compactSupportSiteComparison

private theorem concentration_of_iso
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    {M N : DerivedCategory B} (e : M ≅ N)
    (hN : DerivedCategory.homologyConcentratedIn 0 0 N) :
    DerivedCategory.homologyConcentratedIn 0 0 M := by
  have hge := hN.1
  have hle := hN.2
  exact ⟨DerivedCategory.TStructure.t.isGE_of_iso e.symm 0,
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0⟩

private theorem concentration_of_vanishing
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (M : DerivedCategory B)
    (hM : ∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor B q).obj M)) :
    DerivedCategory.homologyConcentratedIn 0 0 M := by
  exact ⟨(DerivedCategory.isGE_iff M 0).2 (fun q hq ↦ hM q (ne_of_lt hq)),
    (DerivedCategory.isLE_iff M 0).2 (fun q hq ↦ hM q (ne_of_gt hq))⟩

private theorem unit_concentration (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategory.homologyConcentratedIn 0 0 (Etale.ordinaryFiniteUnit A T) := by
  exact ⟨inferInstance, inferInstance⟩

private theorem degree_zero_of_concentration
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (M : DerivedCategory B) (hM : DerivedCategory.homologyConcentratedIn 0 0 M) :
    FrameDescentDegreeZero M := by
  unfold FrameDescentDegreeZero
  refine ⟨hM, DerivedCategory.existsUnique_iso_single_homology_zero M ?_⟩
  intro q hq
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact (DerivedCategory.isGE_iff M 0).1 hM.1 q hq
  · exact (DerivedCategory.isLE_iff M 0).1 hM.2 q hq

private theorem global_restricts_to_frame (hS : IsUnit (l : Γₛ(S, ⊤)))
    (c : Compactification (VectorBundleZeroSection.π S d F))
    (W : S.Opens) (f : VectorBundleZeroSection.Trivialization S d F W) :
    (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      W.ι).mapDerivedCategory.map (frameDescentGlobal l E n S r hA d F hS c) =
        frameDescentLocal l E n S r hA d F hS c W f := by
  have hn : VectorNormalization l E n S r hA d F hS
      (vectorIntegration l E n S r hA d F hS) := by
    simpa only [vectorIntegration] using
      (existsUniqueVectorIntegration l E n S r hA d F hS).exists.choose_spec
  unfold VectorNormalization at hn
  have hh := hn W f
  change _ ≫ _ = _ at hh
  have he := congrArg (fun t ↦ t ≫ (pullbackUnit _ W.ι).inv) hh
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at he
  let a := leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) W.ι
  apply (cancel_epi (a.hom.app _)).mp
  rw [← a.hom.naturality]
  unfold frameDescentGlobal frameDescentLocal
  simp only [Functor.map_comp, Category.assoc]
  rw [he]
  dsimp only [a]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem gluing_from_global (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) {I : Type v} (U : I → T.Opens) (hU : iSup U = ⊤)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.homologyConcentratedIn 0 0 M)
    (hN : DerivedCategory.homologyConcentratedIn 0 0 N)
    (a : ∀ i, (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.obj N)
    (t : M ⟶ N)
    (ht : ∀ i, (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map t = a i) :
    (∀ i j : I,
      DegreeZeroMapGluing.onSmallerOpen
        (fun X : Scheme.{u} ↦ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
        (fun {_ _} f ↦ upperStar (ModuleCat.{u + 1} A) f)
        (fun {_ _ _} f g ↦ upperStarComp (ModuleCat.{u + 1} A) f g)
        T M N (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      DegreeZeroMapGluing.onSmallerOpen
        (fun X : Scheme.{u} ↦ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
        (fun {_ _} f ↦ upperStar (ModuleCat.{u + 1} A) f)
        (fun {_ _ _} f g ↦ upperStarComp (ModuleCat.{u + 1} A) f g)
        T M N (inf_le_right : U i ⊓ U j ≤ U j) (a j)) ∧
    ∃! b : M ⟶ N,
      ∀ i, (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map b = a i := by
  have hg := (DegreeZeroMapGluing.degreeZeroDerivedMapGluing A T U hU).2.2 M N
    (fun i ↦ ⟨Functor.homologyConcentratedIn_mapDerivedCategory_obj
      (upperStar (ModuleCat.{u + 1} A) (U i).ι) hM,
      Functor.homologyConcentratedIn_mapDerivedCategory_obj
        (upperStar (ModuleCat.{u + 1} A) (U i).ι) hN⟩)
  have hu : ∃! b : M ⟶ N,
      ∀ i, (upperStar (ModuleCat.{u + 1} A) (U i).ι).mapDerivedCategory.map b = a i := by
    refine ⟨t, ht, ?_⟩
    intro b hb
    exact (hg.2.2.2.2.2 b t).1 (fun i ↦ (hb i).trans (ht i).symm)
  exact ⟨(hg.2.2.1 a).2 hu, hu⟩

private theorem transport_integration
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {M N U : C} {P V : D} (p : P ≅ H.obj M) (e : M ≅ N)
    (v : V ≅ H.obj N) (t : N ⟶ U) [IsIso t] (i : V ⟶ H.obj U)
    (hi : i = v.hom ≫ H.map t) :
    IsIso ((p ≪≫ H.mapIso e ≪≫ v.symm).hom ≫ i) ∧
    p.inv ≫ (p ≪≫ H.mapIso e ≪≫ v.symm).hom ≫ i = H.map (e.hom ≫ t) := by
  rw [hi]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, ← Functor.map_comp]
  exact ⟨inferInstance, trivial⟩


private theorem global_comparison_and_isIso (hS : IsUnit (l : Γₛ(S, ⊤)))
    (htrace : FrameDescentTraceHypothesis l E n S hS r hA d)
    (c : Compactification (VectorBundleZeroSection.π S d F)) :
    IsIso (frameDescentGlobal l E n S r hA d F hS c) ∧
    (frameDescentSite l E n S r hA d F hS c).inv ≫
        frameDescentGlobal l E n S r hA d F hS c =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        ((frameDescentEtaleChange l E n S r hA d F hS c).hom ≫
          Etale.vectorBundleIntegration (l ^ (r + 1))
            (pow_pos (Fact.out : l.Prime).pos _) _ hA S
            (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F) := by
  let A := Scheme.finiteTateCoefficient l E n
  have he := Etale.vectorBundleIntegration_concentration_and_isIso (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) A hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F
  have := he.2
  unfold frameDescentGlobal frameDescentProChange
  exact transport_integration (comparison A S)
    (frameDescentSite l E n S r hA d F hS c)
    (frameDescentEtaleChange l E n S r hA d F hS c)
    (vectorSite l E n S r hA d F hS) _ _
    (vector_integration_comparison l E n S r hA d F hS htrace)


/-- The complete overlap, degree-zero, unique-gluing and comparison conclusions at a
chosen projective completion. The named global integration satisfies every frame, not
only the frames of the displayed finite cover, expressing independence of all choices.
Source: blueprint def-amb-vector-integration.proof.md; Stacks 06XS, 03EM and 04TQ
(blueprint: lem-pur-vector-frame-integration-site-descent).

Proof: the compared ordinary global trace satisfies the defining local normalization
of pro-etale integration, by ordinary frame normalization and the trace hypothesis.
Uniqueness identifies it with the named pro-etale integration. The ordinary geometric
concentration and invertibility theorem transports through the actual compactification
change and exact site comparison. The standard H0-normalized single-object isomorphism
gives each degree-zero identification. The defining normalization proves restriction
to every frame. Degree-zero map gluing then proves overlap agreement and uniqueness
on the displayed cover, including an empty cover. Cancelling the source comparisons
gives the final comparison equation; ordinary invertibility gives invertibility.
-/
theorem vectorFrameIntegrationSiteDescent (hS : IsUnit (l : Γₛ(S, ⊤)))
    (htrace : FrameDescentTraceHypothesis l E n S hS r hA d)
    (c : Compactification (VectorBundleZeroSection.π S d F))
    {I : Type v} [Finite I] (U : I → S.Opens) (hU : iSup U = ⊤)
    (e : ∀ i : I, VectorBundleZeroSection.Trivialization S d F (U i)) :
    FrameDescentConclusion l E n S r hA d F hS c U e := by
  let A := Scheme.finiteTateCoefficient l E n
  have he := Etale.vectorBundleIntegration_concentration_and_isIso (l ^ (r + 1))
    (pow_pos (Fact.out : l.Prime).pos _) A hA S
    (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F
  have hE := concentration_of_iso (frameDescentEtaleChange l E n S r hA d F hS c)
    (concentration_of_vanishing _ he.1)
  have hC : DerivedCategory.homologyConcentratedIn 0 0
      ((comparison A S).obj (frameDescentEtaleSource l E n S r hA d F c)) :=
    Functor.homologyConcentratedIn_mapDerivedCategory_obj
      (comparisonUpperStar (ModuleCat.{u + 1} A) S) hE
  have hP := concentration_of_iso (frameDescentSite l E n S r hA d F hS c) hC
  have hunit : DerivedCategory.homologyConcentratedIn 0 0 (unit A S) :=
    Functor.homologyConcentratedIn_mapDerivedCategory_obj
      (comparisonUpperStar (ModuleCat.{u + 1} A) S) (unit_concentration A S)
  have hr := global_restricts_to_frame l E n S r hA d F hS c
  have hg := gluing_from_global A S U hU
    (frameDescentProSource l E n S r hA d F c) (unit A S) hP hunit
    (fun i ↦ frameDescentLocal l E n S r hA d F hS c (U i) (e i))
    (frameDescentGlobal l E n S r hA d F hS c) (fun i ↦ hr (U i) (e i))
  have hc := global_comparison_and_isIso l E n S r hA d F hS htrace c
  unfold FrameDescentConclusion
  exact ⟨hg.1, degree_zero_of_concentration _ hE,
    degree_zero_of_concentration _ hP, degree_zero_of_concentration _ hC,
    hg.2, hc.1, hr, hc.2⟩




/-- The constant ordinary coefficient is bounded below in degree zero.
Source: degree-zero constant complex
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
theorem frameActionUnitBounded (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit A T) := by
  exact ⟨0, inferInstance⟩

/-- The coordinate Tate input as a bounded-below object, for the actual frame action.
Source: blueprint frame descent, proof Step 1
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameActionInput (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤))) :=
  (⟨_, rightTower_plus l E n T hT r hA d
    ⟨Etale.ordinaryFiniteUnit _ T, frameActionUnitBounded _ T⟩⟩ :
      DerivedCategory.Plus (Sheaf (affineTraceTower T d).smallEtaleTopology
        (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))



/-- The bounded input has the prescribed ordinary Tate tower as its underlying object.
Source: the definition of the bounded input
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
theorem frameActionInput_obj (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γₛ(T, ⊤))) :
    (frameActionInput l E n r hA d T hT).obj =
      (Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj
        (Etale.ordinaryFiniteUnit _ T) := by
  unfold frameActionInput
  rfl

/-- The canonical Tate pullback map in the bounded input's recorded coordinates.
Only the defining object equality changes its presentation.
Source: blueprint frame descent, canonical Tate coefficient identification
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameActionCoefficient (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γₛ(T, ⊤)))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :
    (Etale.ordinaryFinitePullback (Scheme.finiteTateCoefficient l E n)
      (affineTraceLinearMap T d G)).obj (frameActionInput l E n r hA d T hT).obj ≅
      (frameActionInput l E n r hA d T hT).obj :=
  let e := eqToIso (frameActionInput_obj l E n r hA d T hT)
  (Etale.ordinaryFinitePullback _ (affineTraceLinearMap T d G)).mapIso e ≪≫
    Etale.affineLinearCoefficientPullback _ (l ^ (r + 1)) hA
      (Etale.projectiveLineTraceTransport _ (pow_pos (Fact.out : l.Prime).pos _) _ hA)
      T (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d
      (affineTraceLinearMap T d G) (affineTraceLinearMap_over T d G) ≪≫ e.symm

/-- The canonical inverse-image identification for the identity on the base.
Source: exact inverse image, blueprint frame descent, proof Step 3
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
def frameActionIdentity (T : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) (𝟙 T)).leftDerivedFunctor ≅
        𝟭 _ :=
  leftDerivedUpperStarIsoMapDerivedCategory _ (𝟙 T) ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId _ T) ≪≫
    Functor.mapDerivedCategoryIdIso _



/-- The ordinary compact-support action formula, before specializing coefficients.
Source: blueprint frame descent, proof Step 3
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameActionEtaleComposite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj)
    (z : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj K.obj ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) :=
  (Etale.affineLinearPullbackId A T).inv.app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app K.obj ≫
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map q ≫ z

/-- The independently constructed pro-etale compact-support action formula.
Source: blueprint frame descent, proof Step 3
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameActionProComposite (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (I : (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).leftDerivedFunctor ≅ 𝟭 _)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj)
    (z : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj K.obj ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) :=
  I.inv.app ((rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj ((comparison A X).obj K.obj)) ≫
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app ((comparison A X).obj K.obj) ≫
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
        ((pullback A a).inv.app K.obj ≫ (comparison A X).map q) ≫
    (compactSupportSiteComparison A (c.ofIsPullback sq)).hom.app K ≫
    (comparison A T).map z ≫ (compactSupportSiteComparison A c).inv.app K

/-- The ordinary compact-support frame action: identity pullback, the actual exchange,
canonical Tate identification, and the normalized change back from the pullback
compactification. It is not an action chosen to make a trace invariant.
Source: blueprint frame descent, rho_G^e in proof Step 3
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameActionEtale (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤)))
    (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :=
  let A := Scheme.finiteTateCoefficient l E n
  let K := frameActionInput l E n r hA d T hT
  let sq := affineTraceLinearMap_isPullback T d G
  let q := frameActionCoefficient l E n r hA d T hT G
  let : IsNoetherian (affineTraceTower T d) := affineTraceNoetherian T d
  frameActionEtaleComposite A sq c K q.hom
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
      (c.ofIsPullback sq) c).hom.app K)


/-- The pro-etale compact-support frame action uses its own exchange transformation.
The coefficient identification is the specified scheme-pullback comparison followed by
comparison of the ordinary Tate identification; root-normalized descent makes this
precisely the pro-etale Tate pullback map. The final change is the same common refinement.
Source: blueprint frame descent, rho_G^p in proof Step 3
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def frameActionPro (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γₛ(T, ⊤)))
    (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :=
  let A := Scheme.finiteTateCoefficient l E n
  let K := frameActionInput l E n r hA d T hT
  let sq := affineTraceLinearMap_isPullback T d G
  let q := frameActionCoefficient l E n r hA d T hT G
  let : IsNoetherian (affineTraceTower T d) := affineTraceNoetherian T d
  frameActionProComposite A sq c (frameActionIdentity l E n T) K q.hom
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
      (c.ofIsPullback sq) c).hom.app K)


/-- The intertwining equation for independently constructed frame actions.
Source: blueprint frame descent, rho_p B = B C(rho_e)
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def FrameActionIntertwining (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γₛ(T, ⊤))) (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) : Prop :=
    (compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n) c).inv.app
        (frameActionInput l E n r hA d T hT) ≫
        frameActionPro l E n r hA d T hT c G =
      (comparison (Scheme.finiteTateCoefficient l E n) T).map
          (frameActionEtale l E n r hA d T hT c G) ≫
        (compactSupportSiteComparison (Scheme.finiteTateCoefficient l E n) c).inv.app
          (frameActionInput l E n r hA d T hT)

private theorem exact_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ C) (N : C ⥤ D) (P : D ⥤ D)
    [E.Additive] [N.Additive] [P.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (q : E ⋙ N ≅ N ⋙ P) (e : E ≅ 𝟭 C) (p : P ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ p.hom.app (N.obj X) = N.map (e.hom.app X))
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso q).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso p ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (N.mapDerivedCategory.obj K) =
      N.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K) := by
  have heq : q ≪≫ Functor.isoWhiskerLeft N p ≪≫ N.rightUnitor =
      Functor.isoWhiskerRight e N ≪≫ N.leftUnitor := by
    ext X
    simpa using hq X
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hleft := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft N p) K
  have hright := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N) K
  have hu : (Functor.mapDerivedCategoryNatIso N.rightUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hv : (Functor.mapDerivedCategoryNatIso N.leftUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hu, hv] at hd
  simp only [NatTrans.id_app, Category.comp_id] at hd
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso E N).hom.app K)).mp
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  have hp := congr_app (Functor.mapDerivedCategoryCompIso_comp_id N) K
  have he := congr_app (Functor.mapDerivedCategoryCompIso_id_comp N) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hp he
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hleft hright
  calc
    _ = (Functor.mapDerivedCategoryNatIso q).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft N p)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso N (𝟭 D)).hom.app K ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (N.mapDerivedCategory.obj K) := by
      rw [reassoc_of% hleft]
    _ = (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e N)).hom.app K := by
      rw [hp]
      erw [Category.comp_id]
      exact hd
    _ = (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e N)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso (𝟭 C) N).hom.app K ≫
        N.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app K) := by
      rw [he]
      erw [Category.comp_id]
    _ = _ := by rw [← Category.assoc, hright, Category.assoc]



private theorem bounded_identity (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} A))) :
    (leftDerivedUpperStarComparisonIso (𝟙 T) A).hom.app K =
      (comparison _ T).map
        ((Functor.mapDerivedCategoryNatIso (Etale.upperStarId
          (ModuleCat.{u + 1} A) T) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K.obj) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 T) ≪≫
        Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) T) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv.app ((comparison _ T).obj K.obj) := by
  have h := exact_identity_square
    (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 T))
    (comparisonUpperStar (ModuleCat.{u + 1} A) T)
    (upperStar (ModuleCat.{u + 1} A) (𝟙 T))
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) (𝟙 T)).symm
    (Etale.upperStarId (ModuleCat.{u + 1} A) T)
    (upperStarId (ModuleCat.{u + 1} A) T)
    ((comparison_pullback_coherent.2.2 A).1 T) K.obj
  have hh := congrArg (fun z ↦ z ≫
    (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) T) ≪≫
      Functor.mapDerivedCategoryIdIso _).inv.app ((comparison A T).obj K.obj)) h
  simp only [Category.assoc, Iso.hom_inv_id_app] at hh
  erw [Category.comp_id] at hh
  dsimp only [leftDerivedUpperStarComparisonIso, frameActionIdentity,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Iso.refl_hom, NatTrans.id_app]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [frameActionIdentity,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
    using congrArg (fun z ↦ z ≫ (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} A) (𝟙 T)).inv.app ((comparison A T).obj K.obj)) hh


private theorem coefficient_pull_comparison
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (leftDerivedUpperStarComparisonIso f A).hom.app K ≫
        (geoP1PullComparison A f).hom.app K.obj =
      (geoP1Comparison A X).map
        ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) f).inv.app K.obj) := by
  simp only [leftDerivedUpperStarComparisonIso, geoP1PullComparison,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id, Category.assoc]
  dsimp only [geoP1Comparison, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.mapDerivedCategoryPlus, ObjectProperty.lift]
  erw [Category.id_comp, Iso.inv_hom_id_app_assoc,
    Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryNatIso_symm]
  simp only [Iso.inv_hom_id_app_assoc]


private theorem etale_exchange_coefficient
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj) :
    DerivedCategory.Plus.ι.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app K) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus.obj K) ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) a).inv.app K.obj ≫ q) =
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} A) T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          (((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} A) c).obj K).obj) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app K ≫
      (Etale.affineLinearPullbackId A T).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K.obj) ≫
      (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app K.obj ≫
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map q := by
  let Ie := Functor.mapDerivedCategoryNatIso
    (Etale.upperStarId (ModuleCat.{u + 1} A) T) ≪≫ Functor.mapDerivedCategoryIdIso _
  let bc := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c
  have hc := Etale.unboundedEtaleCompactSupport_exchange_plus A sq c K
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] at hc
  dsimp only [Functor.comp_obj, ObjectProperty.ι_obj] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  simp only [Functor.map_comp]
  erw [reassoc_of% hc]
  simp only [Etale.unboundedEtaleCompactSupportExchange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← reassoc_of% Ie.hom.naturality (bc.hom.app K)]
  dsimp only [Ie, bc, Etale.affineLinearPullbackId, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]



private theorem exchange_action
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (I : (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).leftDerivedFunctor ≅ 𝟭 _)
    (hid : ∀ J : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (leftDerivedUpperStarComparisonIso (𝟙 T) A).hom.app J =
        (comparison A T).map
          ((Functor.mapDerivedCategoryNatIso (Etale.upperStarId
            (ModuleCat.{u + 1} A) T) ≪≫ Functor.mapDerivedCategoryIdIso _).hom.app J.obj) ≫
        I.inv.app ((comparison A T).obj J.obj))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj) :
    (compactSupportSiteComparison A c).inv.app K ≫
      I.inv.app ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj ((comparison A X).obj K.obj)) ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app ((comparison A X).obj K.obj) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
          ((geoP1PullComparison A a).hom.app K.obj ≫ (comparison A X).map q) ≫
      (compactSupportSiteComparison A (c.ofIsPullback sq)).hom.app K =
    (comparison A T).map
      ((Etale.affineLinearPullbackId A T).inv.app
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} A) c).obj K.obj) ≫
        (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app K.obj ≫
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map q) := by
  have h := NatTrans.congr_app (compactSupport_exchange_transport A sq c).1 K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map] at h
  let K' := (Etale.upperStar (ModuleCat.{u + 1} A)
    a).mapDerivedCategoryPlus.obj K
  let be := Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    a
  let qp : K'.obj ⟶ K.obj := (be.inv.app K.obj) ≫ q
  have hn := (compactSupportSiteComparison A (c.ofIsPullback sq)).hom.naturality
    (ObjectProperty.homMk qp : K' ⟶ K)
  simp only [Functor.comp_map] at hn
  let Fe' := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} A) (c.ofIsPullback sq)
  let Fp' := rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} A) (c.ofIsPullback sq)
  let C := comparison A T
  let Cx := comparison A X
  let B := compactSupportSiteComparison A c
  let B' := compactSupportSiteComparison A (c.ofIsPullback sq)
  let bc := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c
  let bc' := Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) (c.ofIsPullback sq)
  let Ie := Functor.mapDerivedCategoryNatIso
    (Etale.upperStarId (ModuleCat.{u + 1} A) T) ≪≫ Functor.mapDerivedCategoryIdIso _
  let L := (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).leftDerivedFunctor
  change Fp'.map (Cx.map qp) ≫ B'.hom.app K =
    B'.hom.app K' ≫ C.map (Fe'.map qp) at hn
  have hp : Fp'.map ((leftDerivedUpperStarComparisonIso
        a A).hom.app K) ≫
      Fp'.map ((geoP1PullComparison A a).hom.app K.obj) ≫
      Fp'.map (Cx.map q) ≫ B'.hom.app K =
      B'.hom.app K' ≫ C.map (Fe'.map qp) := by
    rw [← Fp'.map_comp_assoc, coefficient_pull_comparison]
    rw [← Fp'.map_comp_assoc, ← Cx.map_comp]
    exact hn
  have he := etale_exchange_coefficient A sq c K q
  simp only [compactExchangeTransportSource, compactExchangeTransportTarget,
    compactExchangeTransportComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.map_comp, Category.assoc] at h
  erw [Category.id_comp] at h
  change C.map (DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app K)) ≫
    C.map (bc'.hom.app K') ≫ B'.inv.app K' ≫
      Fp'.map ((leftDerivedUpperStarComparisonIso a A).hom.app K) =
    (leftDerivedUpperStarComparisonIso (𝟙 T) A).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) c).obj K) ≫
      L.map (C.map (bc.hom.app K)) ≫ L.map (B.inv.app K) ≫
        (rightDerivedLowerShriekOfCompactificationBaseChangeMap
          (ModuleCat.{u + 1} A) sq c).app (Cx.obj K.obj) at h
  have h' := congrArg (fun z ↦ z ≫
    Fp'.map ((geoP1PullComparison A a).hom.app K.obj) ≫
    Fp'.map (Cx.map q) ≫ B'.hom.app K) h
  simp only [Category.assoc] at h'
  have hp' := congrArg (fun z ↦ C.map (DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app K)) ≫
    C.map (bc'.hom.app K') ≫ B'.inv.app K' ≫ z) hp
  simp only [Iso.inv_hom_id_app_assoc] at hp'
  have h'' := hp'.symm.trans h'
  clear h'
  have h' := h''
  have he' := congrArg C.map he
  simp only [Functor.map_comp] at he'
  simp only [qp, be, Functor.map_comp] at h'
  have h''' := he'.symm.trans h'
  clear h'
  have h' := h'''
  rw [hid] at h'
  have hi := I.inv.naturality (C.map (bc.hom.app K) ≫ B.inv.app K)
  simp only [Functor.id_map] at hi
  rw [← L.map_comp_assoc] at h'
  simp only [Category.assoc] at h'
  erw [← reassoc_of% hi] at h'
  have hh := (cancel_epi (C.map (Ie.hom.app _))).mp h'
  have hh' := (cancel_epi (C.map (bc.hom.app K))).mp hh
  simpa only [Functor.map_comp, Category.assoc, C, Cx, B, B', Fp', Fe',
    Functor.comp_obj, ObjectProperty.ι_obj] using hh'.symm







private theorem exchange_action_with_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    {f : X ⟶ T} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} (sq : IsPullback a f f (𝟙 T)) (c : Compactification f)
    (I : (upperStar (ModuleCat.{u + 1} A) (𝟙 T)).leftDerivedFunctor ≅ 𝟭 _)
    (hid : ∀ J : DerivedCategory.Plus
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (leftDerivedUpperStarComparisonIso (𝟙 T) A).hom.app J =
        (comparison A T).map
          ((Functor.mapDerivedCategoryNatIso (Etale.upperStarId
            (ModuleCat.{u + 1} A) T) ≪≫ Functor.mapDerivedCategoryIdIso _).hom.app J.obj) ≫
        I.inv.app ((comparison A T).obj J.obj))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (q : (Etale.ordinaryFinitePullback A a).obj K.obj ⟶ K.obj)
    (z : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj K.obj ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K.obj) :
    (compactSupportSiteComparison A c).inv.app K ≫
        frameActionProComposite A sq c I K q z =
      (comparison A T).map (frameActionEtaleComposite A sq c K q z) ≫
        (compactSupportSiteComparison A c).inv.app K := by
  unfold frameActionProComposite frameActionEtaleComposite
  have h := exchange_action A sq c I hid K q
  have hh := congrArg (fun w ↦ w ≫ (comparison A T).map z ≫
    (compactSupportSiteComparison A c).inv.app K) h
  simpa only [pullback, Iso.symm_inv, Functor.map_comp, Category.assoc] using hh




/-- Frame action intertwines the actual site comparison for every compactification.
Source: blueprint frame descent, conclusion and proof Steps 2--3
(blueprint: lem-pur-vector-frame-integration-site-descent).
Proof: apply compact-support exchange transport to the Cartesian affine frame square
and its pulled-back compactification, on the bounded-below Tate input. Naturality of
the actual site comparison in the canonical coefficient map identifies the target
path. The bounded/unbounded ordinary exchange compatibility identifies the ordinary
path. Derived identity coherence, obtained from the underived comparison identity,
cancels the base identity pullback. Postcomposition with the same normalized
compactification change gives the two specified actions and the intertwining equation.
The argument includes rank zero, nonaffine bases, and the empty scheme.
-/
theorem frameActionSiteDescent (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γₛ(T, ⊤))) (c : Compactification (affineTraceProjection T d))
    (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(T, ⊤)) :
    FrameActionIntertwining l E n r hA d T hT c G := by
  let A := Scheme.finiteTateCoefficient l E n
  let K := frameActionInput l E n r hA d T hT
  let sq := affineTraceLinearMap_isPullback T d G
  let : IsNoetherian (affineTraceTower T d) := affineTraceNoetherian T d
  let q := frameActionCoefficient l E n r hA d T hT G
  unfold FrameActionIntertwining frameActionPro frameActionEtale
  dsimp only
  exact exchange_action_with_change A sq c (frameActionIdentity l E n T)
      (bounded_identity A T) K q.hom
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A
        (c.ofIsPullback sq) c).hom.app K)


/-- The supplied compactification is the projective completion of the recorded
symmetric algebra, with precisely its dehomogenization chart. This predicate packages
the conclusion of exists_projective_completion; it constructs no replacement object.
Source: blueprint vector projective completion; Stacks 01OA and 01NG
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
def IsFrameDescentProjectiveCompletion
    (c : Compactification (VectorBundleZeroSection.π S d F)) : Prop :=
  ∃ (P : VectorProjectiveCompletion.Presentation S F)
    (ht : ∀ V : S.affineOpens,
      VectorProjectiveCompletion.t P V ∈ P.algebra.grading V 1)
    (a : ∀ V : S.affineOpens, SymmetricAlgebraSheaf.sections F (Opposite.op V.1) ≃+*
      HomogeneousLocalization.Away (P.algebra.grading V) (VectorProjectiveCompletion.t P V)),
    (∀ (V : S.affineOpens) (m : F.val.obj (Opposite.op V.1)),
      (a V (SymmetricAlgebra.ι _ _ m)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (VectorProjectiveCompletion.t P V))
            (VectorProjectiveCompletion.x P V m) *
          IsLocalization.Away.invSelf (VectorProjectiveCompletion.t P V)) ∧
    (∀ (V : S.affineOpens) (x : Γₛ(S, V.1)),
      (a V (algebraMap Γₛ(S, V.1) (SymmetricAlgebraSheaf.sections F (Opposite.op V.1)) x)).val =
        algebraMap (P.algebra.obj V) (Localization.Away (VectorProjectiveCompletion.t P V))
          (algebraMap Γₛ(S, V.1) (P.algebra.obj V) x)) ∧
    ∃ hZ : c.Z = P.algebra.relProj,
      c.g = eqToHom hZ ≫ P.algebra.relProjHom ∧
      (c.i ≫ eqToHom hZ).opensRange = VectorProjectiveCompletion.chartOpen P ∧
      ∀ V : S.affineOpens,
        VectorBundleZeroSection.affineChart S d F V ≫
            VectorProjectiveCompletion.chartMap P ht a V =
          ((VectorBundleZeroSection.π S d F) ⁻¹ᵁ V.1).ι ≫ c.i ≫ eqToHom hZ

/-- Finite-field specialization with the positive coefficient level of the conventions.
All Noetherianity and invertibility witnesses are consequences in this proposition,
not extra hypotheses. Every finite frame cover, including the empty cover, is allowed.
The coordinate trace hypothesis uses n'=level-1 and r'=r-1 in the node's indexing.
Source: blueprint frame descent, hypotheses and all conclusions
(blueprint: lem-pur-vector-frame-integration-site-descent). -/
@[irreducible]
def FiniteTypeFrameDescent (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] (rank : ℕ)
    (M : T.Modules) [M.IsFiniteLocallyFreeOfRank rank] : Prop :=
  letI : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  ∃ hT : IsUnit (P.coefficients.l : Γₛ(T, ⊤)),
    ∀ (s : ℕ) (hB : ((P.coefficients.l ^ (s + 1) : ℕ) :
      Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)) = 0),
      FrameDescentTraceHypothesis P.coefficients.l P.extension (P.level - 1)
        T hT s hB rank →
      (∀ (c : Compactification (VectorBundleZeroSection.π T rank M)),
        IsFrameDescentProjectiveCompletion T rank M c →
        ∀ (J : Type v) [Finite J] (U : J → T.Opens) (_hU : iSup U = ⊤)
          (e : ∀ j : J, VectorBundleZeroSection.Trivialization T rank M (U j)),
          FrameDescentConclusion P.coefficients.l P.extension (P.level - 1)
            T s hB rank M hT c U e) ∧
      (∀ (W : T.Opens)
        (c : Compactification (affineTraceProjection W.toScheme rank))
        (G : Matrix.GeneralLinearGroup (Fin rank) Γₛ(W.toScheme, ⊤)),
        FrameActionIntertwining P.coefficients.l P.extension (P.level - 1)
          s hB rank W.toScheme (by simpa using hT.map W.ι.appTop.hom) c G)




private theorem frame_descent_all (hS : IsUnit (l : Γₛ(S, ⊤))) :
    ∀ (s : ℕ) (hB : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0),
      FrameDescentTraceHypothesis l E n S hS s hB d →
      (∀ (c : Compactification (VectorBundleZeroSection.π S d F)),
        IsFrameDescentProjectiveCompletion S d F c →
        ∀ (J : Type v) [Finite J] (U : J → S.Opens) (_hU : iSup U = ⊤)
          (e : ∀ j : J, VectorBundleZeroSection.Trivialization S d F (U j)),
          FrameDescentConclusion l E n S s hB d F hS c U e) ∧
      (∀ (W : S.Opens) (c : Compactification (affineTraceProjection W.toScheme d))
        (G : Matrix.GeneralLinearGroup (Fin d) Γₛ(W.toScheme, ⊤)),
        FrameActionIntertwining l E n s hB d W.toScheme
          (by simpa using hS.map W.ι.appTop.hom) c G) := by
  exact fun s hB ht ↦
    ⟨fun c _ J _ U hU e ↦
      vectorFrameIntegrationSiteDescent l E n S s hB d F hS ht c U hU e,
      fun W c G ↦ frameActionSiteDescent l E n s hB d W.toScheme
        (by simpa using hS.map W.ι.appTop.hom) c G⟩


private theorem finite_type_prime_unit (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (CommRingCat.of P.field.k)) :
    IsUnit (P.coefficients.l : Γₛ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using P.coefficientPrime_isUnit_stalk T aT x


/-- Frame descent with exactly the finite-field and positive-level coefficient data.
Source: main-20261015 def-amb-vector-integration.proof.md; Stacks 06XS, 03EM, 04TQ
(blueprint: lem-pur-vector-frame-integration-site-descent).
Proof: finite type over Spec k gives Noetherianity of T. Since l differs from the
characteristic of k, l is a unit in k and on T. Positive level gives
(level-1)+1=level, so the finite-site coefficient is the specified quotient A_{E,n}.
Apply vectorFrameIntegrationSiteDescent to the specified compactification and every
finite frame cover. Apply frameActionSiteDescent on each open. All compactification
changes and comparisons are the prescribed canonical maps; the projective-completion
predicate packages the supplied geometry and requires no replacement construction.
The two theorems give concentration, overlap equality, unique gluing, invertibility,
frame independence and the global comparison equation.
-/
theorem finiteTypeVectorFrameIntegrationSiteDescent
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] (rank : ℕ)
    (M : T.Modules) [M.IsFiniteLocallyFreeOfRank rank] :
    FiniteTypeFrameDescent.{u, v} P T aT rank M := by
  have : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  unfold FiniteTypeFrameDescent
  exact ⟨finite_type_prime_unit P T aT,
    frame_descent_all P.coefficients.l P.extension (P.level - 1) T rank M
      (finite_type_prime_unit P T aT)⟩


end AlgebraicGeometry.ProEtale.VectorIntegrationSite
