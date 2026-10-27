module

public import Sheaf.Paper.AffineOrderedIntegrationData
public import Sheaf.Paper.AffineOrderedCounitData
import Sheaf.Paper.AffineOrderedCounitZero
import Sheaf.Paper.AffineOrderedCounitSuccessor
import Sheaf.Paper.AffineOrderedIntegrationSuccessor
import Sheaf.Paper.AffineLineComparisonNaturality
import Sheaf.Paper.CoordinateLineAdjunction
import all Sheaf.Paper.CoordinateSectionArrows

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.AffineSpacePurityComparison
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.ShriekTensorComposition
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.FiniteProjectionActionLaws
import all Sheaf.Paper.FiniteProjectionActionLaws
import all Sheaf.Paper.CompactSupportSiteCoherence
import all Sheaf.AlgebraicGeometry.ShriekTensorComposition
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

@[expose] public section
set_option autoImplicit false

/-! # Ordered affine integration transposes

Source: main-20261015, sec-smooth-purity/sk-thm-smooth-purity,
lem-pur-projection-purity-agreement.proof.md, final paragraph
(blueprint: lem-pur-affine-ordered-integration-transposes).
- Canonical affine integration is transported from the ordered ordinary counit.
- Its coefficient transpose is compared with the recorded affine-space recursion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
  AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  Functor.leftDerivedFunctor Functor.mapDerivedCategory DerivedCategory.singleFunctors

attribute [local irreducible] projectionMapOfCompactification
attribute [local semireducible] AffineLinePurity.proSourceObject
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ordinary counit equals inverse projection followed by coefficient integration.
The equation is precomposed with the canonical projection, so it uses no arbitrary inverse.
Source: displayed ordered-counit formula
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: for one line compose the normalized projective adjunction with the open adjunction.
The open counit tensor-action identity rewrites its trace as the restricted projective
trace. Induct using the canonical projection-composition and compactification action laws;
lem-pur-composite-integration-counit identifies the composite counit. At the unit this is
exactly ordinaryTraceRaw. The normalized Tate source is ordinarySourceIso. Rank zero is
the identity adjunction. The argument uses only an annihilating invertible exponent, so
it imposes no divisibility or flatness condition on the finite coefficient quotient. -/
theorem ordinary_counit_formula (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k))
    (K : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hK : etaleFiniteTor (AffineLinePurity.Ring P) Y K) (d : ℕ) :
    OrdinaryCounitEquation (AffineLinePurity.Ring P) (affineTraceProjection Y d)
      (Etale.affineLinearBaseCoefficient (AffineLinePurity.Ring P) (exponent P) (annihilates P)
        (affineTraceTower Y d) d) K _ (ordinarySourceIso P Y aY K d)
      (ordinaryCounit P Y aY K hK d) (ordinaryTraceRaw P Y aY d) := by
  induction d generalizing K with
  | zero => exact ordinary_counit_zero P Y aY K hK
  | succ d ih => exact ordinary_counit_successor P Y aY d (fun K hK ↦ ih K hK) K hK

/-- The coordinate bundle as the existing free module sheaf, with its standard basis.
Source: the trivial rank-d bundle
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
abbrev coordinateModule (Y : Scheme.{u}) (d : ℕ) : Y.Modules :=
  SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin d))

/-- Trace, inverse projections, counits, and exceptional transposes use the specified
site comparisons, specialized to the coordinate bundle at the actual positive level.
Source: lem-pur-vector-integration-site-comparison and the site-comparison clause
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: specialize finiteTypeSiteComparison to the free rank-d sheaf and zero-based level
P.level-1. This is the same positive quotient used by AffineLinePurity.Ring P. The predicate
  contains
the projective trace, open-counit restriction, inverse projection, integration and bounded
Hom-transpose squares with their actual comparison units. It quantifies over all
annihilating exponents, so no divisibility hypothesis is introduced. -/
theorem coordinate_site_comparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    FiniteTypeSiteCompatibility P (P.level - 1) Y aY d (coordinateModule Y d) := by
  exact finiteTypeSiteComparison P (P.level - 1) Y aY d (coordinateModule Y d)

/-- The frame prefix whose final map is the explicit ordered trace on the coordinate
coefficient A_X(d)[2d]. All preceding arrows are the canonical compact-support exchange
and normalized finite Tate pullback, with no independent orientation.
Source: trivial-frame integration formula
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def framedTraceFixed (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hA t T hT)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ)
    (e : VectorBundleZeroSection.Trivialization Y d (coordinateModule Y d) ⊤) :=
  Etale.vectorIntegrationLocalTrace N hN A hA t D Y hY d (coordinateModule Y d) ⊤ e

/-- The ordered counit trace is exactly the specified vector integration in every
linear frame of the trivial coordinate bundle, including dimension zero.
Source: def-amb-vector-integration, its local normalization
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: apply VectorIntegrationNormalization to the entire-base frame. Its local map
is exchange, vectorIntegrationChartCoefficient, inverse tower comparison, and the ordered
counit. Insert coefficientComparison followed by its inverse. Naturality of compact
support cancels these maps, leaving exactly framedTrace. Every finite quotient and
empty base is covered by the same normalization; no generator of a Tate line is chosen. -/
theorem trivial_frame_integration (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) [IsNoetherian Y] (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ)
    (e : VectorBundleZeroSection.Trivialization Y d (coordinateModule Y d) ⊤) :
    (Etale.ordinaryFinitePullback (AffineLinePurity.Ring P) (⊤ : Y.Opens).ι).map
        (Etale.vectorBundleIntegration (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P)
            (annihilates P)
          Y (exponentUnit P Y aY) d (coordinateModule Y d)) ≫
      (Etale.ordinaryFiniteUnitPullback (AffineLinePurity.Ring P) (⊤ : Y.Opens).ι).hom =
        framedTraceFixed (AffineLinePurity.Ring P) (exponent P)
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (annihilates P)
          (transport P) (projectiveDatum P) Y (exponentUnit P Y aY) d e := by
  exact (Etale.existsUnique_vectorIntegrationGluing (exponent P)
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) (AffineLinePurity.Ring P)
    (annihilates P) Y (exponentUnit P Y aY) d (coordinateModule Y d)).2.exists.choose_spec.2
      (transport P) (projectiveDatum P) ⊤ e

/-- Coefficient-first standing canonical projection, with its compactification explicit.
Source: def-exchange-projection, two canonical tensor symmetries
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def standingProjection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : C A X) (H : C A Y) :
    ((tensor A Y).obj H).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        (((tensor A X).obj ((inverseImage A f).obj H)).obj M) :=
  projection (ModuleCat.{u + 1} A) (HasCompactification.compactification f) M H

/-- The pro-etale projection-composition equation with the actual origin compositor.
Its only domain witnesses are those needed to evaluate that given compositor.
Source: displayed PF equation
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ProProjectionCompositionEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (M : C A X) (H : C A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hT : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (((tensor A X).obj ((inverseImage A f).obj ((inverseImage A g).obj H))).obj M)) :
    Prop :=
  standingProjection A g ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) H ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      (standingProjection A f M ((inverseImage A g).obj H)) ≫
    (originCompositionAmbient A f g).hom.app ⟨_, hT⟩ =
  ((tensor A Y).obj H).map ((originCompositionAmbient A f g).hom.app ⟨M, hM⟩) ≫
    standingProjection A (f ≫ g) M H ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
      (((tensor A X).map ((inverseImageComp A f g).hom.app H)).app M)

/-- The composition equation for every source on its actual witnessed domain.
Source: the projection composition display
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ProProjectionCompositionLaw (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ Y)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] : Prop :=
  ∀ (M : C A X) (H : C A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hT : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X
      (((tensor A X).obj ((inverseImage A f).obj ((inverseImage A g).obj H))).obj M)),
    ProProjectionCompositionEquation A f g M H hM hT

/-- Coordinate-domain specialization with compactifiability supplied by geometry.
Source: displayed PF composition equation
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def CoordinateProjectionComposition (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) : Prop :=
  letI : HasCompactification (iteratedAffineLineProj Y d) := (projection_geometry Y d).2
  letI : HasCompactification (iteratedAffineLineProj Y (d + 1)) :=
    (projection_geometry Y (d + 1)).2
  letI : HasCompactification (lastProjection Y d ≫ iteratedAffineLineProj Y d) :=
    HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 1))
      (iteratedAffineLineProj_succ Y d)
  ProProjectionCompositionLaw (AffineLinePurity.Ring P) (lastProjection Y d)
    (iteratedAffineLineProj Y d)

/-- The displayed projection formula composition on the witnessed coordinate domain.
Source: actual compositor and projection composition clauses
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: choose bounded ordinary antecedents for the two witnessed sources. The ordinary
projection-composition law holds for the last line and tower projection. The canonical
proper and open site comparisons transport each projection map, while the compositor
square identifies the transported compositor with originCompositionAmbient. Full
faithfulness on bounded ordinary targets reflects equality. Changing the witnesses does
not change the ambient arrows, because the compositor is descended on the full origin
subcategory. Reassociate and insert the canonical tensor symmetries. -/
theorem pro_coordinate_projection_composition (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    CoordinateProjectionComposition P Y d := by
  sorry

/-- The displayed composition law for the ordinary canonical projection maps.
Source: the PF composition display, retaining the exact inverse-image compositor
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def OrdinaryProjectionCompositionEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) : Prop :=
  (Etale.compactSupportProjectionMap A g
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) H ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
      (Etale.compactSupportProjectionMap A f M
        ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj H)) ≫
    (Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj H))).obj M)) =
  (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).map
      ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
    Etale.compactSupportProjectionMap A (f ≫ g) M H ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.unboundedEtaleUpperStarCompIso A f g).hom.app H)).app M))

/-- The site-compositor square for the actual normalized compactification maps.
The proMap contains originCompositionAmbient, through its specified etale model.
Source: the actual alpha_m clause and compact-support site-coherence square
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def CompositionSiteEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} {f : X ⟶ T} {g : T ⟶ Y} [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (b : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) : Prop :=
  (coherenceBoundedSiteFunctor A Y).map
      (coherenceCompositionData A c b e L).etaleIso.hom ≫
        (coherenceBoundaryComponent A e L).hom =
    (coherenceCompositionSource A c b L).hom ≫
      (coherenceCompositionData A c b e L).proMap

section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- The literal pro-etale compactification tensor-action equation before specializing
its coefficient category. Keeping that category as a parameter shares the canonical
derived tensor and inverse-image structures across all occurrences of the equation.
Source: compactification tensor-action identity
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ProTensorActionEquationForCategory
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) : Prop :=
    (projectionActionAssociator A Y
      ((rightDerivedLowerShriekOfCompactification A c).obj M) N₁
      N₂).hom ≫
      (((projectionMapOfCompactification A c).app M).app
        (((derivedTensor A Y).obj N₁).obj N₂)) ≫
      (rightDerivedLowerShriekOfCompactification A c).map
        (((derivedTensor A X).obj M).map
            (leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (projectionActionAssociator A X M (L((f)^*[A]).obj N₁) (L((f)^*[A]).obj N₂)).inv) =
    ((derivedTensor A Y).map (((projectionMapOfCompactification
      A c).app M).app N₁)).app N₂ ≫
      (((projectionMapOfCompactification A c).app (((derivedTensor
        A X).obj M).obj (L((f)^*[A]).obj N₁))).app N₂)

private theorem coordinate_pro_action
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N₁ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    ProTensorActionEquationForCategory A f c M N₁ N₂ := by
  exact ProEtale.genericProjectionAction_compactification A f c M N₁ N₂

/-- The literal ordinary etale compactification tensor-action equation before specializing
its coefficient category. Keeping that category as a parameter shares the canonical
derived tensor and inverse-image structures across all occurrences of the equation.
Source: compactification tensor-action identity
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def OrdinaryTensorActionEquationForCategory
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) : Prop :=
    (Etale.derivedTensorAssociator A Y
      ((Etale.rightDerivedLowerShriekOfCompactification A c).obj M) N₁
      N₂).hom ≫
      (((Etale.projectionMapOfCompactification A c).app M).app
        (((Etale.derivedTensor A Y).obj N₁).obj N₂)) ≫
      (Etale.rightDerivedLowerShriekOfCompactification A c).map
        (((Etale.derivedTensor A X).obj M).map
            (Etale.leftDerivedUpperStarTensorIso A f N₁ N₂).hom ≫
          (Etale.derivedTensorAssociator A X M
            ((Etale.upperStar A f).leftDerivedFunctor.obj N₁)
            ((Etale.upperStar A f).leftDerivedFunctor.obj N₂)).inv) =
    ((Etale.derivedTensor A Y).map (((Etale.projectionMapOfCompactification
      A c).app M).app N₁)).app N₂ ≫
      (((Etale.projectionMapOfCompactification A c).app (((Etale.derivedTensor
        A X).obj M).obj ((Etale.upperStar A f).leftDerivedFunctor.obj N₁))).app N₂)

private theorem coordinate_ordinary_action
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N₁ N₂ : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    OrdinaryTensorActionEquationForCategory A f c M N₁ N₂ := by
  exact Etale.genericProjectionAction_compactification A f c M N₁ N₂

/-- Compactification tensor-action with its literal canonical associators.
Source: compactification tensor-action identity
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def ProTensorActionEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (M : C A X) (N₁ N₂ : C A Y) : Prop :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  ProTensorActionEquationForCategory (ModuleCat.{u + 1} A) f c M N₁ N₂

/-- The same tensor-action equation before the change of site.
Source: ordinary compactification tensor-action identity
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def OrdinaryTensorActionEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (N₁ N₂ : Etale.DerivedCategoryModule A Y) : Prop :=
  letI : IsNoetherianRing A := isNoetherian_of_finite A A
  OrdinaryTensorActionEquationForCategory (ModuleCat.{u + 1} A) f c M N₁ N₂

end

/-- The coordinate specialization of the compositor, projection and action assertions.
Quantification over compactification presentations includes the ordered product of P1's;
all maps are the normalized proper/open maps, with no isomorphism chosen as a parameter.
Source: the first two displayed coherence assertions
(blueprint: lem-pur-affine-ordered-integration-transposes). -/
def CoordinateCoherence (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) : Prop :=
  letI : IsNoetherian Y := tower_noetherian P Y aY 0
  letI : IsNoetherian (iteratedAffineLine Y d) := tower_noetherian P Y aY d
  letI : IsNoetherian (iteratedAffineLine Y (d + 1)) := tower_noetherian P Y aY (d + 1)
  letI : IsNoetherian (AffineSpace PUnit.{u + 1} (iteratedAffineLine Y d)) :=
    isNoetherian_of_locallyOfFiniteType
      (AffineSpace PUnit.{u + 1} (iteratedAffineLine Y d) ↘ iteratedAffineLine Y d)
  letI := (projection_geometry Y d).1
  letI := (projection_geometry Y d).2
  (∀ (c : Compactification (lastProjection Y d))
      (b : Compactification (iteratedAffineLineProj Y d))
      (e : Compactification (lastProjection Y d ≫ iteratedAffineLineProj Y d))
      (L : DerivedCategory.Plus (Sheaf (iteratedAffineLine Y (d + 1)).smallEtaleTopology
        (ModuleCat.{u + 1} (AffineLinePurity.Ring P)))), CompositionSiteEquation
          (AffineLinePurity.Ring P) c b e L) ∧
  (∀ (M : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) (iteratedAffineLine Y (d + 1)))
      (H : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y),
    OrdinaryProjectionCompositionEquation (AffineLinePurity.Ring P) (lastProjection Y d)
      (iteratedAffineLineProj Y d) M H) ∧
  (∀ (c : Compactification (iteratedAffineLineProj Y d))
      (M : C (AffineLinePurity.Ring P) (iteratedAffineLine Y d)) (N₁ N₂ : D P Y),
    ProTensorActionEquation (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d) c M N₁ N₂) ∧
  (∀ (c : Compactification (iteratedAffineLineProj Y d))
      (M : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) (iteratedAffineLine Y d))
      (N₁ N₂ : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y),
    OrdinaryTensorActionEquation (AffineLinePurity.Ring P) (iteratedAffineLineProj Y d) c M N₁ N₂)

section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section

attribute [local irreducible] Etale.compactSupportProjectionMap
  Etale.unboundedEtaleLowerShriekCompIso Etale.unboundedEtaleUpperStarCompIso
  Etale.derivedTensor Etale.rightDerivedLowerShriek Etale.upperStar

private theorem coordinate_ordinary_projection (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    OrdinaryProjectionCompositionEquation A f g M H := by
  exact Etale.compactSupportProjectionMap_comp_forward A f g M H

end

section

attribute [local irreducible] coherenceCompositionDataOfChoice coherenceBoundaryComponent
  coherenceCompositionSource coherenceEtaleFunctor coherenceProEtaleFunctor coherenceSiteFunctor
  coherenceBoundedSiteFunctor

set_option linter.style.haveILetI false in
private theorem coordinate_site_square (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    {f : X ⟶ T} {g : T ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (b : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompositionSiteEquation A c b e L := by
  letI := c.hasCompactification
  letI := b.hasCompactification
  letI := e.hasCompactification
  exact composition_data_coherent A c b e L

end

/-- The coordinate compactification compositor, projection and tensor-action coherences.
Source: the actual-alpha and projection displays
(blueprint: lem-pur-affine-ordered-integration-transposes).
Proof: apply compact-support site coherence to the last line and the preceding tower
projection, with the supplied compactifications. Its proMap contains the specified
origin compositor, so this identifies the actual alpha, rather than a bare isomorphism.
Apply compactSupportProjectionMap_comp on the ordinary site. The finite projection-action
laws give both tensor-action equations, retaining their literal associators and pullback
comparisons. The required Noetherian hypotheses follow from finite type over P.field.k.
The last projection and the preceding tower projection have the separated finite-type
compactification structures supplied by projection_geometry. All compactifications in
the statement are arbitrary, including the ordered product presentation. -/
theorem coordinate_coherence (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    CoordinateCoherence P Y aY d := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : IsNoetherian (iteratedAffineLine Y d) := tower_noetherian P Y aY d
  let : IsNoetherian (iteratedAffineLine Y (d + 1)) := tower_noetherian P Y aY (d + 1)
  let : IsNoetherian (AffineSpace PUnit.{u + 1} (iteratedAffineLine Y d)) :=
    isNoetherian_of_locallyOfFiniteType
      (AffineSpace PUnit.{u + 1} (iteratedAffineLine Y d) ↘ iteratedAffineLine Y d)
  let := (projection_geometry Y d).1
  let := (projection_geometry Y d).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c b e L
    exact coordinate_site_square (AffineLinePurity.Ring P) c b e L
  · intro M H
    exact coordinate_ordinary_projection (AffineLinePurity.Ring P)
      (lastProjection Y d) (iteratedAffineLineProj Y d) M H
  · intro c M N₁ N₂
    let : IsNoetherianRing (AffineLinePurity.Ring P) :=
      isNoetherian_of_finite _ _
    exact coordinate_pro_action (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLineProj Y d) c M N₁ N₂
  · intro c M N₁ N₂
    let : IsNoetherianRing (AffineLinePurity.Ring P) :=
      isNoetherian_of_finite _ _
    exact coordinate_ordinary_action (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLineProj Y d) c M N₁ N₂

end

attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction

private theorem integrationTranspose_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    HEq (integrationTranspose P Y aY K Ke hKe eK 0) (𝟙 K.obj) := by
  unfold integrationTranspose
  exact (integrationTranspose_existsUnique P Y aY K Ke hKe eK 0).exists.choose_spec

private theorem lineComparison_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (K : Plus (AffineLinePurity.Ring P) T)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) T)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) T Ke)
    (eK : (comparison (AffineLinePurity.Ring P) T).obj Ke ≅ K.obj) :
    IsIso (lineComparison P T aT K Ke hKe eK) := by
  let : IsNoetherian T := isNoetherian_of_locallyOfFiniteType aT
  obtain ⟨hT, _, h⟩ :=
    (CoordinateLine.coordinateLineAdjunction P T aT).2.2.2.2.2.1 P.level (annihilates P)
  have := (h K Ke hKe eK).2
  unfold lineComparison
  infer_instance

private theorem exceptionalComposite_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (d : ℕ) :
    IsIso (exceptionalComposite P Y aY K d) := by
  have he : HEq (exceptionalComposite P Y aY K d)
      (exceptionalCompositeRaw P Y aY K d).2.2 := by
    unfold exceptionalComposite
    exact (exceptionalComposite_existsUnique P Y aY K d).exists.choose_spec
  cases d with
  | zero =>
    have he' : exceptionalComposite P Y aY K 0 =
        (exceptionalCompositeRaw P Y aY K 0).2.2 := by
      unfold exceptional
      exact eq_of_heq he
    rw [he']
    let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    change IsIso ((rightDerivedUpperShriekCongr
      (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (Category.comp_id (lastProjection Y 0)).symm).hom.app K.obj)
    exact NatIso.hom_app_isIso _ _
  | succ d =>
    let : HasCompactification (iteratedAffineLineProj Y (d + 1)) :=
      (projection_geometry Y (d + 1)).2
    let : HasCompactification (iteratedAffineLineProj Y (d + 2)) :=
      (projection_geometry Y (d + 2)).2
    let : HasCompactification
        (lastProjection Y (d + 1) ≫ iteratedAffineLineProj Y (d + 1)) :=
      HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 2))
        (iteratedAffineLineProj_succ Y (d + 1))
    let : IsNoetherian Y := tower_noetherian P Y aY 0
    let : IsNoetherian (iteratedAffineLine Y (d + 1)) := tower_noetherian P Y aY (d + 1)
    unfold exceptional at he ⊢
    rw [eq_of_heq he]
    exact AffineZeroPurity.compositionInverse_isIso (AffineLinePurity.Ring P)
      (lastProjection Y (d + 1)) (iteratedAffineLineProj Y (d + 1)) K

/-- Ordered affine integration transposes equal the recorded ordered affine comparisons.
The exceptional conjugate is the one built from originCompositionAmbient, and its inverse
is exactly exceptionalComposite. The recursion and naturality are evaluated at Rp_d!K.
Source: main-20261015, projection-purity-agreement proof, final paragraph
(blueprint: lem-pur-affine-ordered-integration-transposes).

Proof:
1. Work first on ordinary etale sites at exponent ell^(level+1), which annihilates A
without any ramification divisibility restriction. Finite type makes all coordinate
and projective compactification spaces Noetherian. The normalized proper/open tower
comparison is transported to the actual originCompositionAmbient by
lem-pur-compact-support-site-coherence, with the retained bounded-below witnesses.
2. Apply lem-amb-shriek-tensor-composition and lem-sf-composition-projection-mate to the
last coordinate and preceding projection. They give the displayed PF composition
identity. The compactification tensor-action identity is clause 3 of
lem-pur-finite-projection-action-laws. The ordinary projections are invertible by
lem-sf-etale-ambient-adjoint-projection; invert only those projections or their bounded
constructible compared components.
3. Compose the normalized projective-line adjunction with the open adjunction.
The open tensor/counit action law and naturality of proper projection rewrite its
counit as (1_H tensor I_S) Pi. Here I_S is precisely restriction of the projective trace
by the open counit. The finite Tate pullback comparison identifies its coefficient.
This works at every positive finite level, without flatness over the Kummer ring.
4. Induct on the coordinates. At zero the adjunction and trace are identities. Apply
lem-pur-composite-integration-counit to the induction hypothesis and the line formula.
Tate additivity and the even shifts identify the new coefficient. The trace at A is
exactly the ordered counit of lem-amb-affine-space-top-trace, hence the specified vector
integration in its trivial frame.
5. Use lem-pur-vector-integration-site-comparison and
lem-pur-finite-site-counit-projection-transport to carry the trace, projection,
counit and exceptional transpose equations to the pro-etale site. Their comparison
squares preserve the actual adjunctions and reflect equality independently of origin.
6. The existing coordinate-line adjunction makes each exceptional line comparison
invertible. The exceptional compositor is invertible by the proved relative-Hom
composition argument, with the identity normalization at zero. Pullback finite-Tor
preservation and tensor finite-Tor preservation supply the retained origins.
7. Apply lem-pur-integration-transpose-composition. Its trace contraction is Step 4;
its projection composition is Step 2. Transport its right mate using Step 5. This gives
the successor formula with the exact c_d and I_d of def-pur-affine-space-comparison.
Induction identifies P with that definition's Gamma and proves invertibility from
the line and compositor isomorphisms.
8. Extract arbitrary-arrow line naturality from dimension-one ordered naturality by
cancelling its source and exceptional normalization isomorphisms. Apply this to P
to obtain the stated square at the actual
exceptional target. Every source shift is 2 or 2d, so the block permutation sign is +1.
The identity adjunction handles rank zero. Zero coefficients K and empty bases have
only the corresponding zero arrows, and none of the constructions excludes them. -/
theorem ordered_integration_transposes (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y) (Ke : Etale.DerivedCategoryModule
      (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    (∀ d : ℕ, integrationTranspose P Y aY K Ke hKe eK d =
      affineSpacePurityComparison P Y aY K Ke hKe eK d) ∧
    (∀ d : ℕ, IsIso (integrationTranspose P Y aY K Ke hKe eK d)) ∧
    (∀ d : ℕ, IsIso (exceptionalComposite P Y aY K d)) ∧
    (∀ d : ℕ, integrationTranspose P Y aY K Ke hKe eK (d + 1) =
      (sourceReassociation P Y aY K.obj d).hom ≫
        (lineSource P (iteratedAffineLine Y d)).map
          (integrationTranspose P Y aY K Ke hKe eK d) ≫
        exceptionalLine P Y aY K Ke hKe eK d ≫ exceptionalComposite P Y aY K d) ∧
    (∀ d : ℕ,
      (lineSource P (iteratedAffineLine Y d)).map
          (integrationTranspose P Y aY K Ke hKe eK d) ≫
        exceptionalLine P Y aY K Ke hKe eK d =
      sourceLine P Y aY K Ke hKe eK d ≫
        (rightDerivedUpperShriek (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) (lastProjection Y
          d)).map
          (integrationTranspose P Y aY K Ke hKe eK d)) ∧
    HEq (integrationTranspose P Y aY K Ke hKe eK 0) (𝟙 K.obj) := by
  have hzero := integrationTranspose_zero P Y aY K Ke hKe eK
  have hsucc := integrationTranspose_successor P Y aY K Ke hKe eK
  have hcomp := exceptionalComposite_isIso P Y aY K
  have hline (d : ℕ) : IsIso (exceptionalLine P Y aY K Ke hKe eK d) := by
    let : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
    let : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
    let : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
    exact lineComparison_isIso P (iteratedAffineLine Y d) (towerBase aY d)
      ⟨_, (stage_applicability P Y aY K Ke hKe eK d).1⟩
      (stageEtale P Y K.obj Ke d) (stage_applicability P Y aY K Ke hKe eK d).2
      (stageComparison P Y K.obj Ke eK d)
  refine ⟨?_, ?_, hcomp, hsucc, ?_, hzero⟩
  · intro d
    induction d with
    | zero =>
      unfold affineSpacePurityComparison orderedRec comparisonZero
      unfold ComparisonHom orderedSource exceptional
      exact eq_of_heq hzero
    | succ d ih =>
      rw [hsucc d, ih]
      rfl
  · intro d
    induction d with
    | zero =>
      have hz : integrationTranspose P Y aY K Ke hKe eK 0 = 𝟙 K.obj :=
        eq_of_heq hzero
      rw [hz]
      exact IsIso.id K.obj
    | succ d ih =>
      rw [hsucc d]
      have := hcomp d
      have := hline d
      infer_instance
  · intro d
    let : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
    let : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
    let : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
    exact lineComparison_natural P (iteratedAffineLine Y d) (towerBase aY d)
      ⟨_, (source_applicability P Y aY K Ke hKe eK d).1⟩ (sourceEtale P Y Ke d)
      (source_applicability P Y aY K Ke hKe eK d).2 (sourceRealization P Y K.obj Ke eK d)
      ⟨_, (stage_applicability P Y aY K Ke hKe eK d).1⟩ (stageEtale P Y K.obj Ke d)
      (stage_applicability P Y aY K Ke hKe eK d).2 (stageComparison P Y K.obj Ke eK d)
      (integrationTranspose P Y aY K Ke hKe eK d)

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
