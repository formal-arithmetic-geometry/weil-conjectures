module

public import Sheaf.Paper.CompletedCoefficientPushforwardComparison
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Paper.AugmentedDiagramProjectionMate
import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! # Direct image and reduction on adjunction Hom groups

Source: blueprint, prop-sf-closed-unit-all-stages, integral-stage paragraph;
Stacks Tags 0B56, 07A6 and 0D6E
(blueprint: lem-sf-direct-image-reduction-hom-square).

Index n denotes the positive exponent n+1. All categories are ordinary unbounded
module derived categories on the original small pro-etale sites. The normalized
models retain their localization comparisons; changing such a model only transports
the formulas through the uniquely normalized comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedCoefficientPushforward
namespace WeilConjectures.DirectImageReductionHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The unique comparison between two termwise localizations of the same restriction.
Source: Stacks 05RU, 03CZ (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def restrictionIso (W : Scheme.{t}) (S : SiteCoefficientData l E W) (n : ℕ) :
    (S.V n).functor ≅ scalarReductionDerivedRestriction l E W n :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (scalarReductionTarget l E W n) (.up ℤ))
    (DerivedCategory (scalarReductionSource l E W))).preimageIso
      ((S.V n).factors ≪≫ (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.symm)

/-- The actual normalized scalar adjunction, transported to the recorded restriction model.
Source: Stacks 07A6 (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def scalarAdjunction (W : Scheme.{t}) (S : SiteCoefficientData l E W) (n : ℕ) :
    scalarReductionDerivedExtension l E W n ⊣ (S.V n).functor :=
  (Classical.choose (derivedScalarExtensionRestrictionAdjunction l E W n)).ofNatIsoRight
    (restrictionIso l E W S n).symm

variable {Z X : Scheme.{t}} (f : Z ⟶ X) (D : ComparisonData l E f)

/-- The recorded finite derived image with its stored additivity instance made explicit.
Source: Stacks 0D6E (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def finiteImage (n : ℕ) :
    DerivedCategory (scalarReductionTarget l E Z n) ⥤
      DerivedCategory (scalarReductionTarget l E X n) :=
  letI := D.finiteAdditive n
  (D.finiteImage n).functor

/-- The completed-direct-image / finite-restriction comparison, in the direction alpha.
Source: Stacks 0D6E (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def alpha (n : ℕ) :
    (D.source.V n).functor ⋙ D.completedImage.functor ≅
      finiteImage l E f D n ⋙ (D.target.V n).functor :=
  letI := D.finiteAdditive n
  (D.finiteSquare n).comparison.symm

/-- The ordinary geometric module inverse image, using Mathlib's sheafified
presheaf pullback. Its adjunction fixes the scalar action and tensor balancing.
Source: Stacks 03EK, 03DA
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
abbrev geometricPull
    {B : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}}
    {C : Sheaf (Scheme.ProEt.topology Z) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj C) : Mod X B ⥤ Mod Z C :=
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes c
  SheafOfModules.pullback.{max u (t + 1)} c

/-- The ordinary geometric module adjunction supplied by the existing Kan-extension
and sheafification construction in the original independent universes.
Source: Stacks 03EK, 03D7
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def geometricOrdinaryAdjunction
    {B : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}}
    {C : Sheaf (Scheme.ProEt.topology Z) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj C) : geometricPull f c ⊣ push f c :=
  letI := SheafOfModules.module_pushforward_isRightAdjoint_of_universes c
  SheafOfModules.pullbackPushforwardAdjunction c

/-- Geometric module inverse image is additive.
Source: Stacks 03EK (blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: the presheaf pullback and module sheafification preserve sums, so the
adjointly identified Mathlib pullback preserves addition of morphisms. -/
theorem geometricPull_additive
    {B : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}}
    {C : Sheaf (Scheme.ProEt.topology Z) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj C) : (geometricPull f c).Additive := by
  sorry

attribute [instance] geometricPull_additive scalarReductionExtensionAdditive

/-- Completed geometric inverse image is left exact because the profinite coefficient
comparison identifies the pulled-back completion with the source completion.
Source: Stacks 099N, 03EK; profinite coefficient inverse image
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: use structureProjection and the universal limit to identify structureMap
with the canonical completed structural map. The finite-ring inverse-image theorem
identifies its inverse-image ring map with an isomorphism. Module pullback is then
ordinary inverse image, which preserves kernels. -/
theorem completedPull_limits : PreservesFiniteLimits (geometricPull f D.structureMap) := by
  sorry

/-- Geometric module inverse image preserves cokernels by its ordinary adjunction.
Source: Stacks 03EK (blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: Mathlib's pullback is left adjoint to the actual sectionwise pushforward,
so it preserves all colimits, in particular finite colimits. -/
theorem completedPull_colimits : PreservesFiniteColimits (geometricPull f D.structureMap) := by
  sorry

/-- The finite constant coefficient inverse-image comparison is an isomorphism,
so finite-coefficient geometric pullback is left exact.
Source: Stacks 03EK; profinite coefficient inverse image
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: the finite coefficient sheaf pulls back to the same finite constant ring.
Thus geometric module pullback is inverse image on the underlying abelian sheaf,
which preserves kernels. -/
theorem finitePull_limits (n : ℕ) :
    PreservesFiniteLimits (geometricPull f (finiteStructure l E f n)) := by
  sorry

/-- Finite-coefficient geometric pullback preserves finite colimits.
Source: Stacks 03EK (blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: apply colimit preservation of Mathlib's ordinary pullback/pushforward adjunction. -/
theorem finitePull_colimits (n : ℕ) :
    PreservesFiniteColimits (geometricPull f (finiteStructure l E f n)) := by
  sorry

attribute [instance] completedPull_limits completedPull_colimits
  finitePull_limits finitePull_colimits

/-- The geometric derived adjunction is uniquely normalized by the ordinary
geometric adjunction and the recorded universal right-derived unit. In particular
its counit is the actual geometric counit, rather than an arbitrary adjunction.
Source: Stacks 07A6, 0D6E
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: derive the exact ordinary geometric inverse-image adjunction. Compare its
right derived functor with the recorded RightImage by the unique comparison
preserving the universal unit. Transport the adjunction through this comparison.
The displayed formula is the derived Hom formula with identity denominators.
It determines the derived unit by taking N to be the pulled-back M and g the
identity, hence determines the whole adjunction. -/
theorem geometricAdjunction_existsUnique
    {B : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}}
    {C : Sheaf (Scheme.ProEt.topology Z) RingCat.{max u (t + 1)}}
    (c : B ⟶ (ringPush.{t, u} f).obj C) [(push f c).Additive]
    [PreservesFiniteLimits (geometricPull f c)]
    [PreservesFiniteColimits (geometricPull f c)] (G : RightImage (push f c)) :
    ∃! a : (geometricPull f c).mapDerivedCategory ⊣ G.functor,
      ∀ (M : CochainComplex (Mod X B) ℤ) (N : CochainComplex (Mod Z C) ℤ)
        (g : ((geometricPull f c).mapHomologicalComplex (.up ℤ)).obj M ⟶ N),
        a.homEquiv (DerivedCategory.Q.obj M) (DerivedCategory.Q.obj N)
            ((geometricPull f c).mapDerivedCategoryFactors.hom.app M ≫
              DerivedCategory.Q.map g) =
          DerivedCategory.Q.map
              (((geometricOrdinaryAdjunction f c).mapHomologicalComplex
                (.up ℤ)).homEquiv _ _ g) ≫ G.unit.app N := by
  sorry

/-- The normalized completed geometric derived adjunction.
Source: Stacks 07A6 (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def completedGeometricAdjunction :
    (geometricPull f D.structureMap).mapDerivedCategory ⊣ D.completedImage.functor :=
  (geometricAdjunction_existsUnique f D.structureMap D.completedImage).exists.choose

/-- The normalized finite geometric derived adjunction.
Source: Stacks 07A6 (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def finiteGeometricAdjunction (n : ℕ) :
    (geometricPull f (finiteStructure l E f n)).mapDerivedCategory ⊣
      finiteImage l E f D n :=
  letI := D.finiteAdditive n
  (geometricAdjunction_existsUnique f (finiteStructure l E f n)
    (D.finiteImage n)).exists.choose

/-- Ordinary pullback/tensor balancing, fixed by the sectionwise-identity ordinary
coefficient square. This uses no derived comparison alpha and no scalar derived unit.
Source: Stacks 03EK, 07A4 (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def ordinaryTensorPull (n : ℕ) :
    scalarReductionExtension l E X n ⋙ geometricPull f (finiteStructure l E f n) ≅
      geometricPull f D.structureMap ⋙ scalarReductionExtension l E Z n :=
  letI := D.finiteAdditive n
  letI := scalarReductionExtensionAdditive l E Z n
  letI := scalarReductionExtensionAdditive l E X n
  (conjugateIsoEquiv
    ((geometricOrdinaryAdjunction f D.structureMap).comp
      (Classical.choose (scalarReductionExtension_adjunction l E Z n)))
    ((Classical.choose (scalarReductionExtension_adjunction l E X n)).comp
      (geometricOrdinaryAdjunction f (finiteStructure l E f n)))).symm
        (D.finiteSquare n).ordinary.symm

/-- Apply ordinary balancing degree by degree, retaining the two successive
complex functors rather than introducing a new composite tensor functor.
Source: Stacks 07A4 (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def ordinaryTensorPullComplex (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E X) ℤ) :
    ((geometricPull f (finiteStructure l E f n)).mapHomologicalComplex (.up ℤ)).obj
      (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) ⟶
    ((scalarReductionExtension l E Z n).mapHomologicalComplex (.up ℤ)).obj
      (((geometricPull f D.structureMap).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := (ordinaryTensorPull l E f D n).hom.app (P.X i)
  comm' i j _ := ((ordinaryTensorPull l E f D n).hom.naturality (P.d i j)).symm

/-- The universal scalar-extension comparison on cochain representatives, with
only the canonical homotopy-quotient factorization isomorphisms inserted.
Source: Stacks 06YY (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def scalarCochainCounit (W : Scheme.{t}) (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) :
    (scalarReductionDerivedExtension l E W n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (scalarReductionDerivedExtension l E W n).map
      ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
    (scalarReductionCounit l E W n).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((scalarReductionExtension l E W n).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
    (DerivedCategory.quotientCompQhIso _).hom.app
      (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P)

/-- The derived pullback/tensor comparison is uniquely specified by the ordinary
balancing map and the universal scalar-extension counits. This normalization is
independent of the derived direct-image comparison and of its proposed unit equation.
Source: Stacks 07A4, 0B56
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: compute on flat-term K-flat resolutions. Geometric pullback preserves flat
terms and K-flatness because its coefficient ring map is an isomorphism. Ordinary
balancing identifies both computed complexes, with the displayed counit equation.
The universal left-derived comparison extends this map to every object; its inverse
is induced by inverse ordinary balancing. K-flat representatives and the invertible
computation counits determine the comparison uniquely. -/
theorem tensorPull_existsUnique (n : ℕ) :
    ∃! e : scalarReductionDerivedExtension l E X n ⋙
        (geometricPull f (finiteStructure l E f n)).mapDerivedCategory ≅
      (geometricPull f D.structureMap).mapDerivedCategory ⋙
        scalarReductionDerivedExtension l E Z n,
      ∀ P : CochainComplex (scalarReductionSource l E X) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (scalarReductionDerivedExtension l E Z n).map
              ((geometricPull f D.structureMap).mapDerivedCategoryFactors.hom.app P) ≫
            scalarCochainCounit l E Z n
              (((geometricPull f D.structureMap).mapHomologicalComplex (.up ℤ)).obj P) =
          (geometricPull f (finiteStructure l E f n)).mapDerivedCategory.map
              (scalarCochainCounit l E X n P) ≫
            (geometricPull f (finiteStructure l E f n)).mapDerivedCategoryFactors.hom.app
              (((scalarReductionExtension l E X n).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map
              (ordinaryTensorPullComplex l E f D n P) := by
  sorry

/-- The profinite-coefficient derived pullback/tensor comparison, selected by its
unique ordinary-balancing and universal-counit normalization.
Source: Stacks 07A4 (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def tensorPull (n : ℕ) :
    scalarReductionDerivedExtension l E X n ⋙
        (geometricPull f (finiteStructure l E f n)).mapDerivedCategory ≅
      (geometricPull f D.structureMap).mapDerivedCategory ⋙
        scalarReductionDerivedExtension l E Z n :=
  (tensorPull_existsUnique l E f D n).exists.choose

/-- The canonical projection-formula map is the geometric mate of pullback/tensor
balancing. Expanding mateEquiv gives the geometric counit tensored with the finite
coefficient identity, transposed by the finite geometric adjunction. No scalar
unit or alpha occurs in this definition.
Source: Stacks 0B56, equation-projection-formula-map
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def beta (n : ℕ) (K : DerivedCategory (scalarReductionSource l E Z)) :
    (scalarReductionDerivedExtension l E X n).obj (D.completedImage.functor.obj K) ⟶
      (finiteImage l E f D n).obj ((scalarReductionDerivedExtension l E Z n).obj K) :=
  (mateEquiv (completedGeometricAdjunction l E f D)
    (finiteGeometricAdjunction l E f D n)
      (TwoSquare.mk _ _ _ _ (tensorPull l E f D n).hom)).app K

/-- Compute a restricted derived reduction on a specified K-flat representative.
All factors are universal computation or exact localization comparisons.
Source: Stacks 06YY, 05RU (blueprint: lem-sf-direct-image-reduction-hom-square). -/
def restrictedModelIso (W : Scheme.{t}) (S : SiteCoefficientData l E W)
    (K : DerivedCategory (scalarReductionSource l E W))
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W))
    (e : DerivedCategory.Q.obj P ≅ K) (n : ℕ) :
    (S.V n).functor.obj ((scalarReductionDerivedExtension l E W n).obj K) ≅
      DerivedCategory.Q.obj (unrestrictedTowerComplex l E W n P) :=
  (restrictionIso l E W S n).app _ ≪≫
    (scalarReductionDerivedRestriction l E W n).mapIso
      ((scalarReductionDerivedExtension l E W n).mapIso e.symm ≪≫
        (scalarReductionDerivedExtension l E W n).mapIso
          ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
        @asIso _ _ _ _ ((scalarReductionCounit l E W n).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
          (unrestrictedTowerCounit_isIso l E W n P hP) ≪≫
        DerivedCategory.Qh.mapIso
          (((scalarReductionExtension l E W n).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
        (DerivedCategory.quotientCompQhIso _).app (unrestrictedTowerFiniteComplex l E W n P)) ≪≫
    (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.app
      (unrestrictedTowerFiniteComplex l E W n P)

/-- The actual quotient transition, transported from the canonical reduction tower.
The representative and its isomorphism are computational data, not extra mathematical
hypotheses on K; every derived object has such a K-flat representative.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks 06YL
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def representativeTransition (W : Scheme.{t}) (S : SiteCoefficientData l E W)
    (K : DerivedCategory (scalarReductionSource l E W))
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W))
    (e : DerivedCategory.Q.obj P ≅ K) (n : ℕ) :
    (S.V (n + 1)).functor.obj ((scalarReductionDerivedExtension l E W (n + 1)).obj K) ⟶
      (S.V n).functor.obj ((scalarReductionDerivedExtension l E W n).obj K) :=
  (restrictedModelIso l E W S K P hP e (n + 1)).hom ≫
    (canonicalIntegralReductionTower l E W P).map (homOfLE n.le_succ).op ≫
      (restrictedModelIso l E W S K P hP e n).inv


/-- The quotient-linear leg is the transpose of the next quotient unit under the
actual higher scalar adjunction. Composition of restrictions is the normalized
identity on underlying sheaves. This defines the leg without assuming restriction
of scalars is fully faithful.
Source: Stacks 07A6; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def quotientLeg (W : Scheme.{t}) (S : SiteCoefficientData l E W)
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (scalarReductionDerivedExtension l E W (n + 1)).obj K ⟶
      (S.restriction n.le_succ).functor.obj
        ((scalarReductionDerivedExtension l E W n).obj K) :=
  ((scalarAdjunction l E W S (n + 1)).homEquiv _ _).symm
    ((scalarAdjunction l E W S n).unit.app K ≫
      (S.projectionComposition n.le_succ).comparison.inv.app
        ((scalarReductionDerivedExtension l E W n).obj K))

/-- Restrict the actual quotient-linear leg to completed coefficients.
Source: Stacks 07A6; Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def transition (W : Scheme.{t}) (S : SiteCoefficientData l E W)
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (S.V (n + 1)).functor.obj ((scalarReductionDerivedExtension l E W (n + 1)).obj K) ⟶
      (S.V n).functor.obj ((scalarReductionDerivedExtension l E W n).obj K) :=
  (S.V (n + 1)).functor.map (quotientLeg l E W S K n) ≫
    (S.projectionComposition n.le_succ).comparison.hom.app
      ((scalarReductionDerivedExtension l E W n).obj K)

/-- The finite-image transition uses the finite quotient direct-image square, then
composition of scalar restrictions. It is constructed independently of alpha.
Source: Stacks 0D6E; blueprint integral-stage Hom comparison
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def imageTransition (Q : DerivedCategory (scalarReductionSource l E Z)) (n : ℕ) :
    (D.target.V (n + 1)).functor.obj ((finiteImage l E f D (n + 1)).obj
      ((scalarReductionDerivedExtension l E Z (n + 1)).obj Q)) ⟶
    (D.target.V n).functor.obj ((finiteImage l E f D n).obj
      ((scalarReductionDerivedExtension l E Z n).obj Q)) :=
  letI := D.finiteAdditive n
  letI := D.finiteAdditive (n + 1)
  (D.target.V (n + 1)).functor.map
    ((finiteImage l E f D (n + 1)).map
        (quotientLeg l E Z D.source.toSiteCoefficientData Q n) ≫
      (D.quotientSquare n.le_succ).comparison.inv.app
        ((scalarReductionDerivedExtension l E Z n).obj Q)) ≫
    (D.target.projectionComposition n.le_succ).comparison.hom.app
      ((finiteImage l E f D n).obj ((scalarReductionDerivedExtension l E Z n).obj Q))

/-- Transport postcomposition with a specified quotient transition through the two
actual scalar adjunction bijections. This is the finite-coefficient Hom transition.
Source: Stacks 07A6; blueprint integral-stage Hom comparison
(blueprint: lem-sf-direct-image-reduction-hom-square). -/
def homTransition (W : Scheme.{t}) (S : SiteCoefficientData l E W)
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ)
    (M : DerivedCategory (scalarReductionTarget l E W (n + 1)))
    (N : DerivedCategory (scalarReductionTarget l E W n))
    (s : (S.V (n + 1)).functor.obj M ⟶ (S.V n).functor.obj N)
    (u : (scalarReductionDerivedExtension l E W (n + 1)).obj K ⟶ M) :
    (scalarReductionDerivedExtension l E W n).obj K ⟶ N :=
  ((scalarAdjunction l E W S n).homEquiv _ _).symm
    ((scalarAdjunction l E W S (n + 1)).homEquiv _ _ u ≫ s)

/-- The canonical projection mate is invertible and intertwines the scalar-unit
and Hom-transpose maps, for every shift of a complete object.
Source: blueprint prop-sf-closed-unit-all-stages, integral-stage paragraph;
Stacks 0B56, 07A6 and 0D6E
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof:
1. Beta is defined as mateEquiv of the two normalized geometric adjunctions
and tensorPull. The latter is independently fixed by ordinary tensor balancing
and its universal scalar-extension counit equation on cochain representatives.
Thus beta has geometric adjunct equal to the counit tensored with the finite
coefficient identity, exactly Stacks 0B56 and the finite evaluations of the strict
tower projection of prop-weil-pbc-direct-image-limits. Perfectness of the finite
DVR quotients makes it invertible.
2. Evaluate lem-weil-pbc-augmented-diagram-projection-mate at n. The constant tower
comparison evaluates to the identity by the constant-tower normalization theorem,
and its augmentation evaluates to the actual scalar unit. Hence the projection
mate composed with the target unit is the direct image of the source unit.
3. Naturality of the normalized alpha comparison at u, composed with that unit
identity, gives the first equality below. The scalar adjunction transpose formula
is restriction of u composed with its unit, giving the second equality.
All operations are evaluated at P[m]; exact shift comparisons recover P_n[m]
and (FP)[m] in the paper's notation. -/
theorem hom_square (_hZ : IsUnit (l : Γ(Z, ⊤))) (_hX : IsUnit (l : Γ(X, ⊤)))
    (P : DerivedCategory (scalarReductionSource l E Z))
    (_hP : IsDerivedCompleteUnrestricted l E Z P) (m : ℤ) (n : ℕ) :
    IsIso (beta l E f D n (P⟦m⟧)) ∧
      ∀ (M : DerivedCategory (scalarReductionTarget l E Z n))
        (u : (scalarReductionDerivedExtension l E Z n).obj (P⟦m⟧) ⟶ M),
        D.completedImage.functor.map
            ((scalarAdjunction l E Z D.source.toSiteCoefficientData n).unit.app (P⟦m⟧) ≫
              (D.source.V n).functor.map u) ≫ (alpha l E f D n).hom.app M =
          (scalarAdjunction l E X D.target.toSiteCoefficientData n).unit.app
              (D.completedImage.functor.obj (P⟦m⟧)) ≫
            (D.target.V n).functor.map
              (beta l E f D n (P⟦m⟧) ≫ (finiteImage l E f D n).map u) ∧
        D.completedImage.functor.map
            ((scalarAdjunction l E Z D.source.toSiteCoefficientData n).homEquiv _ _ u) ≫
              (alpha l E f D n).hom.app M =
          (scalarAdjunction l E X D.target.toSiteCoefficientData n).homEquiv _ _
            (beta l E f D n (P⟦m⟧) ≫ (finiteImage l E f D n).map u) := by
  sorry

/-- The adjunction-defined quotient transition is the transition of the recorded
canonical reduction tower on every K-flat representative. This fixes the meaning
of the transitions used in hom_square_transitions.
Source: Bhatt--Scholze, Definition 3.5.2; Stacks 06YL and 07A6
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof: compute scalar extension by P. The normalized scalar unit is the
sheafification of x mapped to 1 tensor x. The quotient transition sends s tensor x
to rho(s) tensor x and hence carries the higher unit to the lower unit. Both maps
therefore have the same higher scalar adjunct. Injectivity of that adjunction's
Hom equivalence, followed by the normalized restriction-composition comparison,
gives the equality. The universal K-flat computation and restriction localization
comparisons are exactly restrictedModelIso, so the equation is independent of P. -/
theorem transition_representation (W : Scheme.{t}) (S : SiteCoefficientData l E W)
    (K : DerivedCategory (scalarReductionSource l E W))
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W))
    (e : DerivedCategory.Q.obj P ≅ K) (n : ℕ) :
    transition l E W S K n = representativeTransition l E W S K P hP e n := by
  sorry

/-- Quotient transitions commute with the completed Hom map and, under the actual
scalar adjunction bijections, with the finite Hom map from hom_square.
Source: blueprint prop-sf-closed-unit-all-stages, integral-stage paragraph;
Stacks 07A6 and 0D6E
(blueprint: lem-sf-direct-image-reduction-hom-square).
Proof:
1. The higher scalar transpose of the lower quotient unit defines quotientLeg.
Successive-derived-quotient normalization identifies it with the quotient scalar
unit followed by the successive-reduction comparison. Its restriction is the
actual canonical reduction-tower transition, independently of the representative.
2. Apply projection coherence of the normalized completed-coefficient comparison
to this quotient-linear leg, and use naturality of the finite coefficient square.
This gives alpha_high followed by imageTransition equal to F(transition) followed
by alpha_low. Precomposition with F(h) is the first square below.
3. Transpose a finite u, postcompose with transition, and transpose back using
the lower scalar adjunction. This is exactly homTransition. Apply hom_square
at both levels and the first square to obtain the finite equality below.
This uses bijectivity of the two scalar Hom transposes, never full faithfulness
of scalar restriction. Consecutive squares compose to give all quotient transitions. -/
theorem hom_square_transitions
    (_hZ : IsUnit (l : Γ(Z, ⊤))) (_hX : IsUnit (l : Γ(X, ⊤)))
    (P Q : DerivedCategory (scalarReductionSource l E Z))
    (_hP : IsDerivedCompleteUnrestricted l E Z P)
    (_hQ : IsDerivedCompleteUnrestricted l E Z Q) (m : ℤ) (n : ℕ) :
    (∀ h : P⟦m⟧ ⟶ (D.source.V (n + 1)).functor.obj
        ((scalarReductionDerivedExtension l E Z (n + 1)).obj Q),
      D.completedImage.functor.map
          (h ≫ transition l E Z D.source.toSiteCoefficientData Q n) ≫
            (alpha l E f D n).hom.app ((scalarReductionDerivedExtension l E Z n).obj Q) =
        D.completedImage.functor.map h ≫
          (alpha l E f D (n + 1)).hom.app
            ((scalarReductionDerivedExtension l E Z (n + 1)).obj Q) ≫
              imageTransition l E f D Q n) ∧
    (∀ u : (scalarReductionDerivedExtension l E Z (n + 1)).obj (P⟦m⟧) ⟶
        (scalarReductionDerivedExtension l E Z (n + 1)).obj Q,
      beta l E f D n (P⟦m⟧) ≫ (finiteImage l E f D n).map
          (homTransition l E Z D.source.toSiteCoefficientData (P⟦m⟧) n _ _
            (transition l E Z D.source.toSiteCoefficientData Q n) u) =
        homTransition l E X D.target.toSiteCoefficientData
          (D.completedImage.functor.obj (P⟦m⟧)) n _ _ (imageTransition l E f D Q n)
          (beta l E f D (n + 1) (P⟦m⟧) ≫ (finiteImage l E f D (n + 1)).map u)) := by
  sorry

end WeilConjectures.DirectImageReductionHom
