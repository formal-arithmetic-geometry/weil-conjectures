/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
Definitions moved unchanged by the maintainer L (2026-10-18) out of
IntegralCompactSupportCoefficientComparison.lean
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.CompactSupportRepresentativeIndependence
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import Sheaf.CategoryTheory.CompactSupportRoosCofinality
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.RingTheory.FiniteOverCompleteRing
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.CompletedProjectionCoherence
import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.Paper.CompletedOpenExchangeTransport
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.Paper.IntegralScalarExtensionWellDefined

/-! # Integral compact-support coefficient data

The definitions that other statements use
(moved out of `IntegralCompactSupportCoefficientComparison`,
blueprint: def-pur-integral-compact-support-coefficient-data); the lemma's theorems stay there.

Source: Weil blueprint, sk-thm-purity-transport, Step 3; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).

## Main statements

* `recordedComparisonIso`: the canonical comparison on the recorded support functors.
* `comparisonIso`: its ambient proper/open presentation on the finite-Tor domain.
* `integralCoefficientComparison`: invertibility and constructible completeness.
* `comparison_reduction`, `comparison_quotients`, `comparison_strict_towers`:
  the actual finite maps and strict Roos presentations.
* `comparison_projection`, `comparison_commShift`, `comparison_refinement`:
  projection, shift and normalized compactification compatibility.
* `comparison_identity`, `comparison_composition`: the scalar unit and associativity laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures.PurCompactSupport

/-- Ring sheaves and their inverse-image identifications, used only to organize the
specified completed and finite coefficient constructions below.
Source: Bhatt--Scholze, Sections 6.7--6.8
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
structure Coefficients where
  ring : ∀ W : Scheme.{u}, Sheaf (ProEt.topology W) CommRingCat.{u + 1}
  pull : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj (ring V) ≅ ring U

/-- A compatible map of these coefficient sheaves. The instances below use the actual
completed inclusions and quotient maps, rather than supplying an arbitrary map.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
structure Change (R S : Coefficients.{u}) where
  map : ∀ W : Scheme.{u}, R.ring W ⟶ S.ring W
  square : ∀ {U V : Scheme.{u}} (g : U ⟶ V),
    (R.pull g).hom ≫ map U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (map V) ≫ (S.pull g).hom

/-- Exact open extension for the specified coefficient identification.
Source: Stacks Tags 03DI, 03DJ
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev openExtension (R : Coefficients.{u}) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] :=
  proEtaleRingOpenExtension j (R.ring V) (R.ring U) (R.pull j)

/-- Its specified adjunction to restriction.
Source: Stacks Tag 03DI
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openAdjunction (R : Coefficients.{u}) {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] :
    openExtension R j ⊣ proEtaleRingModulePullback j (R.ring V) (R.ring U) (R.pull j) :=
  Adjunction.ofIsRightAdjoint _

/-- The open scalar-restriction mate, determined by the open adjunction units.
Source: Stacks Tags 03DI, 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openRestrictionMap {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    proEtaleRingRestrictScalars (a.map U) ⋙ openExtension R j ⟶
      openExtension S j ⋙ proEtaleRingRestrictScalars (a.map V) :=
  letI := proEtaleRingRestrictionPullbackInv_isIso
    j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
      (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j)
  ((mateEquiv (openAdjunction S j) (openAdjunction R j)).symm
    (TwoSquare.mk _ _ _ _ (inv (proEtaleRingRestrictionPullbackInv
      j (R.ring V) (S.ring V) (R.ring U) (S.ring U)
        (a.map V) (a.map U) (R.pull j) (S.pull j) (a.square j))))).natTrans

/-- The open mate is invertible. On extension-by-zero summands both it and its inverse
are identity on the underlying section; scalar actions agree by the coefficient square.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: restriction to the open sends the mate to identity by the adjunction triangle
identities. Both sides vanish off the open. The extension-by-zero presheaf has one
summand on an object factoring through the open and no summand otherwise, so the map
is locally the identity and is invertible after sheafification. -/
theorem openRestrictionMap_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    IsIso (openRestrictionMap a j) := by
  sorry

attribute [instance] openRestrictionMap_isIso

/-- Exact descent of the specified open coefficient square.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openRestriction {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
  Functor.mapDerivedCategorySquareIso (asIso (openRestrictionMap a j))

/-- Separately derived proper image after exact extension by zero.
Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def image (R : Coefficients.{u}) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (openExtension R c.i).mapDerivedCategory ⋙
    proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)

/-- Compact-support restriction: the open comparison followed by the canonical
K-injective direct-image comparison. This fixes the normalization before transposition.
Source: Stacks Tags 03DI, 0D6E
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def restriction {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    pbcDerivedRestrict (a.map X) ⋙ image R c ≅
      image S c ⋙ pbcDerivedRestrict (a.map Y) :=
  Functor.isoWhiskerRight (openRestriction a c.i)
      (proEtaleRingDerivedDirectImage c.g (R.ring Y) (R.ring c.Z) (R.pull c.g)) ≪≫
    Functor.isoWhiskerLeft (openExtension S c.i).mapDerivedCategory
      (proEtaleRingRestrictionDerivedDirectImage c.g
        (R.ring Y) (S.ring Y) (R.ring c.Z) (S.ring c.Z)
        (a.map Y) (a.map c.Z) (R.pull c.g) (S.pull c.g) (a.square c.g)).symm

/-- The scalar comparison is the mate of the specified restriction square under the
canonical tensor-unit normalized scalar adjunctions. It therefore has precisely source
C_Y P_R and target P_S C_X.
Source: Stacks Tags 07A6, 0GL6
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def comparison {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    image R c ⋙ pbcDerivedExtend (a.map Y) ⟶
      pbcDerivedExtend (a.map X) ⋙ image S c :=
  ((mateEquiv (pbcDerivedScalarAdjunction (a.map X))
    (pbcDerivedScalarAdjunction (a.map Y))).symm
      (TwoSquare.mk _ _ _ _ (restriction a c).hom)).natTrans

/-- The canonical composition of module direct images, fixed on every section.
Source: Stacks Tags 03D8, 0D6D
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: the fibre-product pasting isomorphism identifies test objects of the two
direct images. Pulling sections across it gives a natural bijection. Coefficient
compatibility makes it linear. Its inverse uses the inverse pasting isomorphism;
sectionwise faithfulness proves uniqueness. -/
theorem modulePushComposition_existsUnique (R : Coefficients.{u})
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    ∃! d : proEtaleRingModuleDirectImage h (R.ring V) (R.ring U) (R.pull h) ⋙
        proEtaleRingModuleDirectImage k (R.ring W) (R.ring V) (R.pull k) ≅
          proEtaleRingModuleDirectImage (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)),
      ∀ (N : pbcModules U (R.ring U)) (T : W.ProEt)
        (m : ((proEtaleRingModuleDirectImage h (R.ring V) (R.ring U) (R.pull h) ⋙
          proEtaleRingModuleDirectImage k (R.ring W) (R.ring V) (R.pull k)).obj N).val.obj
            (op T)),
        (d.hom.app N).val.app (op T) m =
          N.val.map ((MorphismProperty.Over.pullbackComp h k).hom.app T).op m := by
  sorry

/-- Exact derived pullback composition, conjugate to sectionwise direct-image pasting.
Source: Stacks Tags 03D8, 0D6D
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def geometricPullComposition (R : Coefficients.{u})
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W)
    (hc : R.pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      (R.ring W) (R.ring V) (R.ring U) (R.pull k) (R.pull h)) :
    proEtaleRingDerivedPullback (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)) ≅
      proEtaleRingDerivedPullback k (R.ring W) (R.ring V) (R.pull k) ⋙
        proEtaleRingDerivedPullback h (R.ring V) (R.ring U) (R.pull h) :=
  Functor.mapDerivedCategoryNatIso
    ((conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction k (R.ring W) (R.ring V) (R.pull k)).comp
        (proEtaleRingModuleAdjunction h (R.ring V) (R.ring U) (R.pull h)))
      (proEtaleRingModuleAdjunction (h ≫ k) (R.ring W) (R.ring U) (R.pull (h ≫ k)))).symm
      (modulePushComposition_existsUnique R h k hc).exists.choose) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The fixed geometric pullback, with its original small-site universes.
Source: Stacks Tag 03D8
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev pull (R : Coefficients.{u}) {U V : Scheme.{u}} (g : U ⟶ V) :=
  proEtaleRingDerivedPullback g (R.ring V) (R.ring U) (R.pull g)

/-- Separately derived geometric direct image.
Source: Stacks Tag 07A5
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev push (R : Coefficients.{u}) {U V : Scheme.{u}} (g : U ⟶ V) :=
  proEtaleRingDerivedDirectImage g (R.ring V) (R.ring U) (R.pull g)

/-- The exact derived open adjunction, with its inherited unit normalization.
Source: Stacks Tag 03DI
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openDerivedAdjunction (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] : (openExtension R j).mapDerivedCategory ⊣ pull R j :=
  let J := openExtension R j
  let P := proEtaleRingModulePullback j (R.ring V) (R.ring U) (R.pull j)
  letI : CatCommSq (J.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q J.mapDerivedCategory := ⟨J.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (P.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q P.mapDerivedCategory := ⟨P.mapDerivedCategoryFactors.symm⟩
  ((openAdjunction R j).mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    J.mapDerivedCategory P.mapDerivedCategory

/-- The open projection inverse is the adjoint of the open unit tensored with identity,
followed by inverse tensor pullback. Its inverse is the canonical open projection map.
Source: Stacks Tags 03DI, 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openProjectionInverse (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (N : DerivedCategory (pbcModules V (R.ring V))) :
    (openExtension R j).mapDerivedCategory.obj (a.tensor.obj (M, (pull R j).obj N)) ⟶
      b.tensor.obj ((openExtension R j).mapDerivedCategory.obj M, N) :=
  ((openDerivedAdjunction R j).homEquiv _ _).symm
    (a.tensor.map (Prod.mkHom ((openDerivedAdjunction R j).unit.app M) (𝟙 _)) ≫
      (proEtaleCanonicalTensorComparison j (R.ring V) (R.ring U) (R.pull j) b a).inv.app
        ((openExtension R j).mapDerivedCategory.obj M, N))

/-- The open projection inverse is invertible.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: on flat K-flat representatives the map is the sheafified identity
j_!(M tensor j^*N) to j_!M tensor N on the open slice; both sides are zero off
that slice. The unit normalization fixes the map on the open. Thus it is an
isomorphism of representatives, and localization preserves its inverse. -/
theorem openProjectionInverse_isIso (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (N : DerivedCategory (pbcModules V (R.ring V))) :
    IsIso (openProjectionInverse R j a b M N) := by
  sorry

/-- The specified open projection isomorphism.
Source: Stacks Tag 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def openProjectionIso (R : Coefficients.{u}) {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j]
    (a : ProEtaleTensorModel U (R.ring U)) (b : ProEtaleTensorModel V (R.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (N : DerivedCategory (pbcModules V (R.ring V))) :=
  (@asIso _ _ _ _ (openProjectionInverse R j a b M N)
    (openProjectionInverse_isIso R j a b M N)).symm

/-- Curried presentation of the already supplied actual derived tensor model.
Source: Stacks Tag 07A4
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
abbrev tensorCurried {W : Scheme.{u}}
    {R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : ProEtaleTensorModel W R) :=
  Functor.curry.obj a.tensor

/-- The open projection followed by the specified f=pj pullback identification.
Source: blueprint def-exchange-projection, gamma
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def projectionOpenFactor (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (M : DerivedCategory (pbcModules X (R.ring X)))
    (N : DerivedCategory (pbcModules Y (R.ring Y))) :=
  openProjectionIso R c.i a b M ((pull R c.g).obj N) ≪≫
    (openExtension R c.i).mapDerivedCategory.mapIso
      (a.tensor.mapIso (Iso.prod (Iso.refl M)
        (((geometricPullComposition R c.i c.g hc).symm ≪≫
          eqToIso (congrArg (fun g : X ⟶ Y ↦ pull R g) c.comm.symm)).app N)))

/-- The supplied-domain comparison types of def-exchange-projection, fixed componentwise
by the canonical tensor-pullback and open projection constructions above.
Source: blueprint def-exchange-projection, supplied-domain paragraph
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
structure ProjectionComparisons (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (d : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) where
  tensorPullback :
    (Functor.postcompose₂.obj (pull R c.g)).obj (tensorCurried d) ≅
      (((Functor.whiskeringLeft₂ _).obj (pull R c.g)).obj (pull R c.g)).obj (tensorCurried b)
  openProjection :
    (((Functor.whiskeringLeft₂ _).obj (openExtension R c.i).mapDerivedCategory).obj
        (pull R c.g)).obj (tensorCurried b) ≅
      (Functor.postcompose₂.obj (openExtension R c.i).mapDerivedCategory).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (pull R f)).obj (tensorCurried a))
  tensorPullback_eq : ∀ M N,
    (tensorPullback.hom.app M).app N =
      (proEtaleCanonicalTensorComparison c.g (R.ring Y) (R.ring c.Z) (R.pull c.g) d b).hom.app
        (M, N)
  openProjection_eq : ∀ M N,
    (openProjection.hom.app M).app N = (projectionOpenFactor R c a b hc M N).hom

/-- These comparison data exist uniquely, since their components were independently fixed.
Source: Stacks Tags 07A4, 0E8I
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: curry the canonical natural tensor-pullback comparison. Naturality of the open
unit and tensor comparison makes openProjectionInverse natural; its inverse and
pullback composition remain natural. Curry their composite to obtain gamma.
The two displayed component identities hold by construction. Natural transformations
are determined by components, and currying is faithful, so the data are unique. -/
theorem projectionComparisons_existsUnique (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (d : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) :
    ∃! data : ProjectionComparisons R c a b d hc, True := by
  sorry

/-- The actual compact-support projection from def-exchange-projection, using its
existing supplied-domain construction and the uniquely normalized comparison data.
Source: blueprint def-exchange-projection, projection formula
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def projectionMap (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (d : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i)) :=
  let data := (projectionComparisons_existsUnique R c a b d hc).exists.choose
  SuppliedExchangeProjection.compactificationProjectionFromData
    (openExtension R c.i).mapDerivedCategory (pull R f)
    (pull R c.g) (push R c.g)
    (proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z) (R.pull c.g))
    (tensorCurried a) (tensorCurried b) (tensorCurried d) data.tensorPullback data.openProjection

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The inverse-image coefficient map adjoint to the canonical completed direct-image map.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def completedPullMap {U V : Scheme.{u}} (g : U ⟶ V) :=
  ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).homEquiv _ _).symm
    (sfCompletedCoefficientMap l E g)

/-- Canonical inverse image of the completed coefficient sheaf is invertible.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: the profinite-coefficient inverse-image theorem identifies the pullback of the
finite quotient system with the source quotient system, compatibly with projections.
The inverse limit and its constant-section maps identify its completed comparison
with the adjoint of sfCompletedCoefficientMap, since every projection agrees. -/
theorem completedPullMap_isIso {U V : Scheme.{u}} (g : U ⟶ V) :
    IsIso (completedPullMap l E g) := by
  sorry

attribute [instance] completedPullMap_isIso

/-- The specified completed coefficient system, with no identification with a discrete
constant integral sheaf. Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def completed : Coefficients.{u} where
  ring := completedIntegralCommRingSheafUnrestricted l E
  pull g := asIso (completedPullMap l E g)

/-- Completed coefficient inverse-image identifications respect composition.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: take adjoints and compose with all finite projections. Both sides become the
same constant quotient pullback-composition map. Its constant-section normalization
identifies them, and the completed projections are jointly monic. -/
theorem completedPull_comp {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    (completed l E).pull (h ≫ k) = proEtaleRingCompositeCoefficients h k
      ((completed l E).ring W) ((completed l E).ring V) ((completed l E).ring U)
        ((completed l E).pull k) ((completed l E).pull h) := by
  sorry

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Compatibility of the actual completed coefficient inclusion with inverse image.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: def-pur-integral-compact-support-coefficient-data).
Proof: take adjoints and compose with each target finite projection. The completed
structure maps become their constant quotient maps and both routes are induced by
the same inclusion of integer rings. The inverse-limit projections are jointly monic. -/
theorem completedChange_square {U V : Scheme.{u}} (g : U ⟶ V) :
    ((completed l E).pull g).hom ≫ completedCoefficientMap l E F i U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (completedCoefficientMap l E F i V) ≫ ((completed l F).pull g).hom := by
  sorry

/-- The finite quotient coefficient system at the positive exponent n.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def finite (n : ℕ) (hn : 1 ≤ n) : Coefficients.{u} where
  ring W := proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)
  pull g := @sfConstantCoefficientIso _ _ g (Padic.coefficientExtensionRing l E n) _
    (Padic.finite_coefficientExtensionRing l E n hn)

/-- The completed coefficient projection at an arbitrary positive exponent.
Source: Bhatt--Scholze, Definition 6.7.6
(blueprint: def-pur-integral-compact-support-coefficient-data). -/
def projection (n : ℕ) (hn : 1 ≤ n) (W : Scheme.{u}) :
    (completed l E).ring W ⟶ (finite l E n hn).ring W :=
  completedIntegralCommRingProjectionUnrestricted l E W (n - 1) ≫
    eqToHom (congrArg (fun k ↦ proEtaleConstantRing W
      (Padic.coefficientExtensionRing l E k)) (Nat.sub_add_cancel hn))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))] [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

end WeilConjectures.PurCompactSupport
