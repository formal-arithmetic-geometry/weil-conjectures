/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
import Sheaf.Paper.RingedSliceDerivedAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.Paper.RingedSliceDerivedComparisons
import Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Étale chart calculus for unbounded derived algebraic-space modules

Source: Stacks Project, spaces-perfect.tex, Tags 08F2 and 08F4;
sites-cohomology.tex, Tags 0D6G, 0D6D, 0D6E and 07A6
(blueprint: lem-sfb-space-derived-etale-chart-calculus).

All functors are the existing compatible-chart functors on the equivalent small ringed
models. Comparisons retain their ordinary tensor and derived-adjunction normalizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w i

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z T : AlgebraicSpace S}

/-- Étale tensor pullback is exact, without a surjectivity assumption.
Its identification with actual restriction, including the scalar-one unit, is the
recorded `moduleTensorPullback_etale_restriction` comparison, transported through the
small-model equivalences.
Source: Stacks, spaces-perfect.tex, discussion preceding Tag 08F2; spaces-properties.tex,
Tags 03LV and 03LW (blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: identify ordinary tensor pullback with restriction by the multiplication formula
of lem-trf-space-etale-module-pushforward-restriction. On the localized ringed site,
restriction preserves kernels and sheafified cokernels (lem-sfb-ringed-site-restriction-kflat).
Transport these finite limits and colimits through the two module equivalences. This also
works for the empty chart. -/
theorem spaceEtaleTensorPullback_exact (f : X ⟶ Y) (hf : IsEtale f.hom.hom) :
    PreservesFiniteLimits (smallModuleTensorPullback f) ∧
      PreservesFiniteColimits (smallModuleTensorPullback f) := by
  sorry

/-- Exact étale restriction on the unbounded derived categories, applied termwise.
Source: Stacks, spaces-perfect.tex, discussion preceding Tag 08F2;
Tag 015F (blueprint: lem-sfb-space-derived-etale-chart-calculus). -/
def spaceEtaleDerivedRestriction (f : X ⟶ Y) (hf : IsEtale f.hom.hom)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    Y.DerivedModules ⥤ X.DerivedModules :=
  letI := (spaceEtaleTensorPullback_exact f hf).1
  letI := (spaceEtaleTensorPullback_exact f hf).2
  (smallModuleTensorPullback f).mapDerivedCategory

/-- The specified termwise comparison for exact étale restriction.
Source: Stacks, Tag 015F (blueprint: lem-sfb-space-derived-etale-chart-calculus). -/
def spaceEtaleDerivedRestrictionFactors (f : X ⟶ Y) (hf : IsEtale f.hom.hom)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    DerivedCategory.Q ⋙ spaceEtaleDerivedRestriction f hf ≅ smallTensorPullbackComplex f :=
  letI := (spaceEtaleTensorPullback_exact f hf).1
  letI := (spaceEtaleTensorPullback_exact f hf).2
  (smallModuleTensorPullback f).mapDerivedCategoryFactors

/-- Total derived pullback is exact restriction along an étale map. The equality with
its existing derived counit uniquely fixes the comparison on every representative.
Source: Stacks, discussion preceding Tag 08F2; Tag 015F
(blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: exact restriction inverts quasi-isomorphisms. The exact-functor derivation theorem
lem-weil-pbc-exact-functor-derived-functor makes its termwise factorization a total left
derived functor. Uniqueness of that universal property supplies the unique isomorphism
with the displayed counit equation. -/
theorem spaceEtaleDerivedRestriction_existsUnique (f : X ⟶ Y)
    (hf : IsEtale f.hom.hom)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    ∃! e : spaceDerivedPullback f ≅ spaceEtaleDerivedRestriction f hf,
      ∀ P : CochainComplex Y.SmallModules ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (spaceEtaleDerivedRestrictionFactors f hf).hom.app P =
            (spaceDerivedPullbackCounit f).app P := by
  sorry

/-- The recorded derived functors are computed on flat-term K-flat and K-injective
representatives, and their adjunction has the specified ordinary-unit normalization.
Source: Stacks, Tags 06YS, 06YY, 079V and 07A6
(blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: use the enlarged ringed-site model and the chart-adjunction tensor realization
(lem-trf-space-enlarged-etale-ringed-site-model and
lem-trf-space-chart-adjunction-tensor-realization). The ringed derived-image existence
statement gives the adjunction. K-flat resolutions compute its left counit and
K-injective resolutions compute its right unit; the small-model equivalences preserve
these resolving classes. The normalization is the ordinary tensor unit followed by
the right-derived unit, as in def-sfb-space-affine-hom-comparison. -/
theorem spaceDerivedChart_resolution_computation (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    (∀ P : CochainComplex Y.SmallModules ℤ,
      CochainComplex.IsKFlatIndependentCoefficients
        (J := Y.smallEtaleModelTopology) (R := Y.smallStructureSheaf) P →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite
        (J := Y.smallEtaleModelTopology) (R := Y.smallStructureSheaf) (P.X n)) →
      IsIso ((spaceDerivedPullbackCounit f).app P)) ∧
    (∀ (I : CochainComplex X.SmallModules ℤ) [I.IsKInjective],
      IsIso (spaceRightDerivedComplexUnit (smallModuleDirectImage f) I)) ∧
    SpaceDerivedAdjunctionNormalized f (spaceDerivedAdjunction f) := by
  sorry

/-- Canonical pullback comparison for two equal composite paths. In particular this is
`b* Lu* ≅ Lu_V* a*` for an étale cartesian square. It is defined even without flatness
or cartesianness by the previously fixed tensor-normalized composition comparisons.
Source: Stacks, Tag 0D6D (blueprint: lem-sfb-space-derived-etale-chart-calculus). -/
def spaceDerivedChartPullbackSquare (f : X ⟶ Y) (g : Z ⟶ Y)
    (h : T ⟶ X) (f' : T ⟶ Z) (sq : h ≫ f = f' ≫ g)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} Z.SmallModules] [HasDerivedCategory.{w} T.SmallModules] :
    spaceDerivedPullback f ⋙ spaceDerivedPullback h ≅
      spaceDerivedPullback g ⋙ spaceDerivedPullback f' :=
  (spaceDerivedPullbackComp f h).symm ≪≫
    eqToIso (congrArg spaceDerivedPullback sq) ≪≫ spaceDerivedPullbackComp g f'

/-- Étale base change for every unbounded module complex. The unique natural
isomorphism is the mate of the canonical pullback square, followed by the f-counit.
Thus the comparison includes its normalization and all module naturality.
Source: Stacks, Tag 0D6G (blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: base change makes h étale. Represent K by a K-injective I, using
prop-pur-kinjective-resolutions-exist. Restriction of I is K-injective by
lem-pur-kinjective-restrict-localized. The ordinary chart comparison of
lem-trf-space-etale-module-pushforward-restriction identifies both complexes termwise:
on a test scheme over Z both have the same compatible sections over its fibre product
with X. The normalized slice-comparison theorem
lem-weil-pbc-ringed-slice-derived-comparisons identifies this comparison with the mate
of the pullback-square comparison and the f-counit. Localization gives naturality;
the mate equation specifies every component, hence uniqueness. No quasi-coherence,
boundedness, quasi-compactness or separation is used. -/
theorem spaceDerivedChart_etale_baseChange
    (f : X ⟶ Y) (g : Z ⟶ Y) (h : T ⟶ X) (f' : T ⟶ Z)
    (hg : IsEtale g.hom.hom) (hp : IsPullback h f' f g)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} Z.SmallModules] [HasDerivedCategory.{w} T.SmallModules] :
    IsEtale h.hom.hom ∧
      ∃! e : derivedDirectImage f ⋙ spaceDerivedPullback g ≅
          spaceDerivedPullback h ⋙ derivedDirectImage f',
        ∀ K : X.DerivedModules,
          e.hom.app K = (spaceDerivedAdjunction f').homEquiv _ _
            ((spaceDerivedChartPullbackSquare f g h f' hp.w).inv.app
                ((derivedDirectImage f).obj K) ≫
              (spaceDerivedPullback h).map ((spaceDerivedAdjunction f).counit.app K)) := by
  sorry

/-- Quasi-coherent cohomology is local for any jointly surjective étale scheme family.
Source: Stacks, Tag 08F2 and spaces-properties.tex, Tag 03M0
(blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: exact étale restriction commutes with each cohomology sheaf. Quasi-coherence is
local presentations by sums of structure modules. Such presentations restrict, since
restriction is exact and preserves those sums. Conversely refine the given scheme
cover by presentation covers, and base-change these covers to each test scheme.
The resulting covers and presentations show quasi-coherence on X. Apply this to every
integer degree. Empty families are permitted: joint surjectivity then forces X empty. -/
theorem spaceDerivedChart_quasiCoherent_iff_cover
    (X : AlgebraicSpace S) [HasDerivedCategory.{w} X.SmallModules]
    (U : Type i) (V : U → Over S) (a : ∀ j : U, schemeSpace (V j) ⟶ X)
    (ha : ∀ j : U, IsEtale (a j).hom.hom)
    (hc : IsJointlySurjective (fun j : U ↦ (a j).hom.hom))
    [∀ j : U, HasDerivedCategory.{w} (schemeSpace (V j)).SmallModules]
    (K : X.DerivedModules) :
    X.derivedQCohProperty K ↔ ∀ j : U,
      (schemeSpace (V j)).derivedQCohProperty ((spaceDerivedPullback (a j)).obj K) := by
  sorry

/-- Arbitrary unbounded derived pullback preserves quasi-coherent cohomology.
Source: Stacks, Tag 08F4 (blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof:
1. Choose a surjective étale scheme chart V of Y and a further surjective étale scheme
chart U of X times_Y V, using the algebraic-space atlas and fibre-product cover lemmas.
Their composite c:U to X is surjective étale and f c = a h for a scheme map h:U to V.
2. The common K-flat word comparison identifies c* Lf* K with Lh* a* K, using exactness
of the two étale restrictions. The cover criterion gives quasi-coherent cohomology for a* K.
3. On a scheme the Zariski-to-étale pullback epsilon* is exact: its geometric stalks
are tensor with a strictly henselian local ring, faithfully flat over the Zariski stalk.
Use lem-sfb-etale-zariski-module-geometric-stalk, module-stalk exactness, strict
henselization faithful flatness, exact forgetting and geometric-stalk conservativity.
4. For E with quasi-coherent cohomology, affine étale objects form an acyclic basis.
The ordinary QCoh equivalence, étale affine acyclicity, module-derived evaluation/slice
comparison and lem-sfb-ringed-site-acyclic-basis-cohomology give canonical edge maps
Hq(RGamma(U,E)) = Hq(E)(U) in every degree, without boundedness. K-injective resolutions
and bounded-below injective resolutions of the cohomology sheaves justify this computation.
5. Represent E by a K-injective I. Sheafify the presheaves Hq(I(W)) on affine Zariski
opens. Exact module sheafification identifies the cohomology of R epsilon_* E with
epsilon_* Hq(E). The counit acts by the ordinary tensor counit on these edge maps,
hence is invertible by the ordinary QCoh equivalence. Thus E = epsilon* M with M in
Zariski D_QCoh. This proves the scheme derived comparison used here.
6. The ordinary Zariski/étale comparison square, descended on one common flat-term
K-flat resolution by lem-trf-ringed-kflat-word-comparison-descent, identifies
Lh_et* epsilon* M with epsilon* Lh_Zar* M. The scheme derived pullback theorem preserves
QCoh and exact epsilon* preserves its cohomology, proving the scheme case.
7. Apply that case on U, then the étale cover criterion on X. This follows the source
without assuming the fibre product X times_Y V itself is a scheme. -/
theorem space_derived_etale_chart_calculus (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (K : Y.DerivedModules) (hK : Y.derivedQCohProperty K) :
    X.derivedQCohProperty ((spaceDerivedPullback f).obj K) := by
  sorry

/-- Right-adjoint conjugate of the specified derived pullback composition comparison.
Source: Stacks, Tags 0D6D, 0D6E and 07A6
(blueprint: lem-sfb-space-derived-etale-chart-calculus). -/
def spaceDerivedChartDirectImageComp (f : X ⟶ Y) (g : Z ⟶ X)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} Z.SmallModules] :
    derivedDirectImage g ⋙ derivedDirectImage f ≅ derivedDirectImage (g ≫ f) :=
  conjugateIsoEquiv ((spaceDerivedAdjunction f).comp (spaceDerivedAdjunction g))
    (spaceDerivedAdjunction (g ≫ f)) (spaceDerivedPullbackComp f g)

/-- Right-adjoint conjugate of the canonical derived pullback identity comparison.
Source: Stacks, Tags 0D6D and 0D6E
(blueprint: lem-sfb-space-derived-etale-chart-calculus). -/
def spaceDerivedChartDirectImageId (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    derivedDirectImage (𝟙 X) ≅ 𝟭 X.DerivedModules :=
  conjugateIsoEquiv (spaceDerivedAdjunction (𝟙 X)) Adjunction.id
    (spaceDerivedPullbackId X).symm

/-- The tensor-normalized derived pullback compositors satisfy associativity.
Source: Stacks, Tag 0D6D (blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: choose one flat-term K-flat resolution. All successive pullbacks remain flat-term
K-flat. On this resolution both sides multiply the same three scalar coefficients and
retain the same section; ordinary tensor associativity makes them equal. The normalized
common-word descent of lem-trf-ringed-kflat-word-comparison-descent descends that equality. -/
theorem spaceDerivedChart_pullback_associativity (f : X ⟶ Y) (g : Z ⟶ X) (h : T ⟶ Z)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} Z.SmallModules] [HasDerivedCategory.{w} T.SmallModules] :
    (spaceDerivedPullbackComp f (h ≫ g)).hom ≫
        whiskerLeft (spaceDerivedPullback f) (spaceDerivedPullbackComp g h).hom =
      (eqToIso (congrArg spaceDerivedPullback (Category.assoc h g f))).hom ≫
        (spaceDerivedPullbackComp (g ≫ f) h).hom ≫
        whiskerRight (spaceDerivedPullbackComp f g).hom (spaceDerivedPullback h) ≫
        (Functor.associator _ _ _).hom := by
  sorry

/-- Both unit laws for the tensor-normalized derived pullback comparisons.
Source: Stacks, Tag 0D6D (blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: on a common flat-term K-flat representative the identity comparison multiplies
by the unit coefficient. The two compositions therefore equal the ordinary left and
right tensor unit maps. The same normalized descent gives both derived equalities. -/
theorem spaceDerivedChart_pullback_units (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules] :
    ((spaceDerivedPullbackComp f (𝟙 X)).hom ≫
        whiskerLeft (spaceDerivedPullback f) (spaceDerivedPullbackId X).hom ≫
        (Functor.rightUnitor _).hom =
      (eqToIso (congrArg spaceDerivedPullback (Category.id_comp f))).hom) ∧
    ((spaceDerivedPullbackComp (𝟙 Y) f).hom ≫
        whiskerRight (spaceDerivedPullbackId Y).hom (spaceDerivedPullback f) ≫
        (Functor.leftUnitor _).hom =
      (eqToIso (congrArg spaceDerivedPullback (Category.comp_id f))).hom) := by
  sorry

/-- Direct-image composition respects both the units and counits of the specified
composite and single-map adjunctions.
Source: Stacks, Tags 0D6E and 0B65
(blueprint: lem-sfb-space-derived-etale-chart-calculus).
Proof: the direct-image compositor is by definition the right-adjoint conjugate of the
pullback compositor. Apply the unit equation of
lem-weil-pbc-conjugate-iso-unit-equation to these adjunctions; transposing it gives the
counit equation. Conjugation preserves identities and reverses composition, so the
associativity and unit laws above also give the coherent direct-image comparisons. -/
theorem spaceDerivedChart_composition_unit_counit (f : X ⟶ Y) (g : Z ⟶ X)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} Z.SmallModules] :
    (∀ A : Y.DerivedModules,
      ((spaceDerivedAdjunction f).comp (spaceDerivedAdjunction g)).unit.app A ≫
          (spaceDerivedChartDirectImageComp f g).hom.app
            ((spaceDerivedPullback f ⋙ spaceDerivedPullback g).obj A) =
        (spaceDerivedAdjunction (g ≫ f)).unit.app A ≫
          (derivedDirectImage (g ≫ f)).map ((spaceDerivedPullbackComp f g).hom.app A)) ∧
    (∀ B : Z.DerivedModules,
      (spaceDerivedPullback (g ≫ f)).map
          ((spaceDerivedChartDirectImageComp f g).hom.app B) ≫
          (spaceDerivedAdjunction (g ≫ f)).counit.app B =
        (spaceDerivedPullbackComp f g).hom.app
            ((derivedDirectImage g ⋙ derivedDirectImage f).obj B) ≫
          ((spaceDerivedAdjunction f).comp (spaceDerivedAdjunction g)).counit.app B) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
