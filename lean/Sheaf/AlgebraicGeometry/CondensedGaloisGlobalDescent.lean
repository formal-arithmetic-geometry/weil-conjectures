module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
import Sheaf.CategoryTheory.RingedPresentationTransport
import Sheaf.CategoryTheory.InternalActionSitePresentation
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.CategoryTheory.CondensedProductActionInflation
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.RingedDerivedCompositionCocycle
import Sheaf.Paper.DerivedAdjunctionShift

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Mathlib.FieldTheory.Galois.Profinite
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Ordinary condensed Galois descent for global derived sections

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3);
Bhatt--Scholze, Examples 4.1.9--4.1.10; Stacks Tags 08BJ and 0D6E
(blueprint: lem-sfb-condensed-galois-global-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedGalois

/-- The ordinary internal coefficient module category.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
abbrev Modules (R : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (coefficientRing X R).X

/-- The inverse/direct image adjunction from the condensed point.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def pointAdjunction (X : Scheme.{u}) :
    upperStarFromPoint X ⊣ sfbPullbackFromPointRightAdjoint X :=
  pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The point inverse/direct image adjunction has a multiplicative unit.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: both component adjunctions are monoidal. Their composite unit is the first
unit followed by the image of the second unit, so it preserves multiplication and unit. -/
theorem pointUnit_isMonHom (R : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :
    IsMonHom ((pointAdjunction X).unit.app R.X) := by
  sorry

attribute [instance] pointUnit_isMonHom

/-- Module direct image to the condensed point, with its actual unit scalar action.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def pointModules (R : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :
    Modules R X ⥤ Profinite.CondensedAction.Modules R :=
  (sfbPullbackFromPointRightAdjoint X).mapMod (coefficientRing X R).X ⋙
    Mod.comap ((pointAdjunction X).unit.app R.X)

/-- Global sections of the underlying abelian sheaf at the terminal pro-etale object.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def globalSections (R : Profinite.CondensedRing.{u}) (X : Scheme.{u}) :
    Modules R X ⥤ Ab.{u + 1} :=
  Mod.forget (coefficientRing X R).X ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))

/-- Evaluation at the singleton, forgetting only the scalar structure.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def pointEvaluation (R : Profinite.CondensedRing.{u}) :
    Profinite.CondensedAction.Modules R ⥤ Ab.{u + 1} :=
  Mod.forget R.X ⋙ sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
    (evaluation _ _).obj (op (Profinite.of PUnit.{u + 1}))

section CoefficientSquare
variable {C C' D D' : Type (u + 2)}
  [Category.{u + 1} C] [Category.{u + 1} C']
  [Category.{u + 1} D] [Category.{u + 1} D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
  [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} C']
  [HasDerivedCategory.{u + 2} D] [HasDerivedCategory.{u + 2} D']
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
  (L : C' ⥤ C) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (Q : D' ⥤ D) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  (F : C ⥤ D) [F.Additive] (F' : C' ⥤ D') [F'.Additive]

/-- A coefficient comparison with its defining total-derived unit equation. The left
restriction need not preserve K-injectives. The equation is the normalization for
composition of ringed direct images, including identity underlying topoi.
Source: Stacks Tag 0D6E (blueprint: lem-sfb-condensed-galois-global-descent). -/
structure CoefficientComparison where
  /-- The actual underived coefficient comparison. -/
  ordinary : L ⋙ F ≅ F' ⋙ Q
  /-- Its comparison on ordinary unbounded derived categories. -/
  derived : L.mapDerivedCategory ⋙ F.rightDerivedFunctor ≅
    F'.rightDerivedFunctor ⋙ Q.mapDerivedCategory
  /-- The unit equation specifies the canonical derived comparison. -/
  unit : ∀ J : HomotopyCategory C' (ComplexShape.up ℤ),
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit L F).app J ≫
      derived.hom.app (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ordinary.hom
      (ComplexShape.up ℤ)).app J) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F' Q).app J

end CoefficientSquare

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks] [IsSepClosure k ks]
  (X : Scheme.{u}) (a : X ⟶ Spec (.of k))

/-- Base change along the specified separable closure, with its canonical projections.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
abbrev geometricScheme : Scheme.{u} :=
  pullback a (Spec.map (CommRingCat.ofHom (algebraMap k ks)))

/-- Projection from the geometric scheme to X.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
abbrev geometricProjection : geometricScheme k ks X a ⟶ X :=
  pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k ks)))

/-- The ordinary geometric section functor after forgetting its Galois action.
Its value at P is sections of the original module on X^s[P], with the unit coefficient map.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def geometricSections (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] :
    Modules R X ⥤ Profinite.CondensedAction.Modules R :=
  CondensedRing.upperStar R.X (geometricProjection k ks X a) ⋙
    pointModules R (geometricScheme k ks X a)

/-- The coefficient extension to the separable closure is weakly etale.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-condensed-galois-global-descent).
Proof: write ks as its filtered union of finite separable extensions. Their spectra
are finite etale, hence their affine inverse limit is pro-etale and weakly etale. -/
theorem geometricProjection_weaklyEtale : WeaklyEtale (geometricProjection k ks X a) := by
  sorry

attribute [instance] geometricProjection_weaklyEtale

/-- The actual profinite geometric test object, viewed in X_proet.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def test (P : Profinite.{u}) : X.ProEt :=
  Scheme.ProEt.mk (((profiniteToProEtOf (geometricScheme k ks X a)).obj P).hom ≫
    geometricProjection k ks X a)

/-- The map of geometric tests induced by a continuous parameter map.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def testMap {P Q : Profinite.{u}} (f : P ⟶ Q) : test k ks X a P ⟶ test k ks X a Q :=
  { left := ((profiniteToProEtOf (geometricScheme k ks X a)).map f).left
    right := 𝟙 _
    w := by simp [test, ← Category.assoc]
    prop_hom_left := trivial
    prop_hom_right := trivial }

/-- Singleton tests are canonically the geometric scheme itself.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: the profinite test functor preserves finite limits, in particular the terminal
object. Its structure map to X^s is therefore the unique isomorphism of terminal objects. -/
theorem singleton_isIso :
    IsIso (((profiniteToProEtOf (geometricScheme k ks X a)).obj
      (Profinite.of PUnit.{u + 1})).hom) := by
  sorry

attribute [instance] singleton_isIso

/-- Inclusion of the geometric fibre over a point of P into X^s[P].
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def fibreMap (P : Profinite.{u}) (p : P) :
    geometricScheme k ks X a ⟶ (test k ks X a P).left :=
  inv (((profiniteToProEtOf (geometricScheme k ks X a)).obj
    (Profinite.of PUnit.{u + 1})).hom) ≫
      ((profiniteToProEtOf (geometricScheme k ks X a)).map
        (CompHausLike.ofHom _ (ContinuousMap.const _ p))).left

/-- The Galois automorphism preserves the structural field map.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: on coordinate rings the equality is sigma(algebraMap x)=algebraMap x,
which is the defining algebra-compatibility axiom of a k-algebra automorphism. -/
theorem automorphism_condition (σ : ks ≃ₐ[k] ks) :
    pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ≫ a =
      (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k ks)) := by
  sorry

/-- The automorphism of X^s induced contravariantly by sigma on ks.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def geometricAut (σ : ks ≃ₐ[k] ks) :
    geometricScheme k ks X a ⟶ geometricScheme k ks X a :=
  pullback.lift
    (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap k ks))))
    (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap k ks))) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom))
    (automorphism_condition k ks X a σ)

/-- A continuously varying Galois element defines a unique morphism of geometric tests.
The fibre formula specifies the actual morphism, including the empty test.
Source: Bhatt--Scholze Examples 4.1.9--4.1.10
(blueprint: lem-sfb-condensed-galois-global-descent).
Proof: for every affine open U of X, its geometric P-test has coordinate ring
LC(P,O(U) tensor_k ks).
A continuous g acts on the ks scalars by p maps to g(p)(c); these functions are
locally constant because the stabilizer of c is open for the Krull topology.
This produces the compatible morphisms on the affine charts. Their uniqueness follows
by evaluation in every fibre, since locally constant functions are determined pointwise.
They glue to the unique displayed X-map. Empty charts give the unique empty map. -/
theorem twist_existsUnique (P : Profinite.{u}) (g : C(P, ks ≃ₐ[k] ks)) :
    ∃! t : test k ks X a P ⟶ test k ks X a P,
      ∀ p : P, fibreMap k ks X a P p ≫ t.left =
        geometricAut k ks X a (g p) ≫ fibreMap k ks X a P p := by
  sorry

/-- The canonical variable Galois action on the geometric test scheme, chosen only
from a uniqueness statement, rather than from unspecified existence data.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def twist (P : Profinite.{u}) (g : C(P, ks ≃ₐ[k] ks)) :
    test k ks X a P ⟶ test k ks X a P :=
  Classical.choose (ExistsUnique.exists (twist_existsUnique k ks X a P g))

/-- The test maps preserve identities and composition.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: forget the arrows to scheme maps. Both equations are the corresponding
functor equations for profiniteToProEtOf; the over-category fields are propositions. -/
theorem testMap_laws :
    (∀ P : Profinite.{u}, testMap k ks X a (𝟙 P) = 𝟙 (test k ks X a P)) ∧
    (∀ (P Q S : Profinite.{u}) (f : P ⟶ Q) (g : Q ⟶ S),
      testMap k ks X a (f ≫ g) = testMap k ks X a f ≫ testMap k ks X a g) := by
  sorry

/-- The actual geometric-test functor, including its continuous parameter maps.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def tests : Profinite.{u} ⥤ X.ProEt where
  obj := test k ks X a
  map := testMap k ks X a
  map_id := (testMap_laws k ks X a).1
  map_comp := (testMap_laws k ks X a).2 _ _ _

/-- Forget the scalar structure of an internal condensed module as a presheaf.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def condensedPresheaf (R : Profinite.CondensedRing.{u}) :
    Profinite.CondensedAction.Modules R ⥤ (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  Mod.forget R.X ⋙ sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}

/-- The geometric section presheaf, restricted from the original sheaf on X.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def geometricPresheaf (R : Profinite.CondensedRing.{u}) :
    Modules R X ⥤ (Profinite.{u}ᵒᵖ ⥤ Ab.{u + 1}) :=
  Mod.forget (coefficientRing X R).X ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (Functor.whiskeringLeft _ _ _).obj (tests k ks X a).op

/-- The graph into the pullback used by the geometric pullback/direct-image unit.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def testGraph (P : Profinite.{u}) :
    (profiniteToProEtOf (geometricScheme k ks X a)).obj P ⟶
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤
        (geometricProjection k ks X a)).obj (test k ks X a P) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 _) ((profiniteToProEtOf (geometricScheme k ks X a)).obj P).hom
      (by simp [test])) (by simp)

/-- The canonical restriction to geometric sections, obtained from the module pullback
unit and restriction to its graph. It retains the given ring action and all section maps.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def geometricRestriction (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
    (M : Modules R X) (P : Profinite.{u}) :
    ((geometricPresheaf k ks X a R).obj M).obj (op P) ⟶
      ((condensedPresheaf R).obj ((geometricSections k ks X a R).obj M)).obj (op P) :=
  (((CondensedRing.upperStarLowerStarAdjunction R.X
    (geometricProjection k ks X a)).unit.app M).hom.hom.app (op (test k ks X a P))) ≫
      ((CondensedRing.upperStar R.X (geometricProjection k ks X a)).obj M).X.obj.map
        (testGraph k ks X a P).op

/-- The geometric section functor with its actual condensed action. Its underlying
module is the existing geometricSections functor, and its presheaf comparison is
natural in both the module and the test. The action is pullback by the variable
Galois automorphism, so it is fixed by the geometry, not an extra representation.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
structure GeometricData (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] where
  /-- The equivariant geometric section functor. -/
  functor : Modules R X ⥤ Profinite.CondensedAction.ActionModule R (ks ≃ₐ[k] ks)
  /-- Addition is the addition of the original section maps. -/
  additive : functor.Additive
  /-- The exact underlying internal module, with its pulled-back scalar action. -/
  underlying : functor ⋙ Profinite.CondensedAction.forgetAction ≅
    geometricSections k ks X a R
  /-- The geometric formula on every test object and every map. -/
  sections : functor ⋙ Profinite.CondensedAction.forgetAction ⋙ condensedPresheaf R ≅
    geometricPresheaf k ks X a R
  /-- The section formula agrees with the canonical module pullback restriction.
  This ties the presheaf identification to the specified underlying R-module. -/
  normalization : ∀ (M : Modules R X) (P : Profinite.{u}),
    (sections.hom.app M).app (op P) ≫ geometricRestriction k ks X a R M P =
      (underlying.hom.app M).hom.hom.app (op P)
  /-- Every generalized Galois element acts by restriction along the specified twist. -/
  action : ∀ (M : Modules R X) (P : Profinite.{u}) (g : C(P, ks ≃ₐ[k] ks))
    (m : Profinite.CondensedAction.sectionModule R (functor.obj M).module P),
    ((sections.hom.app M).app (op P)).hom ((functor.obj M).act P g m) =
      (M.X.obj.map (twist k ks X a P g).op).hom
        (((sections.hom.app M).app (op P)).hom m)

/-- All arbitrary condensed coefficients can be bundled with their commutativity proof.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
abbrev Coefficients := CategoryTheory.CondensedBar.Ring.{u}

/-- The standard localization universe for internal pro-etale modules.
Source: blueprint size convention (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance moduleDerived (R : Coefficients.{u}) (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (Modules R.toMon Y) := HasDerivedCategory.standard _

/-- The standard localization universe for internal condensed modules.
Source: blueprint size convention (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance condensedDerived (R : Coefficients.{u}) :
    HasDerivedCategory.{u + 2} (Profinite.CondensedAction.Modules R.toMon) :=
  HasDerivedCategory.standard _

/-- The standard localization universe for abelian groups.
Source: blueprint size convention (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance abDerived : HasDerivedCategory.{u + 2} Ab.{u + 1} :=
  HasDerivedCategory.standard _

/-- The standard localization universe for the existing action category.
Source: blueprint size convention (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance actionDerived (R : Coefficients.{u})
    [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)] :
    HasDerivedCategory.{u + 2} (Profinite.CondensedAction.ActionModule R.toMon (ks ≃ₐ[k] ks)) :=
  HasDerivedCategory.standard _

/-- Underived global sections and singleton evaluation are additive.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: the forgetful functor, presheaf inclusion and evaluation retain componentwise sums. -/
theorem sections_additive (R : Coefficients.{u}) (Y : Scheme.{u}) :
    (globalSections R.toMon Y).Additive ∧ (pointEvaluation R.toMon).Additive := by
  sorry

/-- Additivity of the actual global sections functor.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance globalSections_additive (R : Coefficients.{u}) (Y : Scheme.{u}) :
    (globalSections R.toMon Y).Additive := (sections_additive R Y).1

/-- Additivity of the actual singleton evaluation functor.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance pointEvaluation_additive (R : Coefficients.{u}) :
    (pointEvaluation R.toMon).Additive := (sections_additive R specZ).2

/-- Restriction to a geometric test is induced by its structural morphism to X.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def terminalMap (P : Profinite.{u}) : test k ks X a P ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk (test k ks X a P).hom

/-- The coefficient global sections comparison is specified by restriction to X^s.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
structure OrdinaryData (R : Coefficients.{u}) where
  /-- The equivariant geometric section functor, with its concrete normalization. -/
  geometric : GeometricData k ks X a R.toMon
  /-- Fully fixed sections with their specified inclusion and adjunction transposes. -/
  invariants : Profinite.CondensedAction.Invariants R.toMon (ks ≃ₐ[k] ks)
  /-- The natural underived section/invariant isomorphism. -/
  gamma : globalSections R.toMon X ≅
    geometric.functor ⋙ invariants.functor ⋙ pointEvaluation R.toMon
  /-- Under the fixed-section inclusion, gamma is the actual geometric restriction. -/
  normalization : ∀ (M : Modules R.toMon X)
    (m : (globalSections R.toMon X).obj M),
    ((geometric.sections.hom.app M).app (op (Profinite.of PUnit.{u + 1}))).hom
      ((((invariants.inclusion.app (geometric.functor.obj M)).hom.hom.app
        (op (Profinite.of PUnit.{u + 1}))).hom) ((gamma.hom.app M).hom m)) =
      (M.X.obj.map (terminalMap k ks X a (Profinite.of PUnit.{u + 1})).op).hom m

attribute [instance] GeometricData.additive Profinite.CondensedAction.Invariants.additive

/-- Singleton evaluation is exact, with no restriction on the condensed coefficient ring.
Source: Bhatt--Scholze Example 4.1.10
(blueprint: lem-sfb-condensed-galois-global-descent).
Proof: evaluation preserves kernels sectionwise. A section of an epimorphic target
lifts on a finite jointly surjective cover of the singleton. A nonempty member has a
point, and pullback along that point gives a lift over the singleton. The forgetful
internal-module functor computes kernels and cokernels. -/
theorem pointEvaluation_exact (R : Coefficients.{u}) :
    PreservesFiniteLimits (pointEvaluation R.toMon) ∧
      PreservesFiniteColimits (pointEvaluation R.toMon) := by
  sorry

/-- Left exactness of the actual singleton evaluation.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance pointEvaluation_limits (R : Coefficients.{u}) :
    PreservesFiniteLimits (pointEvaluation R.toMon) := (pointEvaluation_exact R).1

/-- Right exactness of the actual singleton evaluation.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance pointEvaluation_colimits (R : Coefficients.{u}) :
    PreservesFiniteColimits (pointEvaluation R.toMon) := (pointEvaluation_exact R).2

section Derived
variable (R : Coefficients.{u})
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R.toMon (ks ≃ₐ[k] ks))]
  (d : OrdinaryData k ks X a R)

/-- The ordinary total right-derived geometric section functor, on all unbounded complexes.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def derivedGeometric := d.geometric.functor.rightDerivedFunctor

/-- The ordinary total right-derived invariant-submodule functor.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def derivedInvariants := d.invariants.functor.rightDerivedFunctor

/-- The invariant side of geometric descent, including the exact evaluation at the point.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def invariantSide := derivedGeometric k ks X a R d ⋙
  derivedInvariants k ks X a R d ⋙ (pointEvaluation R.toMon).mapDerivedCategory

/-- The invariant side carries the canonical shifts of ordinary right-derived functors
and of the exact termwise singleton evaluation.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance invariantSide_commShift : (invariantSide k ks X a R d).CommShift ℤ :=
  inferInstanceAs ((d.geometric.functor.rightDerivedFunctor ⋙
    d.invariants.functor.rightDerivedFunctor ⋙
      (pointEvaluation R.toMon).mapDerivedCategory).CommShift ℤ)

/-- The canonical comparison is derived from the normalized underived restriction and
ordinary right-derived composition. No arbitrary derived isomorphism is chosen here.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def delta [d.geometric.functor.PreservesKInjectiveComplexes] :
    (globalSections R.toMon X).rightDerivedFunctor ≅ invariantSide k ks X a R d :=
  Functor.rightDerivedFunctorNatIso d.gamma ≪≫
    Functor.rightDerivedFunctorCompIso d.geometric.functor
      (d.invariants.functor ⋙ pointEvaluation R.toMon) ≪≫
    Functor.isoWhiskerLeft d.geometric.functor.rightDerivedFunctor
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        d.invariants.functor (pointEvaluation R.toMon))

end Derived
/-- Restrict coefficients by the actual pulled-back condensed ring morphism.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def restrictX {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    Modules R'.toMon Y ⥤ Modules R.toMon Y :=
  Mod.comap ((upperStarFromPoint Y).map φ.hom.hom)

/-- Scalar restriction on internal modules is exact for every coefficient map.
Source: Stacks Tag 0D6E (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: restriction changes only the action, leaving the underlying additive sheaf
and all maps fixed. Kernels and sheafified cokernels carry the restricted action,
so restriction creates them and preserves finite limits and colimits. -/
theorem restrictX_exact {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    PreservesFiniteLimits (restrictX φ Y) ∧ PreservesFiniteColimits (restrictX φ Y) := by
  sorry

/-- Scalar restriction preserves finite limits.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance restrictX_limits {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    PreservesFiniteLimits (restrictX φ Y) := (restrictX_exact φ Y).1

/-- Scalar restriction preserves finite colimits.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance restrictX_colimits {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    PreservesFiniteColimits (restrictX φ Y) := (restrictX_exact φ Y).2

/-- Restriction preserves addition because its underlying maps are unchanged.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance restrictX_additive {R R' : Coefficients.{u}} (φ : R ⟶ R') (Y : Scheme.{u}) :
    (restrictX φ Y).Additive := inferInstanceAs (Mod.comap _).Additive

/-- The actual scalar restriction on condensed modules.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
abbrev restrictCondensed {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    Profinite.CondensedAction.Modules R'.toMon ⥤
      Profinite.CondensedAction.Modules R.toMon :=
  Mod.comap φ.hom.hom

/-- Scalar restriction on internal condensed modules is exact.
Source: Stacks Tag 0D6E (blueprint: lem-sfb-condensed-galois-global-descent).
Proof: its underlying sheaf is unchanged; compute kernels and cokernels there with
the restricted ring action, just as for restrictX_exact. -/
theorem restrictCondensed_exact {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    PreservesFiniteLimits (restrictCondensed φ) ∧
      PreservesFiniteColimits (restrictCondensed φ) := by
  sorry

/-- Left exactness of condensed scalar restriction.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance restrictCondensed_limits {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    PreservesFiniteLimits (restrictCondensed φ) := (restrictCondensed_exact φ).1

/-- Right exactness of condensed scalar restriction.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
instance restrictCondensed_colimits {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    PreservesFiniteColimits (restrictCondensed φ) := (restrictCondensed_exact φ).2

/-- Scalar restriction followed by point evaluation is literally the same additive functor.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def evaluationRestriction {R R' : Coefficients.{u}} (φ : R ⟶ R') :
    restrictCondensed φ ⋙ pointEvaluation R.toMon ≅ pointEvaluation R'.toMon := Iso.refl _

section Scalar
variable {R R' : Coefficients.{u}} (φ : R ⟶ R')
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
  [IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R.toMon (ks ≃ₐ[k] ks))]
  [IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R'.toMon (ks ≃ₐ[k] ks))]
  (d : OrdinaryData k ks X a R) (d' : OrdinaryData k ks X a R')
  (r : CategoryTheory.CondensedBar.ScalarAction φ (ks ≃ₐ[k] ks))
  [PreservesFiniteLimits r.functor] [PreservesFiniteColimits r.functor]

/-- The complete scalar square. Both geometric and invariant derived arrows are
characterized by their total-derived units and by the actual underived section maps.
Source: blueprint paragraph (3), Stacks Tag 0D6E
(blueprint: lem-sfb-condensed-galois-global-descent). -/
structure ScalarData where
  /-- Geometric comparison after the given scalar restriction. -/
  geometric : CoefficientComparison (restrictX φ X) r.functor
    d.geometric.functor d'.geometric.functor
  /-- The geometric comparison leaves every original section unchanged. -/
  sections : ∀ (M : Modules R'.toMon X) (P : Profinite.{u})
    (x : Profinite.CondensedAction.sectionModule R.toMon
      (d.geometric.functor.obj ((restrictX φ X).obj M)).module P),
    ((d'.geometric.sections.hom.app M).app (op P)).hom
      (((r.underlying.hom.app (d'.geometric.functor.obj M)).hom.hom.app (op P)).hom
        ((((geometric.ordinary.hom.app M).val).hom.hom.app (op P)).hom x)) =
      ((d.geometric.sections.hom.app ((restrictX φ X).obj M)).app (op P)).hom x
  /-- The ordinary invariant-submodule comparison and its normalized derived arrow. -/
  invariants : CoefficientComparison r.functor (restrictCondensed φ)
    d.invariants.functor d'.invariants.functor
  /-- The invariant comparison is exactly the identity on included fixed sections. -/
  inclusion : ∀ N : Profinite.CondensedAction.ActionModule R'.toMon (ks ≃ₐ[k] ks),
    d.invariants.inclusion.app (r.functor.obj N) ≫ r.underlying.hom.app N =
      invariants.ordinary.hom.app N ≫
        (restrictCondensed φ).map (d'.invariants.inclusion.app N)
  /-- The global derived scalar comparison. -/
  global : (restrictX φ X).mapDerivedCategory ⋙
    (globalSections R.toMon X).rightDerivedFunctor ≅
      (globalSections R'.toMon X).rightDerivedFunctor
  /-- Its unit normalization uses the literal equality of underived global sections. -/
  global_unit : ∀ J : HomotopyCategory (Modules R'.toMon X) (ComplexShape.up ℤ),
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit
      (restrictX φ X) (globalSections R.toMon X)).app J ≫
      global.hom.app (DerivedCategory.Qh.obj J) =
        (globalSections R'.toMon X).rightDerivedFunctorUnit.app J
  /-- The invariant-side composite comparison. -/
  invariant : (restrictX φ X).mapDerivedCategory ⋙ invariantSide k ks X a R d ≅
    invariantSide k ks X a R' d'
  /-- It is the composite of the geometric, invariant and exact evaluation comparisons. -/
  invariant_formula : ∀ M : DerivedCategory (Modules R'.toMon X),
    invariant.hom.app M =
      (d.invariants.functor.rightDerivedFunctor ⋙
        (pointEvaluation R.toMon).mapDerivedCategory).map (geometric.derived.hom.app M) ≫
      (pointEvaluation R.toMon).mapDerivedCategory.map
        (invariants.derived.hom.app (d'.geometric.functor.rightDerivedFunctor.obj M)) ≫
      ((Functor.mapDerivedCategoryCompIso (restrictCondensed φ)
        (pointEvaluation R.toMon)).inv ≫
        (Functor.mapDerivedCategoryNatIso (evaluationRestriction φ)).hom).app
        (d'.invariants.functor.rightDerivedFunctor.obj
          (d'.geometric.functor.rightDerivedFunctor.obj M))

end Scalar
section Assertion
variable {R R' : Coefficients.{u}}
  [CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks)]
  [CategoryTheory.CondensedBar.ActionAbelian R' (ks ≃ₐ[k] ks)]
  [IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R.toMon (ks ≃ₐ[k] ks))]
  [IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R'.toMon (ks ≃ₐ[k] ks))]
  (d : OrdinaryData k ks X a R) (d' : OrdinaryData k ks X a R')
  [d.geometric.functor.PreservesKInjectiveComplexes]
  [d'.geometric.functor.PreservesKInjectiveComplexes]

/-- The scalar square for every derived morphism from M to the restriction of M'.
Exactness of restriction is a conclusion, not an assumption on the coefficient map.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def ScalarAssertion (φ : R ⟶ R') : Prop := by
  refine ∃ r : CategoryTheory.CondensedBar.ScalarAction φ (ks ≃ₐ[k] ks), ?_
  refine ∃ hl : PreservesFiniteLimits r.functor, ?_
  letI := hl
  refine ∃ hc : PreservesFiniteColimits r.functor, ?_
  letI := hc
  exact ∃ c : ScalarData k ks X a φ d d' r,
    ∀ (M : DerivedCategory (Modules R.toMon X))
      (M' : DerivedCategory (Modules R'.toMon X))
      (f : M ⟶ (restrictX φ X).mapDerivedCategory.obj M'),
    (globalSections R.toMon X).rightDerivedFunctor.map f ≫
        c.global.hom.app M' ≫ (delta k ks X a R' d').hom.app M' =
      (delta k ks X a R d).hom.app M ≫
        (invariantSide k ks X a R d).map f ≫ c.invariant.hom.app M'

end Assertion

/-- The full ordinary unbounded descent assertion for all condensed coefficients, with
canonical geometric/invariant comparisons, all scalar-and-input naturality, and the
shift compatibility giving a morphism of distinguished triangles.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-galois-global-descent). -/
def Assertion : Prop := by
  refine ∃ h : ∀ R : Coefficients.{u},
    CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks), ?_
  letI (R : Coefficients.{u}) : CategoryTheory.CondensedBar.ActionAbelian R (ks ≃ₐ[k] ks) := h R
  refine ∃ g : ∀ R : Coefficients.{u}, IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R.toMon (ks ≃ₐ[k] ks)), ?_
  letI (R : Coefficients.{u}) : IsGrothendieckAbelian.{u + 1}
    (Profinite.CondensedAction.ActionModule R.toMon (ks ≃ₐ[k] ks)) := g R
  refine ∃ d : ∀ R : Coefficients.{u}, OrdinaryData k ks X a R, ?_
  refine ∃ hi : ∀ R : Coefficients.{u}, (d R).geometric.functor.PreservesKInjectiveComplexes, ?_
  letI (R : Coefficients.{u}) : (d R).geometric.functor.PreservesKInjectiveComplexes := hi R
  exact
    (∀ R : Coefficients.{u}, NatTrans.CommShift (delta k ks X a R (d R)).hom ℤ) ∧
    (∀ R : Coefficients.{u}, (invariantSide k ks X a R (d R)).IsTriangulated) ∧
    (∀ (R R' : Coefficients.{u}) (φ : R ⟶ R'),
      ScalarAssertion k ks X a (d R) (d R') φ)

/-- Ordinary condensed Galois descent for global derived sections, with arbitrary
commutative condensed coefficients, arbitrary scalar maps and arbitrary unbounded inputs.
Source: main-20261015 blueprint, direct-images proof paragraph (3), structural input;
Bhatt--Scholze Examples 4.1.9--4.1.10, Stacks Tags 08BJ and 0D6E
(blueprint: lem-sfb-condensed-galois-global-descent).

Proof:
1. Use lem-sfb-field-profinite-galois-site and the dense-subsite equivalence to present
   sheaves on Spec(k)_proet by profinite continuous G-sets. The geometric test is the
   free object G times P, and the arithmetic test is P with trivial action.
2. Free objects form a dense subsite: G times S maps onto S by the action. An equivariant
   map G times T to G times P is (g,t) maps to (g b(t),f(t)). Its composition formula
   is (f,b)(h,c)=(fh,c h*b), the internal-action-site convention. Restricting to it gives
   the action-topos equivalence of lem-sfb-action-topos-geometric-restriction.
3. Descent along G times P to P identifies arithmetic sections with sections fixed after
   all profinite base changes. Its kernel pair is G times G times P. Apply
   lem-sfb-condensed-product-action-inflation with H=1, R=Z, to identify the right adjoint
   of trivial inflation. Uniqueness of left adjoints then identifies the point inverse
   images, including their finite-product and ring structures.
4. Apply lem-weil-pbc-ringed-presentation-transport and
   lem-sfb-internal-action-site-presentation, using the recorded internal/section-module
   equivalence. This gives the exact additive module equivalence with the normalized
   section formula at the geometric tests. It commutes with scalar restriction because
   section maps, restrictions and action maps are unchanged.
5. Structure direct image followed by this equivalence is the geometric section functor.
   lem-weil-pbc-profinite-test-object-functor identifies its tests with X^s[P]. The ringed
   site Grothendieck theorem and product-action-inflation give all three Grothendieck
   module categories and the normalized invariant-submodule adjunction.
6. Evaluation at the singleton is exact by pointEvaluation_exact: covers of the singleton
   split after choosing one point of a nonempty covering member. Forgetting internal
   modules computes finite limits and colimits.
7. Unbounded K-injective resolutions exist in the Grothendieck categories. The geometric
   functor has exact left adjoint a^* followed by the inverse equivalence, by
   det-prop-sfb-module-pullback-exact-main. Hence it preserves K-injectives by
   lem-weil-pbc-right-adjoint-preserves-kinjective; invariants have exact trivial
   inflation as left adjoint too. No bound on group cohomology is used.
8. The singleton descent equalizer gives gamma, normalized as restriction to X^s with
   invariant codomain. Apply it termwise to one K-injective resolution. Geometric
   sections remain K-injective, and evaluation is exact, giving exactly the definition
   delta by ordinary derived composition. Thus it is an isomorphism in D(Ab).
9. Scalar restriction is direct image on the identity underlying topos. Apply
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition to the geometric, invariant
   and point-evaluation commuting ringed squares. Its unit normalization gives exactly
   the CoefficientComparison equations, even for nonflat coefficient maps.
10. The associativity and unit equations of lem-pur-ringed-derived-composition-cocycle
    identify the two coefficient paths. Naturality of delta then gives ScalarAssertion
    for every morphism M to Res M', with the same canonical geometric/invariant maps.
11. The ordinary right-derived functors are triangulated. The normalized comparisons
    commute with their shifts by lem-weil-pbc-derived-adjunction-shift, equivalently
    because gamma on I[n] is gamma_I[n] including the signed differential. Naturality
    at C to A[1] gives the connecting square of every distinguished triangle. The
    trivial Galois group, empty X, and zero coefficient ring give the expected identities
    or zero maps. No continuous-cochain replacement or finite-cd assumption occurs.
-/
theorem condensed_galois_global_descent [CompactSpace X] [QuasiSeparatedSpace X] :
    Assertion k ks X a := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedGalois
