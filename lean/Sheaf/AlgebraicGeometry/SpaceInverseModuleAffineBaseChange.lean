module

public import Sheaf.AlgebraicGeometry.SpaceInverseModuleDerivedLimit
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.CategoryTheory.FunctorPreservesSequentialHomotopyColimit
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing
import Sheaf.CategoryTheory.Sites.UnboundedLeraySections

/-! # Projection-induced reduction on étale charts

Source: Stacks Project, spaces-flat.tex, Tag 0CX8, lemma-compute-over-affine,
with the canonical maps of Tag 0CX6, lemma-compute-against-perfect
(blueprint: lem-sfb-space-inverse-module-affine-base-change).

All section functors, geometric adjunctions, tensor compositors and scalar adjunctions
below are the existing normalized constructions. The helpers spell out their composite;
they introduce no replacement module, derived category, or freely chosen comparison.
The natural index n represents the paper's level n + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

section Calculus

variable [∀ X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))),
  HasDerivedCategory.{w} X.SmallModules]
variable [∀ R : CommRingCat.{u}, HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable {X Y V W : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))}
variable {A B C : CommRingCat.{u}}

/-- The existing Yoneda embedding on the actual contravariant spectrum map.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleSpecArrow (φ : A ⟶ B) :
    schemeSpace (inverseModuleSpec B) ⟶ schemeSpace (inverseModuleSpec A) :=
  ObjectProperty.homMk ⟨yoneda.map (inverseModuleSpecMap φ)⟩

/-- Actual affine-base derived sections, abbreviated for the fixed Spec Z convention.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
abbrev inverseModuleSections (f : X ⟶ schemeSpace (inverseModuleSpec A)) :=
  spaceAffineDerivedSections (inverseModuleSpec A) (Iso.refl _) f

/-- The scheme chart's given map, with its representable source.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleChartArrow (U : X.EtaleSite) : schemeSpace U.obj.left ⟶ X :=
  ObjectProperty.homMk ⟨U.obj.hom⟩

/-- Sections on V, after actual derived restriction along v.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleLocalSections (f : X ⟶ schemeSpace (inverseModuleSpec A)) (v : V ⟶ X) :
    X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  spaceDerivedPullback v ⋙ inverseModuleSections (v ≫ f)

/-- The Γ-Spec scalar map attached to Spec(φ) is exactly φ.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: substitute the definition of spaceAffineRingMap. Naturality of ΓSpecIso
cancels its inverse and identifies pullback of global functions along Spec(φ) with φ. -/
theorem inverseModuleAffineRingMap (φ : A ⟶ B) :
    spaceAffineRingMap (Iso.refl _) (Iso.refl _) (inverseModuleSpecMap φ) = φ.hom := by
  sorry

attribute [local irreducible] spaceAffineDerivedSections Functor.leftAdjoint

/-- The existing section compositor, transported along the Γ-Spec identity.
Source: Stacks 0D6E, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleSectionsComposition (φ : A ⟶ B)
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (h : Y ⟶ X)
    (g : Y ⟶ schemeSpace (inverseModuleSpec B))
    (sq : h ≫ f = g ≫ inverseModuleSpecArrow φ) :
    derivedDirectImage h ⋙ inverseModuleSections f ≅
      inverseModuleSections g ⋙ RingDerivedScalarExtension.moduleDerivedRestriction φ.hom :=
  spaceDerivedSectionsComposition (Iso.refl _) (Iso.refl _)
      (inverseModuleSpecMap φ) f h g sq ≪≫
    Functor.isoWhiskerLeft (inverseModuleSections g)
      (eqToIso (congrArg (fun a : A →+* B ↦
        RingDerivedScalarExtension.moduleDerivedRestriction a)
        (inverseModuleAffineRingMap φ)))

/-- Pull sections back using the geometric unit and its normalized section compositor.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleSectionsPull (φ : A ⟶ B)
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (h : Y ⟶ X)
    (g : Y ⟶ schemeSpace (inverseModuleSpec B))
    (sq : h ≫ f = g ≫ inverseModuleSpecArrow φ) (K : X.DerivedModules) :
    (inverseModuleSections f).obj K ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction φ.hom).obj
        ((inverseModuleSections g).obj ((spaceDerivedPullback h).obj K)) :=
  (inverseModuleSections f).map ((spaceDerivedAdjunction h).unit.app K) ≫
    (inverseModuleSectionsComposition φ f h g sq).hom.app ((spaceDerivedPullback h).obj K)

/-- Exact restriction along the identity has its canonical identity comparison.
Source: Stacks 0D6D (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleScalarRestrictionId (A : CommRingCat.{u}) :
    RingDerivedScalarExtension.moduleDerivedRestriction (RingHom.id A) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsId A) ≪≫
    Functor.mapDerivedCategoryIdIso (ModuleCat.{u} A)

/-- A map over one base gives the square needed by the fixed Spec identity map.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: replace w by av using ha, reassociate, and use Spec.map_id and the fully
faithful schemeSpace embedding to identify schemeSpaceMap(Spec(id)) with identity. -/
theorem inverseModuleLocalRestriction_w
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (v : V ⟶ X) (z : W ⟶ X)
    (a : W ⟶ V) (ha : a ≫ v = z) :
    a ≫ (v ≫ f) = (z ≫ f) ≫ inverseModuleSpecArrow (𝟙 A) := by
  sorry

/-- The actual same-coefficient restriction between two local section functors.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleLocalRestriction
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (v : V ⟶ X) (z : W ⟶ X)
    (a : W ⟶ V) (ha : a ≫ v = z) (K : X.DerivedModules) :
    (inverseModuleLocalSections f v).obj K ⟶ (inverseModuleLocalSections f z).obj K :=
  inverseModuleSectionsPull (𝟙 A) (v ≫ f) a (z ≫ f)
      (inverseModuleLocalRestriction_w f v z a ha) ((spaceDerivedPullback v).obj K) ≫
    (inverseModuleScalarRestrictionId A).hom.app _ ≫
    (inverseModuleSections (z ≫ f)).map
      ((spaceDerivedPullbackComp v a).inv.app K ≫
        (eqToIso (congrArg spaceDerivedPullback ha)).hom.app K)

/-- The canonical degree-zero-to-derived-image comparison, retaining its derived unit.
Source: Stacks 0D6E, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleSingleDerivedImage (j : Y ⟶ X) (M : Y.Modules) :
    (DerivedCategory.singleFunctor X.SmallModules 0).obj
        (X.smallModuleRestriction.obj ((moduleDirectImage j).obj M)) ⟶
      (derivedDirectImage j).obj ((DerivedCategory.singleFunctor Y.SmallModules 0).obj
        (Y.smallModuleRestriction.obj M)) :=
  (DerivedCategory.singleFunctor X.SmallModules 0).map
      (X.smallModuleRestriction.map ((moduleDirectImage j).map
        (Y.smallModuleEquivalence.unitIso.hom.app M))) ≫
    DerivedCategory.Q.map
      (((smallModuleDirectImage j).mapCochainComplexSingleFunctor 0).inv.app
        (Y.smallModuleRestriction.obj M)) ≫
    spaceRightDerivedComplexUnit (smallModuleDirectImage j)
      ((CochainComplex.singleFunctor Y.SmallModules 0).obj (Y.smallModuleRestriction.obj M))

/-- The scalar adjunct of a projection to an ordinary module direct image.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleProjectionAdjunct (j : Y ⟶ X) (M : Y.Modules) (K : X.DerivedModules)
    (q : K ⟶ (DerivedCategory.singleFunctor X.SmallModules 0).obj
      (X.smallModuleRestriction.obj ((moduleDirectImage j).obj M))) :
    (spaceDerivedPullback j).obj K ⟶
      (DerivedCategory.singleFunctor Y.SmallModules 0).obj (Y.smallModuleRestriction.obj M) :=
  ((spaceDerivedAdjunction j).homEquiv _ _).symm
    (q ≫ inverseModuleSingleDerivedImage j M)

/-- The chart fibre product, with the existing sheaf pullback construction.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
abbrev inverseModuleChartFibre (j : Y ⟶ X) (U : X.EtaleSite) :=
  properQuotFibre j U.obj

/-- Commutativity of the chart pullback, as an equality of algebraic-space maps.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: both composites are the defining pullback projections followed by their maps;
pullback.condition gives their equality, and the full embeddings are faithful. -/
theorem inverseModuleChartSquare (j : Y ⟶ X) (U : X.EtaleSite) :
    properQuotFst j U.obj ≫ j = properQuotSnd j U.obj ≫ inverseModuleChartArrow U := by
  sorry

/-- The chart square over the affine coefficient map.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: use inverseModuleChartSquare, reassociate and substitute sq. -/
theorem inverseModuleChartBaseSquare (φ : A ⟶ B)
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (j : Y ⟶ X)
    (g : Y ⟶ schemeSpace (inverseModuleSpec B))
    (sq : j ≫ f = g ≫ inverseModuleSpecArrow φ) (U : X.EtaleSite) :
    properQuotSnd j U.obj ≫ (inverseModuleChartArrow U ≫ f) =
      (properQuotFst j U.obj ≫ g) ≫ inverseModuleSpecArrow φ := by
  sorry

/-- The actual projection-induced map before scalar adjunction. Its target is derived
sections on the sheaf fibre product U times_X Y, with the existing B-action.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleChartProjection (φ : A ⟶ B)
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (j : Y ⟶ X)
    (g : Y ⟶ schemeSpace (inverseModuleSpec B))
    (sq : j ≫ f = g ≫ inverseModuleSpecArrow φ)
    (M : Y.Modules) (K : X.DerivedModules)
    (q : K ⟶ (DerivedCategory.singleFunctor X.SmallModules 0).obj
      (X.smallModuleRestriction.obj ((moduleDirectImage j).obj M))) (U : X.EtaleSite) :
    (inverseModuleLocalSections f (inverseModuleChartArrow U)).obj K ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction φ.hom).obj
        ((inverseModuleLocalSections g (properQuotFst j U.obj)).obj
          ((DerivedCategory.singleFunctor Y.SmallModules 0).obj
            (Y.smallModuleRestriction.obj M))) :=
  inverseModuleSectionsPull φ (inverseModuleChartArrow U ≫ f) (properQuotSnd j U.obj)
      (properQuotFst j U.obj ≫ g) (inverseModuleChartBaseSquare φ f j g sq U)
      ((spaceDerivedPullback (inverseModuleChartArrow U)).obj K) ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction φ.hom).map
      ((inverseModuleSections (properQuotFst j U.obj ≫ g)).map
        (((spaceDerivedPullbackComp j (properQuotFst j U.obj)).symm ≪≫
            eqToIso (congrArg spaceDerivedPullback (inverseModuleChartSquare j U)) ≪≫
            spaceDerivedPullbackComp (inverseModuleChartArrow U)
              (properQuotSnd j U.obj)).inv.app K ≫
          (spaceDerivedPullback (properQuotFst j U.obj)).map
            (inverseModuleProjectionAdjunct j M K q)))

/-- Scalar extension of precisely the projection-induced map, by the fixed adjunction.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleChartBaseChange (φ : A ⟶ B)
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (j : Y ⟶ X)
    (g : Y ⟶ schemeSpace (inverseModuleSpec B))
    (sq : j ≫ f = g ≫ inverseModuleSpecArrow φ)
    (M : Y.Modules) (K : X.DerivedModules)
    (q : K ⟶ (DerivedCategory.singleFunctor X.SmallModules 0).obj
      (X.smallModuleRestriction.obj ((moduleDirectImage j).obj M))) (U : X.EtaleSite) :
    (RingDerivedScalarExtension.moduleDerivedExtension φ.hom).obj
        ((inverseModuleLocalSections f (inverseModuleChartArrow U)).obj K) ⟶
      (inverseModuleLocalSections g (properQuotFst j U.obj)).obj
        ((DerivedCategory.singleFunctor Y.SmallModules 0).obj
          (Y.smallModuleRestriction.obj M)) :=
  ((Adjunction.ofIsRightAdjoint
      (RingDerivedScalarExtension.moduleDerivedRestriction φ.hom)).homEquiv _ _).symm
    (inverseModuleChartProjection φ f j g sq M K q U)

/-- The canonical derived reduction supplied by an ordinary tensor reduction map.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleDerivedReduction (k : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (e : (moduleTensorPullback k).obj M ≅ N) :
    (spaceDerivedPullback k).obj
        ((DerivedCategory.singleFunctor X.SmallModules 0).obj (X.smallModuleRestriction.obj M)) ⟶
      (DerivedCategory.singleFunctor Y.SmallModules 0).obj (Y.smallModuleRestriction.obj N) :=
  (spaceDerivedPullbackCounit k).app
      ((CochainComplex.singleFunctor X.SmallModules 0).obj (X.smallModuleRestriction.obj M)) ≫
    DerivedCategory.Q.map
      (((smallModuleTensorPullback k).mapCochainComplexSingleFunctor 0).hom.app
        (X.smallModuleRestriction.obj M)) ≫
    (DerivedCategory.singleFunctor Y.SmallModules 0).map
      (Y.smallModuleRestriction.map
        ((moduleTensorPullback k).map (X.smallModuleEquivalence.unitIso.inv.app M) ≫ e.hom))

/-- Restriction with a coefficient change, using exactly the two geometric units and
pullback compositors; the final arrow is the specified derived module reduction.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleLocalPull (φ : A ⟶ B)
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) (k : Y ⟶ X)
    (g : Y ⟶ schemeSpace (inverseModuleSpec B))
    (v : V ⟶ X) (z : W ⟶ Y) (b : W ⟶ V)
    (sq : b ≫ (v ≫ f) = (z ≫ g) ≫ inverseModuleSpecArrow φ)
    (wz : z ≫ k = b ≫ v) (L : X.DerivedModules) (N : Y.DerivedModules)
    (d : (spaceDerivedPullback k).obj L ⟶ N) :
    (inverseModuleLocalSections f v).obj L ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction φ.hom).obj
        ((inverseModuleLocalSections g z).obj N) :=
  inverseModuleSectionsPull φ (v ≫ f) b (z ≫ g) sq ((spaceDerivedPullback v).obj L) ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction φ.hom).map
      ((inverseModuleSections (z ≫ g)).map
        (((spaceDerivedPullbackComp k z).symm ≪≫
            eqToIso (congrArg spaceDerivedPullback wz) ≪≫
            spaceDerivedPullbackComp v b).inv.app L ≫
          (spaceDerivedPullback z).map d))

/-- The affine-base square of the infinitesimal fibre.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: this is pullback.condition for properQuotFibre f (inverseModuleTest c n).
The second test map is, by definition, Spec of the nth ring projection. -/
theorem inverseModuleFibreBaseSquare
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (n : ℕ) :
    properQuotFst f (inverseModuleTest c n) ≫ f =
      properQuotSnd f (inverseModuleTest c n) ≫ inverseModuleSpecArrow (c.π.app (op n)) := by
  sorry

/-- The comparison at a specified level and specified homotopy-limit projection.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleLevelBaseChange
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (K : X.DerivedModules)
    (q : ∀ n : ℕ, K ⟶ inverseModuleDerivedTerm f (inverseModuleTest c n) (M n))
    (n : ℕ) (U : X.EtaleSite) :=
  inverseModuleChartBaseChange (c.π.app (op n)) f
    (properQuotFst f (inverseModuleTest c n)) (properQuotSnd f (inverseModuleTest c n))
    (inverseModuleFibreBaseSquare c f n) (M n) K (q n) U

/-- The same comparison before scalar adjunction, for writing coherence without
arbitrary choices of tensor associativity isomorphisms.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleLevelProjection
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (K : X.DerivedModules)
    (q : ∀ n : ℕ, K ⟶ inverseModuleDerivedTerm f (inverseModuleTest c n) (M n))
    (n : ℕ) (U : X.EtaleSite) :=
  inverseModuleChartProjection (c.π.app (op n)) f
    (properQuotFst f (inverseModuleTest c n)) (properQuotSnd f (inverseModuleTest c n))
    (inverseModuleFibreBaseSquare c f n) (M n) K (q n) U

/-- The canonical map between chart fibres induced by a chart morphism.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleChartRestriction (j : Y ⟶ X) {U V : X.EtaleSite} (a : V ⟶ U) :
    inverseModuleChartFibre j V ⟶ inverseModuleChartFibre j U :=
  properQuotFibreMap j a.hom

/-- Chart-fibre restriction preserves the projection to Y.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: properQuotFibreMap_fst applied to the underlying chart arrow gives the equation. -/
theorem inverseModuleChartRestriction_w (j : Y ⟶ X) {U V : X.EtaleSite} (a : V ⟶ U) :
    inverseModuleChartRestriction j a ≫ properQuotFst j U.obj = properQuotFst j V.obj := by
  sorry

/-- The base chart restriction commutes with its map to X.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: the chart morphism is a commuting costructured-arrow triangle. Yoneda and
the full embeddings preserve that equality. -/
theorem inverseModuleChartArrow_w {U V : X.EtaleSite} (a : V ⟶ U) :
    (ObjectProperty.homMk ⟨yoneda.map a.hom.left⟩ :
      schemeSpace V.obj.left ⟶ schemeSpace U.obj.left) ≫ inverseModuleChartArrow U =
        inverseModuleChartArrow V := by
  sorry

/-- Canonical chart restriction on the source of the reduction maps.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleSourceRestriction
    (f : X ⟶ schemeSpace (inverseModuleSpec A)) {U V : X.EtaleSite}
    (a : V ⟶ U) (K : X.DerivedModules) :=
  inverseModuleLocalRestriction f (inverseModuleChartArrow U) (inverseModuleChartArrow V)
    (ObjectProperty.homMk ⟨yoneda.map a.hom.left⟩) (inverseModuleChartArrow_w a) K

/-- Canonical chart restriction on the target of the reduction maps.
Source: Stacks 0CX8 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleTargetRestriction
    (g : Y ⟶ schemeSpace (inverseModuleSpec B)) (j : Y ⟶ X)
    (M : Y.Modules) {U V : X.EtaleSite} (a : V ⟶ U) :=
  inverseModuleLocalRestriction g (properQuotFst j U.obj) (properQuotFst j V.obj)
    (inverseModuleChartRestriction j a) (inverseModuleChartRestriction_w j a)
    ((DerivedCategory.singleFunctor Y.SmallModules 0).obj (Y.smallModuleRestriction.obj M))

/-- The scalar-restriction associator for a cone projection and one ring transition.
Source: Stacks 0CX6 (blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: the cone naturality equation identifies (r_n composed with pi_(n+1)) with pi_n.
This is exactly the equality of ring homomorphisms used for restriction of scalars. -/
theorem inverseModuleRingCone_w
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (n : ℕ) :
    (c.π.app (op n)).hom = (r n).hom.comp (c.π.app (op (n + 1))).hom := by
  sorry

/-- Exact restriction composition along the specified inverse sequence.
Source: Stacks 0CX6 (blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleRestrictionComposition
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (n : ℕ) :
    RingDerivedScalarExtension.moduleDerivedRestriction (r n).hom ⋙
        RingDerivedScalarExtension.moduleDerivedRestriction (c.π.app (op (n + 1))).hom ≅
      RingDerivedScalarExtension.moduleDerivedRestriction (c.π.app (op n)).hom :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (ModuleCat.restrictScalarsComp' (c.π.app (op (n + 1))).hom (r n).hom
        (c.π.app (op n)).hom (inverseModuleRingCone_w c n)).symm

/-- The canonical map between fibres over a fixed chart induced by a level transition.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleChartTransition
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (n : ℕ) (U : X.EtaleSite) :
    inverseModuleChartFibre (properQuotFst f (inverseModuleTest c n)) U ⟶
      inverseModuleChartFibre (properQuotFst f (inverseModuleTest c (n + 1))) U :=
  ObjectProperty.homMk (Limits.pullback.map
    (properQuotFst f (inverseModuleTest c n)).hom (inverseModuleChartArrow U).hom
    (properQuotFst f (inverseModuleTest c (n + 1))).hom (inverseModuleChartArrow U).hom
    (properQuotFibreMap f (inverseModuleTestMap c n)).hom (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans (congrArg (fun a ↦ a.hom)
      (properQuotFibreMap_fst f (inverseModuleTestMap c n))).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The two projection equations and the coefficient square for the chart transition.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change).
Proof: the pullback.map first-projection equation gives the first equality; the
second-projection equation and the original fibre-base square give the second.
The Spec transition square is inverseModuleTestMap_w. -/
theorem inverseModuleChartTransition_w
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (n : ℕ) (U : X.EtaleSite) :
    properQuotFst (properQuotFst f (inverseModuleTest c n)) U.obj ≫
        properQuotFibreMap f (inverseModuleTestMap c n) =
      inverseModuleChartTransition c f n U ≫
        properQuotFst (properQuotFst f (inverseModuleTest c (n + 1))) U.obj ∧
    inverseModuleChartTransition c f n U ≫
        (properQuotFst (properQuotFst f (inverseModuleTest c (n + 1))) U.obj ≫
          properQuotSnd f (inverseModuleTest c (n + 1))) =
      (properQuotFst (properQuotFst f (inverseModuleTest c n)) U.obj ≫
        properQuotSnd f (inverseModuleTest c n)) ≫ inverseModuleSpecArrow (r n) := by
  sorry

/-- The actual coefficient-changing target transition, induced by e_n.
Source: Stacks 0CX6, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleTargetTransition
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n) (n : ℕ) (U : X.EtaleSite) :=
  inverseModuleLocalPull (r n) (properQuotSnd f (inverseModuleTest c (n + 1)))
    (properQuotFibreMap f (inverseModuleTestMap c n))
    (properQuotSnd f (inverseModuleTest c n))
    (properQuotFst (properQuotFst f (inverseModuleTest c (n + 1))) U.obj)
    (properQuotFst (properQuotFst f (inverseModuleTest c n)) U.obj)
    (inverseModuleChartTransition c f n U) (inverseModuleChartTransition_w c f n U).2
    (inverseModuleChartTransition_w c f n U).1 _ _
    (inverseModuleDerivedReduction (properQuotFibreMap f (inverseModuleTestMap c n))
      (M (n + 1)) (M n) (e n))

/-- The projections of the specified product triangle, in the ambient derived category.
Source: Stacks 0CX5, 0CX8
(blueprint: lem-sfb-space-inverse-module-affine-base-change). -/
def inverseModuleLimitProjections
    {R : ℕ → CommRingCat.{u}} {r : ∀ n : ℕ, R (n + 1) ⟶ R n}
    (c : Cone (Functor.ofOpSequence r)) (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    [HasProduct (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))]
    (K : X.DerivedQCoh)
    (p : K ⟶ ∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) (n : ℕ) :
    K.obj ⟶ inverseModuleDerivedTerm f (inverseModuleTest c n) (M n) :=
  (X.derivedQCohProperty.ι).map (p ≫ Pi.π (fun m : ℕ ↦
    inverseModuleQCohTerm f (inverseModuleTest c m) (M m) (hq m)) n)

/-- Projection-induced derived reduction is invertible on every quasi-compact
quasi-separated étale scheme chart, and commutes with chart restriction and the given
module reductions. The last square is written before scalar adjunction; transposing
it gives exactly the derived-tensor transition square with the canonical associator.
Source: Stacks Project, spaces-flat.tex, Tag 0CX8, lemma-compute-over-affine,
with the canonical maps of Tag 0CX6, lemma-compute-against-perfect
(blueprint: lem-sfb-space-inverse-module-affine-base-change).

Proof:
1. By lem-sfb-space-inverse-module-derived-limit, K is in D_QCoh and its projections
   satisfy q_n = t_n q_(n+1). The closed-immersion quasi-coherent module theorem makes
   L_n = i_(n,*)M_n quasi-coherent, retaining its A_n-action. The perfect-telescope
   theorem computes sections on U as hocolim_m RΓ(X,E_m tensor L), functorially for
   both L = K and L = L_n, with the same perfect E_m.
2. Derived scalar extension is exact by lem-pur-derived-change-of-rings and is left
   adjoint to restriction by lem-pur-sheaf-ring-derived-coefficient-adjunction on the
   one-object site. The left-adjoint colimit theorem and
   lem-kun-functor-preserves-hocolim make it commute with these actual telescopes.
3. Apply lem-sfb-space-inverse-module-perfect-test-reduction to every E_m. Its
   projection-induced scalar adjunct is invertible and natural in E_m. Taking the
   functorial telescope gives an isomorphism from extended sections of K to sections
   of L_n with A_n-coefficients.
4. Transpose the entire telescope diagram. The defining equation Res(beta_m) eta =
   T_m(q_n), together with naturality of its cocones, identifies this isomorphism
   with the scalar adjunct of S(q_n). Use the telescope on complex representatives;
   no uniqueness of arbitrary triangle fillers from their legs is asserted.
5. Affine higher-image vanishing gives Ri_(n,*)M_n = i_(n,*)M_n with its ordinary
   degree-zero unit. The normalized derived étale-chart comparison and unbounded
   ringed-site Leray identify its chart sections with those on U_n. The comparison
   is identity on representative sections and respects the A_n-actions. Thus the
   constructed map is precisely inverseModuleLevelBaseChange, not an arbitrary iso.
6. The same unit, section compositor and pullback-square normalizations commute with
   chart restriction. Naturality of scalar adjunction gives the second displayed
   square. The equation q_n = t_n q_(n+1) and naturality give the final square before
   scalar adjunction. The target transition is constructed from the supplied e_n;
   relative A_(n+1)-flatness identifies its derived version with ordinary reduction.
   Transpose using the canonical restriction-composition isomorphism to obtain the
   tensor transition square, including its associativity identification.
-/
theorem inverseModuleAffineBaseChange
    (A : ℕ → CommRingCat.{u}) (r : ∀ n : ℕ, A (n + 1) ⟶ A n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    (hnil : ∀ (n : ℕ) (a : A (n + 1)), (r n) a = 0 → IsNilpotent a)
    (c : Cone (Functor.ofOpSequence r)) (hc : IsLimit c)
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (f : X ⟶ schemeSpace (inverseModuleSpec c.pt))
    (hsep : MapIsSeparated f) (hfp : ProperQuotFinitePresentation f)
    (M : ∀ n : ℕ, (properQuotFibre f (inverseModuleTest c n)).Modules)
    (hqc : ∀ n : ℕ, (M n).IsQuasicoherent)
    (hfin : ∀ n : ℕ, (M n).IsFinitePresentation)
    (hflat : ∀ (n : ℕ) (U : (properQuotFibre f (inverseModuleTest c n)).EtaleSite),
      ((schemeRestriction _ U).obj (M n)).IsFlatOver
        (yoneda.preimage (U.obj.hom ≫ (properQuotSnd f (inverseModuleTest c n)).hom.hom)).left)
    (hsupp : ∀ n : ℕ, ∃ (Z : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
      (i : Z ⟶ properQuotFibre f (inverseModuleTest c n)),
      IsRepresentableWith (fun _ _ a ↦ IsClosedImmersion a.left) i.hom.hom ∧
      MapIsProper (i ≫ properQuotSnd f (inverseModuleTest c n)) ∧ ∃ G : Z.Modules,
        G.IsQuasicoherent ∧ G.IsFiniteType ∧ Nonempty ((moduleDirectImage i).obj G ≅ M n))
    (e : ∀ n : ℕ,
      (moduleTensorPullback (properQuotFibreMap f (inverseModuleTestMap c n))).obj
        (M (n + 1)) ≅ M n)
    (hq : ∀ n : ℕ,
      X.derivedQCohProperty (inverseModuleDerivedTerm f (inverseModuleTest c n) (M n)))
    [HasProduct (fun n : ℕ ↦ inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))]
    (K : X.DerivedQCoh)
    (p : K ⟶ ∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n)))
    (δ : (∏ᶜ (fun n : ℕ ↦
      inverseModuleQCohTerm f (inverseModuleTest c n) (M n) (hq n))) ⟶ K⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle (fun n : ℕ ↦ inverseModuleDerivedTransition f
      (inverseModuleTestMap c n) (M n) (M (n + 1)) (e n) (hq n) (hq (n + 1))) K p δ) :
    (∀ (n : ℕ) (U : X.EtaleSite),
      CompactSpace U.obj.left.left → QuasiSeparatedSpace U.obj.left.left →
      IsIso (inverseModuleLevelBaseChange c f M K.obj
        (inverseModuleLimitProjections c f M hq K p) n U)) ∧
    (∀ (n : ℕ) (U V : X.EtaleSite) (a : V ⟶ U),
      CompactSpace U.obj.left.left → QuasiSeparatedSpace U.obj.left.left →
      CompactSpace V.obj.left.left → QuasiSeparatedSpace V.obj.left.left →
      (RingDerivedScalarExtension.moduleDerivedExtension (c.π.app (op n)).hom).map
          (inverseModuleSourceRestriction f a K.obj) ≫
        inverseModuleLevelBaseChange c f M K.obj
          (inverseModuleLimitProjections c f M hq K p) n V =
      inverseModuleLevelBaseChange c f M K.obj
          (inverseModuleLimitProjections c f M hq K p) n U ≫
        inverseModuleTargetRestriction (properQuotSnd f (inverseModuleTest c n))
          (properQuotFst f (inverseModuleTest c n)) (M n) a) ∧
    (∀ (n : ℕ) (U : X.EtaleSite),
      CompactSpace U.obj.left.left → QuasiSeparatedSpace U.obj.left.left →
      inverseModuleLevelProjection c f M K.obj
          (inverseModuleLimitProjections c f M hq K p) (n + 1) U ≫
        (RingDerivedScalarExtension.moduleDerivedRestriction
            (c.π.app (op (n + 1))).hom).map
          (inverseModuleTargetTransition c f M e n U) ≫
        (inverseModuleRestrictionComposition c n).hom.app _ =
      inverseModuleLevelProjection c f M K.obj
        (inverseModuleLimitProjections c f M hq K p) n U) := by
  sorry

end Calculus

end AlgebraicGeometry.AlgebraicSpace
