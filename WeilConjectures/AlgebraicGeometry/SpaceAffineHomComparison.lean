/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SpaceDerivedPullback
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
public import WeilConjectures.AlgebraicGeometry.RingDerivedScalarExtension
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Canonical affine global Hom comparison for algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0E4S and its preceding
construction (blueprint: def-sfb-space-affine-hom-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

section Ambient

variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]

/-- Internal Hom pullback is the transpose of pulled evaluation.
Source: Stacks 0E4S, 08J9 (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceInternalHomPullback {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (P Q : Y.DerivedModules) :
    (spaceDerivedPullback f).obj (Y.derivedHom.obj (op P, Q)) ⟶
      X.derivedHom.obj (op ((spaceDerivedPullback f).obj P), (spaceDerivedPullback f).obj Q) :=
  X.derivedDualityModel.closed.transpose _ _ _
    ((SingleComplex.derivedTensorComparison f).inv.app (Y.derivedHom.obj (op P, Q), P) ≫
      (spaceDerivedPullback f).map (Y.derivedDualityModel.closed.evaluation P Q))

/-- The terminal étale chart of a represented scheme.
Source: Stacks 03G7 (blueprint: def-sfb-space-affine-hom-comparison). -/
def affineIdentityChart (Y : Over S) : (schemeSpace Y).EtaleSite :=
  ⟨CostructuredArrow.mk (𝟙 (yoneda.obj Y)),
    ((representable_etale_scheme_tests (S := S)).2.2.2.2.2.2.2.1 Y Y (𝟙 Y)).2
      (inferInstance : Etale (𝟙 Y.left))⟩

/-- The Yoneda-preimage map is the required triangle for the terminal target chart.
Source: Stacks 03G8 (blueprint: def-sfb-space-affine-hom-comparison).
Proof: Yoneda maps its preimage back to the given chart map. The terminal chart has
identity structure map, and moduleChartTarget composes the original chart with f.
Substitute these descriptions and cancel composition with the identity. -/
theorem affineModuleChart_triangle (Y : Over S) {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (U : X.EtaleSite) :
    yoneda.map (yoneda.preimage (U.obj.hom ≫ f.hom.hom)) ≫
      (affineIdentityChart Y).obj.hom = ((moduleChartTarget f).obj U).hom := by
  sorry

/-- The unique map of any source chart to the represented target scheme.
Source: Stacks 03G8 (blueprint: def-sfb-space-affine-hom-comparison). -/
def affineModuleChart (Y : Over S) {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (U : X.EtaleSite) : ModuleChart f (affineIdentityChart Y) :=
  CostructuredArrow.mk (Y := U)
    (CostructuredArrow.homMk (yoneda.preimage (U.obj.hom ≫ f.hom.hom))
      (affineModuleChart_triangle Y f U))

/-- A-valued global sections of the original module topos, via the fixed basis equivalence.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineSections {A : Type u} [CommRing A] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y) :
    X.SmallModules ⥤ ModuleCat.{u} A :=
  X.smallModuleEquivalence.inverse ⋙ moduleDirectImage f ⋙
    SheafOfModules.evaluation (schemeSpace Y).structureSheaf (op (affineIdentityChart Y)) ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫ e.hom.appTop).hom)

/-- Sections are additive, since all chart projections preserve addition.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison).
Proof: the basis equivalences preserve biproducts. Direct image, evaluation and exact
restriction of scalars are additive; their composite is additive. -/
@[instance] theorem spaceAffineSections_additive {A : Type u} [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) : (spaceAffineSections Y e f).Additive := by
  sorry

/-- Actual unbounded derived global sections with their affine base action.
Source: Stacks 079V, 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineDerivedSections {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y) :
    X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (spaceAffineSections Y e f).rightDerivedFunctor

/-- The recorded internal Hom followed by actual derived global sections.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceGlobalHom {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y) :
    X.DerivedModulesᵒᵖ × X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  X.derivedHom ⋙ spaceAffineDerivedSections Y e f

/-- Projection of a global section to any actual étale chart.
Source: Stacks 03G8 (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineSectionAt {A : Type u} [CommRing A] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (M : X.SmallModules) (U : X.EtaleSite)
    (s : (spaceAffineSections Y e f).obj M) :
    (X.smallModuleEquivalence.inverse.obj M).val.obj (op U) :=
  ((moduleDirectImageModel f).projection (X.smallModuleEquivalence.inverse.obj M)
    (affineIdentityChart Y)).app (op (affineModuleChart Y f U)) s

/-- The ring map induced by a map between the represented affine schemes.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineRingMap {A B : Type u} [CommRing A] [CommRing B]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) : A →+* B :=
  (((Scheme.ΓSpecIso (.of A)).inv ≫ e.hom.appTop) ≫ g.left.appTop ≫
    e'.inv.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom).hom

/-- The ordinary sections/direct-image comparison is fixed by all chart projections.
Source: Stacks 03G8, 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def SpaceSectionsCompositionNormalized {A B : Type u} [CommRing A] [CommRing B]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (c : smallModuleDirectImage h ⋙ spaceAffineSections Y e f ≅
      spaceAffineSections Y' e' f' ⋙ ModuleCat.restrictScalars (spaceAffineRingMap e e' g)) :
    Prop :=
  ∀ (M : X'.SmallModules) (V : X.EtaleSite) (q : ModuleChart h V)
    (s : (spaceAffineSections Y e f).obj ((smallModuleDirectImage h).obj M)),
    ((moduleDirectImageModel h).projection (X'.smallModuleEquivalence.inverse.obj M) V).app
      (op q)
      (((X.smallModuleEquivalence.unitIso.inv.app
        ((moduleDirectImage h).obj (X'.smallModuleEquivalence.inverse.obj M))).val.app (op V))
        (spaceAffineSectionAt Y e f ((smallModuleDirectImage h).obj M) V s)) =
      spaceAffineSectionAt Y' e' f' M q.left ((c.hom.app M) s)

/-- The normalized sections comparison exists uniquely for any commuting affine square.
Source: Stacks 03G8, 0E4S (blueprint: def-sfb-space-affine-hom-comparison).
Proof: both modules are the compatible sections of M over all charts of X'.
The nested compatible-section limits on the left flatten to that one limit. The square
identifies the A-actions via the displayed ring map. Projection to any source chart is
exactly the stated iterated projection, which determines the map and its inverse.
The limit universal property gives naturality and uniqueness. -/
theorem spaceSectionsComposition_existsUnique {A B : Type u} [CommRing A] [CommRing B]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) :
    ∃! c : smallModuleDirectImage h ⋙ spaceAffineSections Y e f ≅
      spaceAffineSections Y' e' f' ⋙ ModuleCat.restrictScalars (spaceAffineRingMap e e' g),
      SpaceSectionsCompositionNormalized e e' g f h f' c := by
  sorry

/-- The unique comparison of actual section modules.
Source: Stacks 03G8 (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceSectionsComposition {A B : Type u} [CommRing A] [CommRing B]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) :=
  Classical.choose (spaceSectionsComposition_existsUnique e e' g f h f' sq)

end Ambient

/-- The fixed ordinary tensor adjunction transported through the basis equivalences.
Source: Stacks 03D7 (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceSmallTensorAdjunction {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    smallModuleTensorPullback h ⊣ smallModuleDirectImage h :=
  (Y.smallModuleEquivalence.symm.toAdjunction.comp (moduleTensorAdjunction h)).comp
    X.smallModuleEquivalence.toAdjunction

/-- The right-derived comparison on an actual complex, retaining the fixed unit.
Source: Stacks 079V (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceRightDerivedComplexUnit
    {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    [Abelian.HasKInjectiveResolutions C] [HasDerivedCategory.{w} C]
    {D : Type (u + 1)} [Category.{u} D] [Abelian D] [HasDerivedCategory.{w} D]
    (G : C ⥤ D) [G.Additive] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K)

/-- The derived adjunction is fixed by the ordinary unit and the shared derived counits.
Source: Stacks 07A6 (blueprint: def-sfb-space-affine-hom-comparison). -/
def SpaceDerivedAdjunctionNormalized {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (h : X ⟶ Y)
    (adj : spaceDerivedPullback h ⊣ derivedDirectImage h) : Prop :=
  ∀ K : CochainComplex Y.SmallModules ℤ,
    adj.unit.app (DerivedCategory.Q.obj K) ≫
      (derivedDirectImage h).map ((spaceDerivedPullbackCounit h).app K) =
    DerivedCategory.Q.map
      (((spaceSmallTensorAdjunction h).mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      spaceRightDerivedComplexUnit (smallModuleDirectImage h)
        (((smallModuleTensorPullback h).mapHomologicalComplex (.up ℤ)).obj K)

/-- Existence and uniqueness of the adjunction descending the ordinary scalar-one unit.
Source: Stacks 07A6, 06YY (blueprint: def-sfb-space-affine-hom-comparison).
Proof: apply the derived adjunction theorem to ordinary tensor pullback and direct image.
Flat-term K-flat and K-injective resolutions compute the respective functors. Their
universal counit and unit give the displayed normalization. Universal derivation makes
the unit the unique lift of the ordinary unit, and the unit determines the adjunction. -/
theorem spaceDerivedAdjunction_existsUnique {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (h : X ⟶ Y) :
    ∃! adj : spaceDerivedPullback h ⊣ derivedDirectImage h,
      SpaceDerivedAdjunctionNormalized h adj := by
  sorry

/-- The canonical derived adjunction with its ordinary-unit normalization.
Source: Stacks 07A6 (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceDerivedAdjunction {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (h : X ⟶ Y) :=
  Classical.choose (spaceDerivedAdjunction_existsUnique h)

section Ambient

variable [∀ X : AlgebraicSpace S, HasDerivedCategory.{w} X.SmallModules]

/-- Derived sections/direct-image composition retains the ordinary projection comparison.
Source: Stacks 0D6E, 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def SpaceDerivedSectionsCompositionNormalized
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y))
    (σ : derivedDirectImage h ⋙ spaceAffineDerivedSections Y e f ≅
      spaceAffineDerivedSections Y' e' f' ⋙
        RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)) :
    Prop :=
  ∀ (I : CochainComplex X'.SmallModules ℤ) [I.IsKInjective],
    spaceRightDerivedComplexUnit (spaceAffineSections Y e f)
        (((smallModuleDirectImage h).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (spaceAffineDerivedSections Y e f).map
        (spaceRightDerivedComplexUnit (smallModuleDirectImage h) I) ≫
      σ.hom.app (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map
      ((Functor.mapHomologicalComplexCompIso
        (spaceSectionsComposition e e' g f h f' sq) (.up ℤ)).hom.app I) ≫
      (ModuleCat.restrictScalars (spaceAffineRingMap e e' g)).mapDerivedCategoryFactors.inv.app
        (((spaceAffineSections Y' e' f').mapHomologicalComplex (.up ℤ)).obj I) ≫
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).map
        (spaceRightDerivedComplexUnit (spaceAffineSections Y' e' f') I)

/-- The unique derived composition comparison induced by actual global sections.
Source: Stacks 0D6E, 0E4S (blueprint: def-sfb-space-affine-hom-comparison).
Proof: resolve the input by a K-injective complex. Direct image followed by global
sections computes the right derived composite: the corresponding restriction of modules
from the point is exact, so the usual acyclicity argument applies to K-injectives.
Flatten compatible chart sections using spaceSectionsComposition. Exact scalar restriction
commutes with derivation. The displayed square is precisely the resulting map, and
comparison of resolutions proves naturality. Every input admits a K-injective resolution,
so this square also gives uniqueness; the inverse comes from the same sectionwise iso. -/
theorem spaceDerivedSectionsComposition_existsUnique
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) :
    ∃! σ : derivedDirectImage h ⋙ spaceAffineDerivedSections Y e f ≅
      spaceAffineDerivedSections Y' e' f' ⋙
        RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g),
      SpaceDerivedSectionsCompositionNormalized e e' g f h f' sq σ := by
  sorry

/-- The unique comparison, with its full K-injective normalization.
Source: Stacks 0D6E (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceDerivedSectionsComposition
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) :=
  Classical.choose (spaceDerivedSectionsComposition_existsUnique e e' g f h f' sq)

/-- A-linear pullback of global Hom: insert the geometric adjunction unit, use actual
sections/direct-image composition, and then apply the pulled-evaluation transpose.
Source: Stacks 0E4S, preceding construction
(blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceGlobalHomPullback
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) (P Q : X.DerivedModules) :
    (spaceGlobalHom Y e f).obj (op P, Q) ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).obj
        ((spaceGlobalHom Y' e' f').obj
          (op ((spaceDerivedPullback h).obj P), (spaceDerivedPullback h).obj Q)) :=
  (spaceAffineDerivedSections Y e f).map
      ((spaceDerivedAdjunction h).unit.app (X.derivedHom.obj (op P, Q))) ≫
    (spaceDerivedSectionsComposition e e' g f h f' sq).hom.app
      ((spaceDerivedPullback h).obj (X.derivedHom.obj (op P, Q))) ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).map
      ((spaceAffineDerivedSections Y' e' f').map (spaceInternalHomPullback h P Q))

/-- The canonical B-linear extension, defined by the scalar adjunction itself.
Source: Stacks 0E4S, preceding construction
(blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineHomBaseChange
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) (P Q : X.DerivedModules) :
    (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)).obj
      ((spaceGlobalHom Y e f).obj (op P, Q)) ⟶
      (spaceGlobalHom Y' e' f').obj
        (op ((spaceDerivedPullback h).obj P), (spaceDerivedPullback h).obj Q) :=
  ((Adjunction.ofIsRightAdjoint
    (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g))).homEquiv
      _ _).symm (spaceGlobalHomPullback e e' g f h f' sq P Q)

/-- Global Hom after derived scalar extension, as a bifunctor.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineHomSource
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X : AlgebraicSpace S} (f : X ⟶ schemeSpace Y) :
    X.DerivedModulesᵒᵖ × X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} B) :=
  spaceGlobalHom Y e f ⋙
    RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)

/-- Global Hom on the base change, as a bifunctor in the original two complexes.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineHomTarget
    {B : Type u} [CommRing B] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y' : Over S} (e' : Y'.left ≅ Spec (.of B))
    {X X' : AlgebraicSpace S} (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y') :
    X.DerivedModulesᵒᵖ × X.DerivedModules ⥤ DerivedCategory (ModuleCat.{u} B) :=
  ((spaceDerivedPullback h).op.prod (spaceDerivedPullback h)) ⋙ spaceGlobalHom Y' e' f'

/-- Both-variable naturality of the canonical scalar-adjoint comparison.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison).
Proof: transpose under the scalar adjunction. The unit is natural, the sections
comparison is a natural isomorphism, and the internal Hom map is a transpose of
natural evaluation. Precomposition in P and postcomposition in Q commute with each
of these operations. Transposing back gives exactly the displayed square. -/
theorem spaceAffineHomBaseChange_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y))
    (K L : X.DerivedModulesᵒᵖ × X.DerivedModules) (a : K ⟶ L) :
    (spaceAffineHomSource e e' g f).map a ≫
      spaceAffineHomBaseChange e e' g f h f' sq L.1.unop L.2 =
    spaceAffineHomBaseChange e e' g f h f' sq K.1.unop K.2 ≫
      (spaceAffineHomTarget e' h f').map a := by
  sorry

/-- The actual base-change arrow is a natural transformation in both arguments.
Its components are the scalar adjoints, rather than any chosen isomorphisms.
Source: Stacks 0E4S (blueprint: def-sfb-space-affine-hom-comparison). -/
def spaceAffineHomBaseChangeNat
    {A B : Type u} [CommRing A] [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    {Y Y' : Over S} (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S} (f : X ⟶ schemeSpace Y)
    (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫
      (ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g) :
        schemeSpace Y' ⟶ schemeSpace Y)) :
    spaceAffineHomSource e e' g f ⟶ spaceAffineHomTarget e' h f' where
  app K := spaceAffineHomBaseChange e e' g f h f' sq K.1.unop K.2
  naturality K L a := spaceAffineHomBaseChange_naturality e e' g f h f' sq K L a

/-- Cohomology of the actual global Hom complex is the group of shifted derived maps.
The isomorphism is the usual class-of-cocycle identification on a K-injective target.
Source: Stacks 08JA, 0E4S (blueprint: def-sfb-space-affine-hom-comparison).
Proof: replace the target by a K-injective complex and the source by a K-flat complex.
Their sheaf Hom is K-injective, so ordinary sections compute derived sections. Sections
of sheaf Hom are global module maps and commute with the products in total Hom. The
differential is d_Q a minus (-1)^j a d_P. Its cocycles are maps to Q[j], and its boundaries
are null-homotopic maps. K-injectivity identifies these homotopy classes with derived
maps. Exact restriction to A retains the additive groups, giving the displayed equivalence. -/
theorem spaceGlobalHom_cohomology
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (Y : Over S) (e : Y.left ≅ Spec (.of A)) {X : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (P Q : X.DerivedModules) (j : ℤ) :
    Nonempty (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
      ((spaceGlobalHom Y e f).obj (op P, Q))) ≃+ (P ⟶ Q⟦j⟧)) := by
  sorry

end Ambient

end AlgebraicGeometry.AlgebraicSpace
