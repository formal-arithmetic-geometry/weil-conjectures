/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.NaiveCotangentComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.RingTheory.KoszulBaseChangeIso
import WeilConjectures.RingTheory.KoszulConormalBasis
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.RingTheory.CotangentResolutionCoherence
import WeilConjectures.RingTheory.CotangentTransitivityTriangle
import WeilConjectures.RingTheory.EtaleCotangentVanishing
import WeilConjectures.RingTheory.KoszulQuotientCotangentVanishing
import WeilConjectures.RingTheory.PolynomialCotangentIdentification
import WeilConjectures.RingTheory.TorIndependentCotangentBaseChange
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.EtaleLocalNormalForm

/-!
# Intrinsic cotangent complexes and local complete intersections

Source: Stacks Project, Cotangent Complex, Tags 08T2, 08T3, 08SJ, 08SL, 08QQ and 08R5
(blueprint: lem-trf-lci-cotangent-presentation).

The section model fixes every section complex and restriction map by the recorded
standard polynomial resolution. Its module sheafification is the intrinsic complex.
The existence statement below supplies the comparison maps with their normalizations.

## Main definitions

- `SectionModel`, `sheafComplex`, `cotangent`: the intrinsic standard model.
- `System`: the canonical affine and base-change arrows, normalized on sections.
- `ConormalModel`, `LciIdentification`: the two-term model and its affine normalization.
- `LciIdentifications`: the specified family of globally compatible lci comparisons.
- `Properties`: all assertions of the intrinsic lci presentation theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genInjectivity false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial
open Algebra.CotangentResolution

namespace AlgebraicGeometry.CotangentPresentation

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The standard section complex, using the alternating model in nonpositive degrees.
Source: Stacks, Tags 08PN and 08SX
(blueprint: lem-trf-lci-cotangent-presentation). -/
def ringComplex (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) :=
  differentialComplex (C.differentials (C.standard f))

/-- The section arrow of a map of sheaves of commutative rings.
Source: Stacks, Tag 08SX (blueprint: lem-trf-lci-cotangent-presentation). -/
def sectionArrow {T : TopCat.{u}}
    {A B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    (φ : A ⟶ B) (V : (Opens T)ᵒᵖ) : Arrow CommRingCat.{u} :=
  Arrow.mk (φ.hom.app V)

/-- The canonical ring square for restriction of sections.
Source: Stacks, Tag 08SX (blueprint: lem-trf-lci-cotangent-presentation). -/
def restrictionSquare {T : TopCat.{u}}
    {A B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    (φ : A ⟶ B) {V W : (Opens T)ᵒᵖ} (h : V ⟶ W) :
    sectionArrow φ V ⟶ sectionArrow φ W :=
  Arrow.homMk' (A.obj.map h) (B.obj.map h) (φ.hom.naturality h)

/-- The sectionwise standard differential complex before sheafification. The
identifications include differentials; restriction is exactly the standard ring-square
map, in every degree. Thus this is specified construction data, not an unspecified
object of the derived category.
Source: Stacks, Tags 08SR, 08SS, 08SW and 08SX
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure SectionModel (C : Coherence.{u}) {T : TopCat.{u}}
    {A B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}} (φ : A ⟶ B) where
  presheaf : CochainComplex (PresheafOfModules.{u} (B.obj ⋙ forget₂ _ RingCat)) ℤ
  sectionIso : ∀ V : (Opens T)ᵒᵖ,
    ((PresheafOfModules.evaluation (B.obj ⋙ forget₂ _ RingCat) V).mapHomologicalComplex
      (.up ℤ)).obj presheaf ≅
      ringComplex C (sectionArrow φ V)
  restriction : ∀ {V W : (Opens T)ᵒᵖ} (h : V ⟶ W) (i : ℤ)
      (x : (presheaf.X i).obj V),
    (sectionIso W).hom.f i ((presheaf.X i).map h x) =
      (C.differentialMap (C.standardMap (restrictionSquare φ h))).map.f i
        ((sectionIso V).hom.f i x)

/-- The intrinsic differential complex: module sheafification of the actual sectionwise
standard resolution. Normalization and alternating faces give the same derived object.
Source: Stacks, Tags 08SS and 08SW
(blueprint: lem-trf-lci-cotangent-presentation). -/
def sheafComplex {C : Coherence.{u}} {T : TopCat.{u}}
    {A B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}} {φ : A ⟶ B}
    (M : SectionModel C φ) :
    CochainComplex
      (SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) ℤ :=
  let F := PresheafOfModules.sheafification.{u}
    (R := (sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
    (𝟙 (B.obj ⋙ forget₂ _ RingCat))
  letI : F.Additive := (PresheafOfModules.sheafificationAdjunction.{u}
    (R := (sheafCompose (Opens.grothendieckTopology T)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
    (𝟙 (B.obj ⋙ forget₂ _ RingCat))).left_adjoint_additive
  (F.mapHomologicalComplex (.up ℤ)).obj M.presheaf

/-- The canonical map from the standard section complex into sections of its
sheafification, including the module structure.
Source: Stacks, Tag 08SX (blueprint: lem-trf-lci-cotangent-presentation). -/
def sectionMap {C : Coherence.{u}} {T : TopCat.{u}}
    {A B : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}} {φ : A ⟶ B}
    (M : SectionModel C φ) (V : (Opens T)ᵒᵖ) (i : ℤ) :
    (ringComplex C (sectionArrow φ V)).X i ⟶
      ((sheafComplex M).X i).val.obj V :=
  (M.sectionIso V).inv.f i ≫
    ((PresheafOfModules.sheafificationAdjunction.{u}
      (R := (sheafCompose (Opens.grothendieckTopology T)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
      (𝟙 (B.obj ⋙ forget₂ _ RingCat))).unit.app (M.presheaf.X i)).app V

attribute [irreducible] sheafComplex

/-- On a scheme morphism, the intrinsic complex uses the actual adjoint ring-sheaf map
`f⁻¹ O_S → O_X`, as required by the definition for ringed spaces.
Source: Stacks, Tag 08T2 (blueprint: lem-trf-lci-cotangent-presentation). -/
abbrev SchemeModel (C : Coherence.{u}) {X S : Scheme.{u}} (f : X ⟶ S) :=
  SectionModel C (Scheme.Modules.tensorPullbackRingMap f)

/-- The intrinsic cotangent object in the shared category `D(O_X)`.
Source: Stacks, Tag 08T2 (blueprint: lem-trf-lci-cotangent-presentation). -/
def cotangent {C : Coherence.{u}} {X S : Scheme.{u}} {f : X ⟶ S}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : SchemeModel C f) : schemeDerivedCategory.{u, w} X :=
  DerivedCategory.Q.{w}.obj (sheafComplex M)

/-- The inverse-image unit on structure-sheaf sections.
Source: Stacks, Tags 008X and 08T2
(blueprint: lem-trf-lci-cotangent-presentation). -/
def inverseUnit {X S : Scheme.{u}} (f : X ⟶ S) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f.base) CommRingCat.{u}
    (Opens.grothendieckTopology S) (Opens.grothendieckTopology X)).unit.app S.sheaf).hom

/-- The canonical square on inverse-image structure sheaves. Naturality and the unit
formula specify its base-ring arrow; the latter also includes every smaller open, so
there is no choice of an unrelated ring map.
Source: Stacks, Tags 08SV and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure BaseSquare {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X) (h : S' ⟶ S) where
  commutes : g ≫ f = f' ≫ h
  base : (TopCat.Sheaf.inverseImageRing f.base S.sheaf).obj ⟶
    (Opens.map g.base).op ⋙ (TopCat.Sheaf.inverseImageRing f'.base S'.sheaf).obj
  square : ∀ V : X.Opens,
    base.app (op V) ≫ (Scheme.Modules.tensorPullbackRingMap f').hom.app (op (g ⁻¹ᵁ V)) =
      (Scheme.Modules.tensorPullbackRingMap f).hom.app (op V) ≫ g.c.app (op V)
  unit : ∀ (V : S.Opens) (W : X'.Opens)
      (e : W ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) (e' : W ≤ f' ⁻¹ᵁ (h ⁻¹ᵁ V)),
    (inverseUnit f).app (op V) ≫ base.app (op (f ⁻¹ᵁ V)) ≫
      (TopCat.Sheaf.inverseImageRing f'.base S'.sheaf).obj.map (homOfLE e).op =
    h.c.app (op V) ≫ (inverseUnit f').app (op (h ⁻¹ᵁ V)) ≫
      (TopCat.Sheaf.inverseImageRing f'.base S'.sheaf).obj.map (homOfLE e').op

/-- The actual ring square on an open used by the differential-complex formula.
Source: Stacks, Tag 08QL (blueprint: lem-trf-lci-cotangent-presentation). -/
def BaseSquare.sectionSquare {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    (q : BaseSquare f f' g h) (V : X.Opens) :
    sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op V) ⟶
      sectionArrow (Scheme.Modules.tensorPullbackRingMap f') (op (g ⁻¹ᵁ V)) :=
  Arrow.homMk' (q.base.app (op V)) (g.c.app (op V)) (q.square V)

/-- Ordinary module pullback applied termwise, using its recorded adjunction
for zero preservation. Source: Stacks, Tag 0095
(blueprint: lem-trf-lci-cotangent-presentation). -/
def pullbackComplex {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  letI := (Scheme.Modules.tensorPullbackSectionAdjunction g).left_adjoint_additive
  ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj K

/-- The existing tilde functor on cochain complexes, expressed in the shared
module-sheaf category. Its additive structure is the published tilde structure.
Source: Stacks, Tag 01I6 (blueprint: lem-trf-lci-cotangent-presentation). -/
def tildeComplexFunctor (R : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)) ℤ :=
  (tilde.functor R).mapHomologicalComplex (.up ℤ)

/-- A complex of intrinsic cotangent models with the canonical chain comparisons
for all squares of schemes. The formula uses actual pure pullback sections and
standard differential maps, in every degree.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System (C : Coherence.{u}) :=
  Σ (model : ∀ {X S : Scheme.{u}} (f : X ⟶ S), SchemeModel C f),
    (∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
    Arrow.mk (f.appLE V U e) ⟶ sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op U)) ×
    (∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V),
    (tildeComplexFunctor Γ(X, U)).obj
      (ringComplex C (Arrow.mk (f.appLE V U e))) ⟶
        pullbackComplex hU.fromSpec (sheafComplex (model f))) ×
    (∀ {X S : Scheme.{u}} (f : X ⟶ S),
    sheafComplex (model f) ⟶
      (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (.up ℤ) 0).obj f.relativeDifferentials) ×
    (∀ {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X) (h : S' ⟶ S),
    g ≫ f = f' ≫ h → BaseSquare f f' g h) ×
    (∀ {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    (_q : BaseSquare f f' g h),
    pullbackComplex g (sheafComplex (model f)) ⟶ sheafComplex (model f'))

/-- The model component of the intrinsic cotangent construction.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System.model {C : Coherence.{u}} (D : System C) :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), SchemeModel C f :=
  D.1

/-- The chartSquare component of the intrinsic cotangent construction.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System.chartSquare {C : Coherence.{u}} (D : System C) :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
    Arrow.mk (f.appLE V U e) ⟶ sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op U) :=
  D.2.1

/-- The affine component of the intrinsic cotangent construction.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System.affine {C : Coherence.{u}} (D : System C) :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V),
    (tildeComplexFunctor Γ(X, U)).obj
      (ringComplex C (Arrow.mk (f.appLE V U e))) ⟶
        pullbackComplex hU.fromSpec (sheafComplex (D.model f)) :=
  D.2.2.1

/-- The augmentation component of the intrinsic cotangent construction.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System.augmentation {C : Coherence.{u}} (D : System C) :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    sheafComplex (D.model f) ⟶
      (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (.up ℤ) 0).obj f.relativeDifferentials :=
  D.2.2.2.1

/-- The square component of the intrinsic cotangent construction.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System.square {C : Coherence.{u}} (D : System C) :
    ∀ {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X) (h : S' ⟶ S),
    g ≫ f = f' ≫ h → BaseSquare f f' g h :=
  D.2.2.2.2.1

/-- The change component of the intrinsic cotangent construction.
Source: Stacks, Tags 08T2, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def System.change {C : Coherence.{u}} (D : System C) :
    ∀ {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    (_q : BaseSquare f f' g h),
    pullbackComplex g (sheafComplex (D.model f)) ⟶ sheafComplex (D.model f') :=
  D.2.2.2.2.2

attribute [irreducible] System

/-- The base-ring normalization of the affine chart square.
Source: Stacks, Tags 08SX, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def ChartSquareLeftLaw {C : Coherence.{u}} (D : System C) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
    (D.chartSquare f U V e).left = (inverseUnit f).app (op V) ≫
      (TopCat.Sheaf.inverseImageRing f.base S.sheaf).obj.map (homOfLE e).op

/-- The identity coefficient map of the affine chart square.
Source: Stacks, Tags 08SX, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def ChartSquareRightLaw {C : Coherence.{u}} (D : System C) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V),
    (D.chartSquare f U V e).right = 𝟙 Γ(X, U)

/-- The canonical affine comparison formula on standard-resolution sections.
Source: Stacks, Tags 08SX, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def AffineFormula {C : Coherence.{u}} (D : System C) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (i : ℤ)
    (x : (ringComplex C (Arrow.mk (f.appLE V U e))).X i),
    ((D.affine f U V hU hV e).f i).val.app (op (hU.fromSpec ⁻¹ᵁ U))
      (tilde.toOpen _ (hU.fromSpec ⁻¹ᵁ U) x) =
    Scheme.Modules.tensorPullbackSection hU.fromSpec ((sheafComplex (D.model f)).X i) U
      (sectionMap (D.model f) (op U) i
        ((C.differentialMap (C.standardMap (D.chartSquare f U V e))).map.f i x))

/-- The canonical augmentation formula on standard differential generators.
Source: Stacks, Tags 08SX, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def AugmentationFormula {C : Coherence.{u}} (D : System C) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (b : Γ(X, U))
    (x : (C.standard (sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op U))).algebra.obj
      (op ⦋0⦌)),
    (((D.augmentation f).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 f.relativeDifferentials).hom).val.app (op U))
      (sectionMap (D.model f) (op U) 0
        (complexGenerator (C.differentials
          (C.standard (sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op U)))) 0 b x)) =
    b • f.relativeDifferentialsDerivation.d
      ((C.standard (sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op U))).augmentation.app
        (op ⦋0⦌) x)

/-- The canonical base-change formula on pulled-back standard-resolution sections.
Source: Stacks, Tags 08SX, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def ChangeFormula {C : Coherence.{u}} (D : System C) : Prop :=
  ∀ {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    (q : BaseSquare f f' g h) (V : X.Opens) (i : ℤ)
    (x : (ringComplex C
      (sectionArrow (Scheme.Modules.tensorPullbackRingMap f) (op V))).X i),
    ((D.change q).f i).val.app (op (g ⁻¹ᵁ V))
      (Scheme.Modules.tensorPullbackSection g ((sheafComplex (D.model f)).X i) V
        (sectionMap (D.model f) (op V) i x)) =
      sectionMap (D.model f') (op (g ⁻¹ᵁ V)) i
        ((C.differentialMap (C.standardMap (q.sectionSquare V))).map.f i x)

/-- The generator normalizations of the intrinsic standard model and its maps.
The separate predicates retain every section formula while keeping the bundled
law type compact for kernel checking.
Source: Stacks, Tags 08SX, 08T3 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure SystemLaws {C : Coherence.{u}} (D : System C) : Prop where
  chartSquare_left : ChartSquareLeftLaw D
  chartSquare_right : ChartSquareRightLaw D
  affine_formula : AffineFormula D
  augmentation_formula : AugmentationFormula D
  change_formula : ChangeFormula D

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The natural derived comparison: first use the fixed derived tensor-pullback
counit, then the normalized chain comparison. This definition is actual morphism data.
Source: Stacks, Tag 08QQ (blueprint: lem-trf-lci-cotangent-presentation). -/
def derivedChange {C : Coherence.{u}} (D : System C)
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g : X' ⟶ X} {h : S' ⟶ S} (q : BaseSquare f f' g h) :
    (derivedPullback g).obj (cotangent (D.model f)) ⟶ cotangent (D.model f') :=
  (recordedDerivedPullbackCounit g).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (sheafComplex (D.model f))) ≫
    DerivedCategory.Q.{w}.map (D.change q)

/-- The conormal term `i^* I = I/I²` of a closed immersion, using its actual
kernel ideal sheaf and the existing module pullback.
Source: Stacks, Tag 08SL (blueprint: lem-trf-lci-cotangent-presentation). -/
def conormalTerm {U P : Scheme.{u}} (i : U ⟶ P) :=
  (Scheme.Modules.tensorPullback i).obj i.ker.toModules

/-- The other term in the conormal model is the actual pullback of relative
differentials. Source: Stacks, Tag 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def ambientDifferentials {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S) :=
  (Scheme.Modules.tensorPullback i).obj p.relativeDifferentials

/-- A finite Koszul-regular set of generators for the ideal near every point
of the closed subscheme. Ranks are allowed to vary and the sequence may be empty.
Source: Stacks, Tags 08SJ and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def IsKoszulImmersion {U P : Scheme.{u}} (i : U ⟶ P) : Prop :=
  ∀ x : U, ∃ W : P.affineOpens, i x ∈ W.1 ∧
    ∃ (r : ℕ) (a : Fin r → Γ(P, W.1)),
      RingTheory.Sequence.IsKoszulRegular a ∧ Ideal.span (Set.range a) = i.ker.ideal W

/-- The global two-term conormal complex. The two terms and its differential
are specified by the kernel inclusion, the universal derivation and pure tensor
sections. Thus the complex represents `[I/I² → i^* Ω¹_{P/S}]`, not an arbitrary
two-term perfect complex.
Source: Stacks, Tag 08SL (blueprint: lem-trf-lci-cotangent-presentation). -/
structure ConormalModel {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S) where
  complex : CochainComplex (SheafOfModules.{u} (moduleRings U.toRingedSpace)) ℤ
  negative : complex.X (-1) ≅ conormalTerm i
  zero : complex.X 0 ≅ ambientDifferentials i p
  other : ∀ j : ℤ, j ≠ -1 → j ≠ 0 → IsZero (complex.X j)
  differential : ∀ (W : P.Opens) (t : Γ(i.ker.toModules, W)),
    ((negative.inv ≫ complex.d (-1) 0 ≫ zero.hom).val.app (op (i ⁻¹ᵁ W)))
      (Scheme.Modules.tensorPullbackSection i i.ker.toModules W t) =
      Scheme.Modules.tensorPullbackSection i p.relativeDifferentials W
        (p.relativeDifferentialsDerivation.d (i.ker.toModulesι.val.app (op W) t))

/-- An affine presentation of the given geometric immersion, including the actual
ambient coordinate ring and its structure maps. The polynomial condition is on
that presentation, and is not a replacement geometric hypothesis.
Source: Stacks, Tags 08T3 and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure ImmersionChart {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S) where
  W : P.Opens
  A : S.Opens
  affineW : IsAffineOpen W
  affineA : IsAffineOpen A
  affineU : IsAffineOpen (i ⁻¹ᵁ W)
  intoA : W ≤ p ⁻¹ᵁ A
  intoA' : i ⁻¹ᵁ W ≤ (i ≫ p) ⁻¹ᵁ A
  presentation : Naive.Presentation (Arrow.mk ((i ≫ p).appLE A (i ⁻¹ᵁ W) intoA'))
  ambient : presentation.ring ≅ Γ(P, W)
  base : presentation.base ≫ ambient.hom = p.appLE A W intoA
  augmentation : ambient.hom ≫ i.app W = presentation.augmentation
  polynomial : Naive.IsLocalizedPolynomial presentation

/-- The conormal model on an affine chart is the sheafified existing naïve complex.
Both component maps have their pure-section normalization: the negative term sends
a relation class to its ideal section, and the zero term sends `b ⊗ dz` to `b dz`.
Source: Stacks, Tags 08RB and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure ConormalChartIso {U P S : Scheme.{u}} {i : U ⟶ P} {p : P ⟶ S}
    (N : ConormalModel i p) (T : ImmersionChart i p) where
  iso : (tildeComplexFunctor Γ(U, i ⁻¹ᵁ T.W)).obj
    (Naive.complex T.presentation) ≅ pullbackComplex T.affineU.fromSpec N.complex
  negative : ∀ (t : Γ(i.ker.toModules, T.W)) (z : RingHom.ker T.presentation.augmentation.hom)
    (_hz : T.ambient.hom z.val = i.ker.toModulesι.val.app (op T.W) t),
    ((iso.hom.f (-1) ≫ (Scheme.Modules.tensorPullback T.affineU.fromSpec).map
      N.negative.hom).val.app (op (T.affineU.fromSpec ⁻¹ᵁ (i ⁻¹ᵁ T.W))))
      (tilde.toOpen _ (T.affineU.fromSpec ⁻¹ᵁ (i ⁻¹ᵁ T.W))
        ((Naive.conormalIso T.presentation).inv (Naive.kernelClass T.presentation z))) =
    Scheme.Modules.tensorPullbackSection T.affineU.fromSpec (conormalTerm i) (i ⁻¹ᵁ T.W)
      (Scheme.Modules.tensorPullbackSection i i.ker.toModules T.W t)
  zero : ∀ (b : Γ(U, i ⁻¹ᵁ T.W)) (z : T.presentation.ring),
    ((iso.hom.f 0 ≫ (Scheme.Modules.tensorPullback T.affineU.fromSpec).map
      N.zero.hom).val.app (op (T.affineU.fromSpec ⁻¹ᵁ (i ⁻¹ᵁ T.W))))
      (tilde.toOpen _ (T.affineU.fromSpec ⁻¹ᵁ (i ⁻¹ᵁ T.W))
        ((Naive.differentialsIso T.presentation).inv (Naive.tensorGenerator T.presentation b z))) =
    T.affineU.fromSpec.app (i ⁻¹ᵁ T.W) b •
      Scheme.Modules.tensorPullbackSection T.affineU.fromSpec (ambientDifferentials i p)
        (i ⁻¹ᵁ T.W) (Scheme.Modules.tensorPullbackSection i p.relativeDifferentials T.W
          (p.relativeDifferentialsDerivation.d (T.ambient.hom z)))

/-- Derived tensor with a module placed in degree zero, in the published K-flat
monoidal structure. Source: Stacks, Tags 06YU and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def tensorModule {X : Scheme.{u}} (K : schemeDerivedCategory.{u, w} X)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) : schemeDerivedCategory.{u, w} X :=
  @MonoidalCategory.tensorObj (schemeDerivedCategory.{u, w} X) inferInstance
    (schemeDerivedTensorMonoidal X).toMonoidalCategoryStruct K
      ((DerivedCategory.singleFunctor.{w} _ 0).obj M)

/-- The affine comparison is invertible in the derived category. Its morphism
is the chain map already normalized on every section of the standard resolution.
Source: Stacks, Tag 08T3 (blueprint: lem-trf-lci-cotangent-presentation). -/
structure AffineIdentifications {C : Coherence.{u}} (D : System C) where
  iso : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V),
    (DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings (Spec Γ(X, U)).toRingedSpace))).obj
      ((tildeComplexFunctor Γ(X, U)).obj
        (ringComplex C (Arrow.mk (f.appLE V U e)))) ≅
      (DerivedCategory.Q.{w}
        (C := SheafOfModules.{u} (moduleRings (Spec Γ(X, U)).toRingedSpace))).obj
        (pullbackComplex (X := Spec Γ(X, U)) (Y := X) hU.fromSpec
          (sheafComplex (D.model f)))
  hom : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V),
    (iso f U V hU hV e).hom = DerivedCategory.Q.{w}.map (D.affine f U V hU hV e)

/-- On a K-flat complex, the fixed comparison to ordinary termwise pullback.
Source: Stacks, Tag 06YJ (blueprint: lem-trf-lci-cotangent-presentation). -/
def pullbackCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (derivedPullback g).obj (DerivedCategory.Q.{w}.obj K) ⟶
      DerivedCategory.Q.{w}.obj (pullbackComplex g K) :=
  (recordedDerivedPullbackCounit g).app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)

/-- The global lci isomorphism, with its inverse normalized by the existing naïve
comparison on every affine presentation and every lift to the standard resolution.
The affine normalization alone does not characterize a global derived morphism.
Global compatibility is asserted for the specified family `LciIdentifications`.
Source: Stacks, Tags 08RB and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure LciIdentification {C : Coherence.{u}} (D : System C)
    (F : AffineIdentifications D) (κ : Naive.Comparison C)
    {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S) where
  model : ConormalModel i p
  iso : DerivedCategory.Q.{w}.obj model.complex ≅ cotangent (D.model (i ≫ p))
  chart : ∀ T : ImmersionChart i p, ConormalChartIso model T
  normalization : ∀ (T : ImmersionChart i p)
    (a : Naive.PresentationMap (𝟙 _) (Naive.standardPresentation C _) T.presentation),
    (derivedPullback T.affineU.fromSpec).map iso.inv ≫
      pullbackCounit T.affineU.fromSpec model.complex ≫
      DerivedCategory.Q.{w}.map (chart T).iso.inv =
    pullbackCounit T.affineU.fromSpec (sheafComplex (D.model (i ≫ p))) ≫
      (F.iso (i ≫ p) (i ⁻¹ᵁ T.W) T.A T.affineU T.affineA T.intoA').inv ≫
      DerivedCategory.Q.{w}.map
        ((tildeComplexFunctor Γ(U, i ⁻¹ᵁ T.W)).map
          (κ.projection T.presentation T.polynomial a))

/-- A closed immersion into an open of finite-dimensional relative affine space,
with a locally finite Koszul-regular ideal. This bundles exactly the geometric
hypotheses for a local conormal presentation; the dimension may be zero.
Source: Stacks, Tags 08SJ and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure LciPresentation {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S) where
  dimension : ℕ
  ambient : P ⟶ AffineSpace (ULift.{u} (Fin dimension)) S
  closed : IsClosedImmersion i
  open_immersion : IsOpenImmersion ambient
  structure_map : ambient ≫ (AffineSpace (ULift.{u} (Fin dimension)) S ↘ S) = p
  koszul : IsKoszulImmersion i

/-- A specified family of global lci identifications, indexed by the geometric
presentations. Its global coherence is asserted by `Properties.conormal_baseChange`;
chartwise normalization is not used to infer uniqueness of global derived maps.
Source: Stacks, Tags 08QL, 08RB and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure LciIdentifications {C : Coherence.{u}} (D : System C)
    (F : AffineIdentifications D) (κ : Naive.Comparison C) where
  identification : ∀ {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S)
    (_T : LciPresentation i p), LciIdentification D F κ i p

/-- The canonical map between conormal models in a square of presentations.
The formulas specify the map on ideal sections and on differentials of ambient
sections, after restriction to any common open. In particular no identification
of unequal inverse-image opens is silently assumed.
Source: Stacks, Tags 08QL, 08RB and 08SL
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure ConormalChange {U P S U' P' S' : Scheme.{u}}
    {i : U ⟶ P} {p : P ⟶ S} {i' : U' ⟶ P'} {p' : P' ⟶ S'}
    (N : ConormalModel i p) (N' : ConormalModel i' p') (g : U' ⟶ U) (k : P' ⟶ P) where
  map : pullbackComplex g N.complex ⟶ N'.complex
  negative : ∀ (W : P.Opens) (V : U'.Opens)
    (e : V ≤ g ⁻¹ᵁ (i ⁻¹ᵁ W)) (e' : V ≤ i' ⁻¹ᵁ (k ⁻¹ᵁ W))
    (t : Γ(i.ker.toModules, W)) (t' : Γ(i'.ker.toModules, k ⁻¹ᵁ W))
    (_ht : k.app W (i.ker.toModulesι.val.app (op W) t) =
      i'.ker.toModulesι.val.app (op (k ⁻¹ᵁ W)) t'),
    (((Scheme.Modules.tensorPullback g).map N.negative.inv ≫ map.f (-1) ≫
      N'.negative.hom).val.app (op V))
      (((Scheme.Modules.tensorPullback g).obj (conormalTerm i)).val.map (homOfLE e).op
        (Scheme.Modules.tensorPullbackSection g (conormalTerm i) (i ⁻¹ᵁ W)
          (Scheme.Modules.tensorPullbackSection i i.ker.toModules W t))) =
    (conormalTerm i').val.map (homOfLE e').op
      (Scheme.Modules.tensorPullbackSection i' i'.ker.toModules (k ⁻¹ᵁ W) t')
  zero : ∀ (W : P.Opens) (V : U'.Opens)
    (e : V ≤ g ⁻¹ᵁ (i ⁻¹ᵁ W)) (e' : V ≤ i' ⁻¹ᵁ (k ⁻¹ᵁ W)) (r : Γ(P, W)),
    (((Scheme.Modules.tensorPullback g).map N.zero.inv ≫ map.f 0 ≫
      N'.zero.hom).val.app (op V))
      (((Scheme.Modules.tensorPullback g).obj (ambientDifferentials i p)).val.map (homOfLE e).op
        (Scheme.Modules.tensorPullbackSection g (ambientDifferentials i p) (i ⁻¹ᵁ W)
          (Scheme.Modules.tensorPullbackSection i p.relativeDifferentials W
            (p.relativeDifferentialsDerivation.d r)))) =
    (ambientDifferentials i' p').val.map (homOfLE e').op
      (Scheme.Modules.tensorPullbackSection i' p'.relativeDifferentials (k ⁻¹ᵁ W)
        (p'.relativeDifferentialsDerivation.d (k.app W r)))

/-- The identity comparison on ordinary complexes, with the section-normalized
identity pullback. Source: Stacks, Tags 0095 and 08QL
(blueprint: lem-trf-lci-cotangent-presentation). -/
def identityComplex {X : Scheme.{u}}
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    pullbackComplex (𝟙 X) K ⟶ K :=
  letI := (Scheme.Modules.tensorPullbackSectionAdjunction (𝟙 X)).left_adjoint_additive
  (NatTrans.mapHomologicalComplex (Scheme.Modules.tensorPullbackSectionId X).hom
    (.up ℤ)).app K

/-- The complete assertions of the intrinsic cotangent presentation theorem.
The existential data include the standard-resolution construction and a specified
family of global lci comparisons. The lci, Tor-amplitude and conormal base-change
clauses refer to this same family; they do not quantify over arbitrary global
isomorphisms satisfying only affine normalizations.
Source: Stacks, Tags 08T2, 08T3, 08SJ, 08SL, 08QQ and 08R5
(blueprint: lem-trf-lci-cotangent-presentation). -/
structure Properties {C : Coherence.{u}} (D : System C)
    (F : AffineIdentifications D) (κ : Naive.Comparison C)
    (E : LciIdentifications D F κ) : Prop where
  laws : SystemLaws D
  nonpositive : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (i : ℤ), 0 < i →
    IsZero ((sheafComplex (D.model f)).X i)
  restriction : ∀ {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    (q : BaseSquare f f' g h), IsOpenImmersion g → IsOpenImmersion h →
      IsIso (derivedChange D q)
  identity : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (q : BaseSquare f f (𝟙 X) (𝟙 S)),
    D.change q = identityComplex (sheafComplex (D.model f))
  composition : ∀ {X S X' S' X'' S'' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {f'' : X'' ⟶ S''}
    {g : X' ⟶ X} {h : S' ⟶ S} {g' : X'' ⟶ X'} {h' : S'' ⟶ S'}
    (q : BaseSquare f f' g h) (q' : BaseSquare f' f'' g' h')
    (q'' : BaseSquare f f'' (g' ≫ g) (h' ≫ h)),
    derivedChange D q'' =
      (recordedDerivedPullbackComposition g' g).inv.app (cotangent (D.model f)) ≫
        (derivedPullback g').map (derivedChange D q) ≫ derivedChange D q'
  baseChange : ∀ {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    (q : BaseSquare f f' g h), IsPullback g f' f h →
    PullbackStalkTensor.IsTorIndependent f h → IsIso (derivedChange D q)
  smooth : ∀ {X S : Scheme.{u}} (f : X ⟶ S), Smooth f →
    IsIso (DerivedCategory.Q.{w}.map (D.augmentation f))
  lci : ∀ {U P S : Scheme.{u}} (i : U ⟶ P) (p : P ⟶ S) (T : LciPresentation i p),
    SheafOfModules.IsFiniteLocallyFree ((E.identification i p T).model.complex.X (-1)) ∧
    SheafOfModules.IsFiniteLocallyFreeOfRank ((E.identification i p T).model.complex.X 0)
      T.dimension ∧
    ∀ (M : SheafOfModules.{u} (moduleRings U.toRingedSpace)) (a : ℤ),
      a < -1 ∨ 0 < a →
      IsZero ((DerivedCategory.homologyFunctor.{w} _ a).obj
        (tensorModule (DerivedCategory.Q.{w}.obj (E.identification i p T).model.complex) M))
  lci_baseChange : ∀ {U P S U' P' S' : Scheme.{u}}
    {i : U ⟶ P} {p : P ⟶ S} {i' : U' ⟶ P'} {p' : P' ⟶ S'}
    (g : U' ⟶ U) (k : P' ⟶ P) (h : S' ⟶ S)
    (n : ℕ) (j : P ⟶ AffineSpace (ULift.{u} (Fin n)) S),
    IsClosedImmersion i → IsOpenImmersion j →
    j ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = p → IsKoszulImmersion i →
    g ≫ i = i' ≫ k → IsPullback g (i' ≫ p') (i ≫ p) h → IsPullback k p' p h →
    PullbackStalkTensor.IsTorIndependent (i ≫ p) h → IsKoszulImmersion i'
  conormal_baseChange : ∀ {U P S U' P' S' : Scheme.{u}}
    {i : U ⟶ P} {p : P ⟶ S} {i' : U' ⟶ P'} {p' : P' ⟶ S'}
    (g : U' ⟶ U) (k : P' ⟶ P) (h : S' ⟶ S)
    (q : BaseSquare (i ≫ p) (i' ≫ p') g h)
    (T : LciPresentation i p) (T' : LciPresentation i' p'),
    g ≫ i = i' ≫ k →
    IsPullback g (i' ≫ p') (i ≫ p) h → IsPullback k p' p h →
    PullbackStalkTensor.IsTorIndependent (i ≫ p) h →
    ∃ m : ConormalChange (E.identification i p T).model
        (E.identification i' p' T').model g k,
      (derivedPullback g).map (E.identification i p T).iso.hom ≫ derivedChange D q =
        pullbackCounit g (E.identification i p T).model.complex ≫
          DerivedCategory.Q.{w}.map m.map ≫ (E.identification i' p' T').iso.hom

/-- Intrinsic cotangent complexes have the canonical lci conormal models,
Tor-independent base-change isomorphisms and smooth specialization.

Source: Stacks Project, Cotangent Complex, Tags 08T2, 08T3, 08SJ, 08SL, 08QQ and 08R5
(blueprint: lem-trf-lci-cotangent-presentation).

Proof:
1. Sheafify the sectionwise standard resolution. The normalized/alternating
   equivalence (lem-cbc-normalized-alternating-homotopy-equivalence) identifies
   its convention with the normalized complex. The section maps and localization
   comparisons of lem-trf-affine-cotangent-comparison, together with
   lem-weil-pbc-affine-tilde-gamma-adjunction and
   lem-weil-pbc-spec-tilde-stalk-localization, construct the affine arrows above.
   Check their cones stalkwise by lem-sc-abelian-sheaf-exact-iff-stalk-exact.
2. In a localized polynomial presentation apply
   lem-trf-cotangent-transitivity-triangle. The polynomial differential term is
   identified by lem-trf-smooth-cotangent-identification, using
   lem-weil-pbc-polynomial-ring-kahler-basis-any-variables and
   lem-weil-pbc-kahler-differentials-localization. The quotient term is the
   conormal module in degree -1 by lem-trf-koszul-quotient-cotangent-vanishing.
   The exact sequence of lem-sf-derived-homology-long-exact proves full
   vanishing outside degrees -1,0.
3. The normalized map of lem-trf-lci-naive-cotangent-model identifies the
   remaining truncation with the displayed conormal complex. Invert it.
   lem-sc-koszul-conormal-basis and the polynomial differential basis show
   that both terms are finite locally free. The generator formulas make these
   identifications agree on all smaller affine charts. Construct their global
   comparison through the global naive cotangent complex, retaining this chosen
   family as existential data; agreement of derived maps on charts alone would
   not imply their global equality.
4. By lem-pc-bounded-above-flat-kflat-site these local two-term complexes are
   K-flat. lem-pur-derived-change-of-rings computes their derived tensor with
   every module termwise, proving the Tor-amplitude bound.
5. For Tor-independent affine base change,
   lem-trf-tor-independent-cotangent-base-change makes the tensor of the standard
   resolution a polynomial resolution. Its differential tensors are free and
   K-flat by the same two cited K-flat and change-of-rings nodes. The universal
   property of def-weil-pbc-kahler-differentials identifies their base change
   degreewise, by dp tensor b mapping to d(p tensor 1) tensor b.
   lem-trf-cotangent-resolution-coherence identifies the resulting chain map
   with the standard functorial comparison.
6. lem-weil-pbc-ringed-topoi-derived-tensor-pullback computes the derived
   pullback by these flat representatives. Apply
   lem-weil-pbc-tilde-pullback-base-change degreewise and the affine comparison
   from step 1 to obtain the global base-change isomorphism.
7. Standard resolution functoriality in
   lem-trf-cotangent-resolution-coherence gives identity and composition, since
   both composite formulas have the same values on every differential tensor.
   The fixed counits and their recorded composition comparisons descend these
   equalities to the displayed derived equality.
8. For conormal compatibility use the Koszul resolution of the quotient.
   Polynomial rings are base-flat, and
   lem-pc-affine-flat-module-localization-preserves-flatness preserves this on
   ambient charts. Tor independence and lem-pur-derived-change-of-rings make
   its base change a resolution. lem-sc-koszul-base-change-iso then shows the
   new equations are Koszul-regular. lem-sc-koszul-conormal-basis identifies
   conormal base change on the equation classes, without assuming arbitrary
   tensor preserves a kernel.
9. The degree-zero differential comparison and these conormal maps give the
   specified map between two-term models. Naturality in
   lem-trf-lci-naive-cotangent-model gives the chartwise formulas. Choose the
   global identifications in step 3 from the global naive comparison and its
   functoriality. Inverting this globally natural comparison gives the
   displayed commuting square for that specified family. This is not an
   assertion about every affine-normalized global isomorphism.
10. For smooth f, sbc-thm-etale-local-normal-form factors affine charts through
    an etale algebra over a polynomial algebra. Use
    lem-trf-etale-cotangent-vanishing, the transitivity triangle and its long
    exact sequence to eliminate every nonzero cohomological degree.
    lem-trf-smooth-cotangent-identification computes the polynomial term.
    The naive comparison and the universal derivation identify degree zero
    with the existing relative differential sheaf; their section formulas
    identify the isomorphism with the augmentation above. -/
theorem exists_lciCotangentPresentation (C : Coherence.{u}) (κ : Naive.Comparison C) :
    ∃ (D : System C) (F : AffineIdentifications D) (E : LciIdentifications D F κ),
      Properties D F κ E := by
  sorry

end AlgebraicGeometry.CotangentPresentation
