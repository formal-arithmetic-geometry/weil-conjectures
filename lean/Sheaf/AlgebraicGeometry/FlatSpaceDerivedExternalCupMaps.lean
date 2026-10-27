module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleStructureMap

public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction

public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

public import Sheaf.CategoryTheory.RingedSiteGlobalDerivedAdjunction

public import Sheaf.Paper.RingedTensorSquarePresentation

public import Sheaf.CategoryTheory.RingedSiteDualityMaps

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.RingDerivedScalarExtension
public import Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors
public import Sheaf.AlgebraicGeometry.SpaceAffineHomComparison
public import Sheaf.AlgebraicGeometry.SpaceRelativeFlatClosedKernelBaseChange
public import Sheaf.CategoryTheory.RingedSiteModuleCupProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # Canonical maps for derived external cup on algebraic spaces

Source: Stacks 0B6C, 0FPL, 0FPN, 08IN, 08IR, 071Q and 0H9A
(blueprint: def-sfb-flat-space-derived-external-cup-maps).

## Main definitions
- `sections`, `mul`, `unit`, `rho`, `external`, `baseChange`: canonical scalar maps.
- `Comparisons`, `ScalarTensor`: normalized presentation witnesses.
- `ZariskiComparison`: comparison with the actual Zariski ringed-site cup.

No algebra, Kunneth or scalar-change theorem is assumed in these definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry.AlgebraicSpace
namespace FlatExternalCup

variable {S : Scheme.{u}}
  [∀ X : AlgebraicSpace S, HasDerivedCategory.{u} X.SmallModules]

/-- A represented morphism, using the existing fppf Yoneda embedding.
Source: Stacks 03G7 (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def schemeMap {Y Y' : Over S} (g : Y' ⟶ Y) : schemeSpace Y' ⟶ schemeSpace Y :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map g)

/-- The object RΓ(X,O_X), with the already specified scalar action.
Source: Stacks 08IN (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
abbrev sections (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :=
  (affineDerivedSections A Y e X f).obj X.derivedStructure

/-- Structure-module multiplication is the normalized unitor, transported from the unit.
Source: Stacks 0FPL (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def structureMul (X : AlgebraicSpace S) :
    (derivedDualityModel.{u, u} X).closed.tensor.obj (X.derivedStructure, X.derivedStructure) ⟶
      X.derivedStructure :=
  (derivedDualityModel.{u, u} X).closed.tensor.map
    (X := (X.derivedStructure, X.derivedStructure))
    (Y := ((derivedDualityModel.{u, u} X).closed.monoidal.tensorUnit, X.derivedStructure))
    (Prod.mkHom (derivedDualityModel.{u, u} X).unitIso.inv (𝟙 _)) ≫
    ((derivedDualityModel.{u, u} X).closed.monoidal.leftUnitor X.derivedStructure).hom

/-- Multiplication is precisely the existing scalar relative cup followed by O multiplication.
Source: Stacks 0B6C, 0FPL (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def mul (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :
    sections A Y e X f ⊗ sections A Y e X f ⟶ sections A Y e X f :=
  affineDerivedCup A Y e X f X.derivedStructure X.derivedStructure ≫
    (affineDerivedSections A Y e X f).map (structureMul X)

/-- Insertion of a scalar as multiplication by that scalar on O_X, before deriving.
Source: Stacks 0FPJ (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def scalar (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :
    ModuleCat.of A A ⟶
      (affineScalarSections A Y e X f).obj (SheafOfModules.unit X.smallStructureRings) :=
  let M := (affineScalarSections A Y e X f).obj
    (SheafOfModules.unit X.smallStructureRings)
  ModuleCat.ofHom (X := ModuleCat.of A A) (Y := M)
    (LinearMap.toSpanSingleton A M (𝟙 _))

/-- The actual structural unit R[0] → RΓ(X,O_X), using the universal derived unit.
Source: Stacks 0FPJ, 071Q (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def unit (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) :
    𝟙_ (DerivedCategory (ModuleCat.{u} A)) ⟶ sections A Y e X f :=
  (DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u} A)).inv ≫
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.app _ ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map (scalar A Y e X f)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (affineScalarSections A Y e X f) (.up ℤ) 0).inv.app _) ≫
    affineSectionsComplexUnit A Y e X f
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
        (SheafOfModules.unit X.smallStructureRings)) ≫
    (affineDerivedSections A Y e X f).map
      ((DerivedCategory.singleFunctorIsoCompQ X.SmallModules 0).inv.app _)

/-- Witness identifying the Hom(O,-) and compatible-chart models of the SAME sections.
The ordinary map is fixed by evaluation on every chart; the derived map by its unit.
Source: Stacks 03G8, 079V (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
structure SectionsComparison (A : Type u) [CommRing A] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y) where
  ordinary : affineScalarSections A Y e X f ≅ spaceAffineSections Y e f
  on_sections : ∀ (M : X.SmallModules) (U : X.EtaleSite)
    (s : (affineScalarSections A Y e X f).obj M),
    spaceAffineSectionAt Y e f M U (ordinary.hom.app M s) =
      (fullModuleSection X M s).val.app (op U)
        (1 : X.structureSheaf.obj.obj (op U))
  derived : affineDerivedSections A Y e X f ≅ spaceAffineDerivedSections Y e f
  on_complexes : ∀ P : CochainComplex X.SmallModules ℤ,
    affineSectionsComplexUnit A Y e X f P ≫ derived.hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P) ≫
      spaceRightDerivedComplexUnit (spaceAffineSections Y e f) P

/-- Canonical structure sheaf pullback on derived global sections, before scalar adjunction.
The right hand side retains the geometric unit and the regular-function structure map.
Source: Stacks 0FPN, 0H9A (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def pull {A B : Type u} [CommRing A] [CommRing B] {Y Y' : Over S}
    (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y))
    (c : SectionsComparison A Y e X f) (c' : SectionsComparison B Y' e' X' f') :
    sections A Y e X f ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).obj
        (sections B Y' e' X' f') :=
  c.derived.hom.app _ ≫
    (spaceAffineDerivedSections Y e f).map
      ((DerivedCategory.singleFunctor X.SmallModules 0).map
        (relativeClosedKernelSmallStructureMap h) ≫
      relativeClosedKernelDirectImageComparison h (SheafOfModules.unit X'.smallStructureRings)) ≫
    (spaceDerivedSectionsComposition e e' g f h f' sq).hom.app X'.derivedStructure ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g)).map
      (c'.derived.inv.app _)

/-- A normalized simultaneous choice of the two equivalent section presentations.
All entries are uniquely fixed by their displayed chart and derived-unit equations.
Source: Stacks 03G8, 079V (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
structure Comparisons where
  sections : ∀ (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y), SectionsComparison A Y e X f
  ring_id : ∀ (A : Type u) [CommRing A] (Y : Over S) (e : Y.left ≅ Spec (.of A)),
    spaceAffineRingMap e e (𝟙 Y) = RingHom.id A
  ring_comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {Y Y' Y'' : Over S} (e : Y.left ≅ Spec (.of A))
    (e' : Y'.left ≅ Spec (.of B)) (e'' : Y''.left ≅ Spec (.of C))
    (g : Y' ⟶ Y) (g' : Y'' ⟶ Y'),
    spaceAffineRingMap e e'' (g' ≫ g) =
      (spaceAffineRingMap e' e'' g').comp (spaceAffineRingMap e e' g)

/-- The coefficient compositor induced by actual composition of regular functions.
Source: Stacks 0FPN, 0H9A (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def restrictionComp (c : Comparisons (S := S))
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] {Y Y' Y'' : Over S}
    (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (e'' : Y''.left ≅ Spec (.of C)) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e' e'' g') ⋙
      RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g) ≅
    RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e'' (g' ≫ g)) :=
  ConstantScalarRealization.moduleDerivedRestrictionComposition
      (spaceAffineRingMap e e' g) (spaceAffineRingMap e' e'' g') ≪≫
    eqToIso (by rw [c.ring_comp e e' e'' g g'])

/-- Extension-of-scalars compositor, the left-adjoint mate of restriction composition.
Source: Stacks 0H9A (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def extensionComp (c : Comparisons (S := S))
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] {Y Y' Y'' : Over S}
    (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (e'' : Y''.left ≅ Spec (.of C)) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g) ⋙
      RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e' e'' g') ≅
    RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e'' (g' ≫ g)) :=
  (((ConstantScalarRealization.moduleDerivedAdjunction (spaceAffineRingMap e e' g)).comp
    (ConstantScalarRealization.moduleDerivedAdjunction
      (spaceAffineRingMap e' e'' g'))).ofNatIsoRight
       (restrictionComp c e e' e'' g g')).leftAdjointUniq
    (ConstantScalarRealization.moduleDerivedAdjunction (spaceAffineRingMap e e'' (g' ≫ g)))

/-- Exact restriction along the identity coefficient map has its canonical identity comparison.
Source: Stacks 0FPN (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def restrictionId (A : Type u) [CommRing A] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) (c : Comparisons (S := S)) :
    RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e (𝟙 Y)) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsId' _ (c.ring_id A Y e)) ≪≫
      Functor.mapDerivedCategoryIdIso (ModuleCat.{u} A)

/-- Identity extension of coefficients, by uniqueness of the left adjoint to identity.
Source: Stacks 0H9A (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def extensionId (A : Type u) [CommRing A] (Y : Over S)
    (e : Y.left ≅ Spec (.of A)) (c : Comparisons (S := S)) :
    RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e (𝟙 Y)) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  ((ConstantScalarRealization.moduleDerivedAdjunction
    (spaceAffineRingMap e e (𝟙 Y))).ofNatIsoRight
      (restrictionId A Y e c)).leftAdjointUniq Adjunction.id

/-- Pullback over a fixed affine base, using the normalized section presentations.
Source: Stacks 0FPN (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def rho (c : Comparisons (S := S)) (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A)) {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y)
    (sq : h ≫ f = f') : sections A Y e X f ⟶ sections A Y e X' f' :=
  pull e e (𝟙 Y) f h f' (by
      rw [sq]
      congr 1)
    (c.sections A Y e X f) (c.sections A Y e X' f') ≫
      (restrictionId A Y e c).hom.app _

/-- External cup is multiplication of the two projection pullbacks, in that order.
Source: Stacks 08IN, 0B6C (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def external (c : Comparisons (S := S)) (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A)) {X Z W : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (g : Z ⟶ schemeSpace Y) (k : W ⟶ schemeSpace Y)
    (p : W ⟶ X) (q : W ⟶ Z) (hp : p ≫ f = k) (hq : q ≫ g = k) :
    sections A Y e X f ⊗ sections A Y e Z g ⟶ sections A Y e W k :=
  (rho c A Y e f p k hp ⊗ₘ rho c A Y e g q k hq) ≫ mul A Y e W k

/-- The canonical B-linear base-change comparison is the scalar-adjoint of pullback.
Source: Stacks 08IR, 0H9A (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def baseChange (c : Comparisons (S := S))
    {A B : Type u} [CommRing A] [CommRing B] {Y Y' : Over S}
    (e : Y.left ≅ Spec (.of A)) (e' : Y'.left ≅ Spec (.of B))
    (g : Y' ⟶ Y) {X X' : AlgebraicSpace S}
    (f : X ⟶ schemeSpace Y) (h : X' ⟶ X) (f' : X' ⟶ schemeSpace Y')
    (sq : h ≫ f = f' ≫ (ObjectProperty.homMk
      ((Scheme.fppfTopology.over S).yoneda.map g) : schemeSpace Y' ⟶ schemeSpace Y)) :
    (RingDerivedScalarExtension.moduleDerivedExtension (spaceAffineRingMap e e' g)).obj
      (sections A Y e X f) ⟶ sections B Y' e' X' f' :=
  ((Adjunction.ofIsRightAdjoint
    (RingDerivedScalarExtension.moduleDerivedRestriction (spaceAffineRingMap e e' g))).homEquiv
      _ _).symm (pull e e' g f h f' sq
        (c.sections A Y e X f) (c.sections B Y' e' X' f'))

/-- Flat qcqs is the conjunction of the existing chartwise flatness and the two
quasi-compactness predicates; the second quasi-compactness is that of the diagonal.
Source: Stacks 08IN, 08IR (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def admissible {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  MapIsFlat f ∧ MapIsQuasiCompact f.hom.hom ∧
    MapIsQuasiCompact (Limits.pullback.diagonal f.hom.hom)

/-- The fixed Koszul symmetry of the existing ordinary-module derived tensor.
Source: Stacks 0FPM (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def symmetry (A : Type u) [CommRing A]
    (K L : DerivedCategory (ModuleCat.{u} A)) : K ⊗ L ≅ L ⊗ K :=
  (DerivedCategory.symmetricCategory (ModuleCat.{u} A)).braiding K L

/-- The canonical derived scalar tensor is specified on flat-term K-flat complexes
by the actual ordinary extension-of-scalars tensor comparison. Its unit is specified
by the ordinary scalar unit and localization. These equations determine its data.
Source: Stacks 07A4, 0H9A (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
structure ScalarTensor {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) where
  tensor : ∀ K L : DerivedCategory (ModuleCat.{u} A),
    (RingDerivedScalarExtension.moduleDerivedExtension a).obj K ⊗
      (RingDerivedScalarExtension.moduleDerivedExtension a).obj L ≅
    (RingDerivedScalarExtension.moduleDerivedExtension a).obj (K ⊗ L)
  naturality : ∀ {K K' L L' : DerivedCategory (ModuleCat.{u} A)}
    (f : K ⟶ K') (g : L ⟶ L'),
    ((RingDerivedScalarExtension.moduleDerivedExtension a).map f ⊗ₘ
      (RingDerivedScalarExtension.moduleDerivedExtension a).map g) ≫ (tensor K' L').hom =
    (tensor K L).hom ≫ (RingDerivedScalarExtension.moduleDerivedExtension a).map (f ⊗ₘ g)
  unit : 𝟙_ (DerivedCategory (ModuleCat.{u} B)) ≅
    (RingDerivedScalarExtension.moduleDerivedExtension a).obj
      (𝟙_ (DerivedCategory (ModuleCat.{u} A)))
  tensor_representatives : ∀ (P Q : CochainComplex (ModuleCat.{u} A) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat Q →
    (∀ n : ℤ, Module.Flat A (P.X n)) → (∀ n : ℤ, Module.Flat A (Q.X n)) →
    (tensor (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
      (RingDerivedScalarExtension.moduleDerivedExtension a).map
        (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      ConstantScalarRealization.moduleRepresentative a (P ⊗ Q) =
    (ConstantScalarRealization.moduleRepresentative a P ⊗ₘ
      ConstantScalarRealization.moduleRepresentative a Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        (((ModuleCat.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars a).mapHomologicalComplex (.up ℤ)).obj Q) ≫
      DerivedCategory.Q.map
        (Functor.LaxMonoidal.μ ((ModuleCat.extendScalars a).mapHomologicalComplex (.up ℤ)) P Q)
  unit_representative : unit.hom ≫
      (RingDerivedScalarExtension.moduleDerivedExtension a).map
        (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
      ConstantScalarRealization.moduleRepresentative a
        (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) =
    Functor.LaxMonoidal.ε DerivedCategory.Q ≫
      DerivedCategory.Q.map (Functor.LaxMonoidal.ε
        ((ModuleCat.extendScalars a).mapHomologicalComplex (.up ℤ)))

/-- Derived restriction is lax tensor by the scalar extension adjunction and its
normalized strong tensor comparison. This is the usual change-of-coefficients cup.
Source: Stacks 0B6C, 07A6 (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def restrictionTensor {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B)
    (t : ScalarTensor a) (K L : DerivedCategory (ModuleCat.{u} B)) :
    (RingDerivedScalarExtension.moduleDerivedRestriction a).obj K ⊗
      (RingDerivedScalarExtension.moduleDerivedRestriction a).obj L ⟶
    (RingDerivedScalarExtension.moduleDerivedRestriction a).obj (K ⊗ L) :=
  (ConstantScalarRealization.moduleDerivedAdjunction a).homEquiv _ _
    ((t.tensor _ _).inv ≫
      ((ConstantScalarRealization.moduleDerivedAdjunction a).counit.app K ⊗ₘ
        (ConstantScalarRealization.moduleDerivedAdjunction a).counit.app L))

variable [∀ Z : Scheme.{u}, HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The genuine Zariski ringed site with a representative-normalized derived tensor.
Source: Stacks 071Q, 0FPJ (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def zariskiCorner (Z : Scheme.{u})
    (M : RingedSiteDualityModel.{u, u, u, u} (Opens.grothendieckTopology Z)
      Z.sheaf) : SheafOfModules.RingedTensorCorner.{u, u} where
  site := Z.Opens
  topology := Opens.grothendieckTopology Z
  ring := Z.sheaf
  tensor := M.closed.tensor

/-- Ordinary Zariski multiplication, using the unit constraint of its fixed derived tensor.
Source: Stacks 0FPJ (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def zariskiStructureMul (Z : Scheme.{u})
    (M : RingedSiteDualityModel.{u, u, u, u} (Opens.grothendieckTopology Z)
      Z.sheaf) :
    M.closed.tensor.obj
      (ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z) Z.sheaf,
        ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z) Z.sheaf) ⟶
    ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z) Z.sheaf :=
  M.closed.tensor.map
    (X := (ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z) Z.sheaf,
      ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z) Z.sheaf))
    (Y := (M.closed.monoidal.tensorUnit,
      ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z) Z.sheaf))
    (Prod.mkHom M.unitIso.inv (𝟙 _)) ≫
    (M.closed.monoidal.leftUnitor _).hom

/-- The canonical derived O_Z → Rε_*O_etale; it is not an unspecified structure isomorphism.
Source: Stacks 071Q (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def zariskiDerivedStructureInsertion (Z : Over S)
    (i : SheafOfModules.unit (moduleRings Z.left.toRingedSpace) ⟶
      (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).obj
        (SheafOfModules.unit (schemeSpace Z).smallStructureRings)) :
    ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z.left) Z.left.sheaf ⟶
    (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).rightDerivedFunctor.obj
      (schemeSpace Z).derivedStructure :=
  DerivedCategory.Q.map
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map i) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)) (.up ℤ) 0).inv.app _) ≫
    spaceRightDerivedComplexUnit
      (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z))
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
        (SheafOfModules.unit (schemeSpace Z).smallStructureRings)) ≫
    (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).rightDerivedFunctor.map
      ((DerivedCategory.singleFunctorIsoCompQ (schemeSpace Z).SmallModules 0).inv.app _)

/-- All Zariski comparison data are tied to actual restriction, regular functions,
and the universal right-derived units. The tensor model is tied to its flat representatives.
Source: Stacks 071Q, 0FPJ (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
structure ZariskiComparison (A : Type u) [CommRing A] (Y Z : Over S)
    (e : Y.left ≅ Spec (.of A)) (g : Z ⟶ Y) where
  model : RingedSiteDualityModel.{u, u, u, u}
    (Opens.grothendieckTopology Z.left) Z.left.sheaf
  tensor : SheafOfModules.RingedTensorModel (zariskiCorner Z.left model)
  tensor_normalized : ∀ (P Q : CochainComplex
    (SheafOfModules.{u} (moduleRings Z.left.toRingedSpace)) ℤ)
    (hP : (zariskiCorner Z.left model).mateFlat P)
    (hQ : (zariskiCorner Z.left model).mateFlat Q),
    ∃ (hP' : CochainComplex.IsKFlatIndependentCoefficients
      (J := Opens.grothendieckTopology Z.left) (R := Z.left.sheaf) P)
      (hQ' : CochainComplex.IsKFlatIndependentCoefficients
      (J := Opens.grothendieckTopology Z.left) (R := Z.left.sheaf) Q),
      tensor.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (model.models.iso _ _ model.closed P Q hP' hQ').hom
  scalar : A →+* SheafOfModules.RingedSiteCup.scalars (zariskiCorner Z.left model)
  scalar_sections : ∀ (a : A) (U : Z.left.Opens),
    (scalar a).val (op U) =
      Z.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op
        (((Scheme.ΓSpecIso (.of A)).inv ≫ (g.left ≫ e.hom).appTop).hom a)
  scalar_tensor : ScalarTensor scalar
  [global_additive : (SheafOfModules.RingedSiteCup.globalSections
    (zariskiCorner Z.left model)).Additive]
  [restriction_additive :
    (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).Additive]
  [composite_additive : (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z) ⋙
    SheafOfModules.RingedSiteCup.globalSections (zariskiCorner Z.left model)).Additive]
  ordinary : affineScalarSections A Y e (schemeSpace Z) (schemeMap g) ≅
    (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z) ⋙
      SheafOfModules.RingedSiteCup.globalSections (zariskiCorner Z.left model)) ⋙
        ModuleCat.restrictScalars scalar
  ordinary_sections : ∀ (M : (schemeSpace Z).SmallModules)
    (s : (affineScalarSections A Y e (schemeSpace Z) (schemeMap g)).obj M)
    (U : Z.left.Opens),
    (ordinary.hom.app M s).val.app (op U) (1 : Z.left.presheaf.obj (op U)) =
      ((schemeRestriction (schemeSpace Z) (affineIdentityChart Z)).map
        (fullModuleSection (schemeSpace Z) M s)).val.app (op U)
        ((schemeOpensRingHom (schemeSpace Z) (affineIdentityChart Z)).app (op U) 1)
  derived : affineDerivedSections A Y e (schemeSpace Z) (schemeMap g) ≅
    (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).rightDerivedFunctor ⋙
      SheafOfModules.RingedSiteCup.derivedGlobalSections (zariskiCorner Z.left model) ⋙
        RingDerivedScalarExtension.moduleDerivedRestriction scalar
  [ordinary_additive : (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z) ⋙
      SheafOfModules.RingedSiteCup.globalSections (zariskiCorner Z.left model) ⋙
        ModuleCat.restrictScalars scalar).Additive]
  on_complexes : ∀ P : CochainComplex (schemeSpace Z).SmallModules ℤ,
    affineSectionsComplexUnit A Y e (schemeSpace Z) (schemeMap g) P ≫
        derived.hom.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso ordinary.symm (.up ℤ)).inv.app P) ≫
      (ModuleCat.restrictScalars scalar).mapDerivedCategoryFactors.inv.app _ ≫
      (RingDerivedScalarExtension.moduleDerivedRestriction scalar).map
        (DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z) ⋙
              SheafOfModules.RingedSiteCup.globalSections (zariskiCorner Z.left model)))
            (.up ℤ)).inv.app P)) ≫
      (RingDerivedScalarExtension.moduleDerivedRestriction scalar).map
        (spaceRightDerivedComplexUnit
          (SheafOfModules.RingedSiteCup.globalSections (zariskiCorner Z.left model))
          (((smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).mapHomologicalComplex
            (.up ℤ)).obj P)) ≫
      (RingDerivedScalarExtension.moduleDerivedRestriction scalar).map
        ((SheafOfModules.RingedSiteCup.derivedGlobalSections
          (zariskiCorner Z.left model)).map
          (spaceRightDerivedComplexUnit
            (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)) P))
  structure_ordinary : SheafOfModules.unit (moduleRings Z.left.toRingedSpace) ⟶
    (smallSchemeRestriction (schemeSpace Z) (affineIdentityChart Z)).obj
      (SheafOfModules.unit (schemeSpace Z).smallStructureRings)
  structure_sections : ∀ (U : Z.left.Opens) (a : Z.left.presheaf.obj (op U)),
    structure_ordinary.val.app (op U) a =
      ((schemeRestriction (schemeSpace Z) (affineIdentityChart Z)).map
        (fullModuleSection (schemeSpace Z)
          (SheafOfModules.unit (schemeSpace Z).smallStructureRings) (𝟙 _))).val.app (op U)
        ((schemeOpensRingHom (schemeSpace Z) (affineIdentityChart Z)).app (op U) a)
  structure_iso : IsIso (zariskiDerivedStructureInsertion Z structure_ordinary)

/-- The actual Zariski scalar cup: ordinary ringed-site derived cup, then restriction of scalars.
Source: Stacks 0FPJ, 0B6C (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def ZariskiComparison.multiplication {A : Type u} [CommRing A] {Y Z : Over S}
    {e : Y.left ≅ Spec (.of A)} {g : Z ⟶ Y} (d : ZariskiComparison A Y Z e g) :
    (RingDerivedScalarExtension.moduleDerivedRestriction d.scalar).obj
        ((SheafOfModules.RingedSiteCup.derivedGlobalSections
          (zariskiCorner Z.left d.model)).obj
          (ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z.left) Z.left.sheaf)) ⊗
    (RingDerivedScalarExtension.moduleDerivedRestriction d.scalar).obj
        ((SheafOfModules.RingedSiteCup.derivedGlobalSections
          (zariskiCorner Z.left d.model)).obj
          (ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z.left) Z.left.sheaf)) ⟶
    (RingDerivedScalarExtension.moduleDerivedRestriction d.scalar).obj
        ((SheafOfModules.RingedSiteCup.derivedGlobalSections
          (zariskiCorner Z.left d.model)).obj
          (ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z.left) Z.left.sheaf)) :=
  restrictionTensor d.scalar d.scalar_tensor _ _ ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction d.scalar).map
      (SheafOfModules.RingedSiteCup.global (zariskiCorner Z.left d.model) d.tensor _ _ ≫
        (SheafOfModules.RingedSiteCup.derivedGlobalSections (zariskiCorner Z.left d.model)).map
          (zariskiStructureMul Z.left d.model))

/-- The canonical étale–Zariski derived comparison on scalar global sections of O.
Source: Stacks 071Q (blueprint: def-sfb-flat-space-derived-external-cup-maps). -/
def ZariskiComparison.comparison {A : Type u} [CommRing A] {Y Z : Over S}
    {e : Y.left ≅ Spec (.of A)} {g : Z ⟶ Y} (d : ZariskiComparison A Y Z e g) :
    sections A Y e (schemeSpace Z) (schemeMap g) ⟶
      (RingDerivedScalarExtension.moduleDerivedRestriction d.scalar).obj
        ((SheafOfModules.RingedSiteCup.derivedGlobalSections
          (zariskiCorner Z.left d.model)).obj
          (ringedSiteDualityUnit.{u, u, u, u} (Opens.grothendieckTopology Z.left) Z.left.sheaf)) :=
  d.derived.hom.app (schemeSpace Z).derivedStructure ≫
    (RingDerivedScalarExtension.moduleDerivedRestriction d.scalar).map
      ((SheafOfModules.RingedSiteCup.derivedGlobalSections (zariskiCorner Z.left d.model)).map
        (@inv _ _ _ _ (zariskiDerivedStructureInsertion Z d.structure_ordinary) d.structure_iso))

end FlatExternalCup
end AlgebraicGeometry.AlgebraicSpace
