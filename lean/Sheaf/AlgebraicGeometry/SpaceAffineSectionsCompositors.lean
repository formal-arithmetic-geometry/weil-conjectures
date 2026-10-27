module

public import Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Normalized global-section compositors

Source: Stacks 0B6C, 079V and 071Q
(blueprint: def-sfb-space-affine-sections-compositors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction identifies the structure modules sectionwise.
Source: Stacks 039Z (blueprint: def-sfb-space-affine-sections-compositors).
Proof: the map is induced by the identity map of regular-function presheaves; each
component is the identity linear map and hence invertible. -/
@[instance] theorem smallModuleUnit_isIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      (F := X.smallEtaleInclusion) (R := X.structureSheaf)
      (S := X.smallStructureRings) ⟨𝟙 _⟩) := by
  sorry

/-- The literal restriction comparison of the two structure modules.
Source: Stacks 039Z (blueprint: def-sfb-space-affine-sections-compositors). -/
def smallModuleUnitIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SheafOfModules.unit X.smallStructureRings ≅
      X.smallModuleRestriction.obj (SheafOfModules.unit X.structureSheaf) :=
  asIso (SheafOfModules.unitToPushforwardObjUnit
    (F := X.smallEtaleInclusion) (R := X.structureSheaf)
    (S := X.smallStructureRings) ⟨𝟙 _⟩)

/-- Extend a compatible section from the small affine model to all scheme charts.
Source: Stacks 039Z (blueprint: def-sfb-space-affine-sections-compositors). -/
def fullModuleSection {S : Scheme.{u}} (X : AlgebraicSpace S) (M : X.SmallModules)
    (s : SheafOfModules.unit X.smallStructureRings ⟶ M) :
    SheafOfModules.unit X.structureSheaf ⟶ X.smallModuleEquivalence.inverse.obj M :=
  X.smallModuleEquivalence.unitIso.hom.app _ ≫
    X.smallModuleEquivalence.inverse.map ((smallModuleUnitIso X).inv ≫ s)

section
variable {S : Scheme.{u}} (A : Type u) [CommRing A]
  (Y : Over S) (e : Y.left ≅ Spec (.of A))
  (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)

/-- The global-section compositor is fixed on every compatible-chart projection.
Source: Stacks 03G8, 0B6C (blueprint: def-sfb-space-affine-sections-compositors). -/
def AffineSectionsCompositionNormalization
    (c : affineScalarSections A Y e X f ≅
      smallModuleDirectImage f ⋙ affineScalarSections A Y e (schemeSpace Y) (𝟙 _)) : Prop :=
  ∀ (M : X.SmallModules) (s : (affineScalarSections A Y e X f).obj M)
    (V : (schemeSpace Y).EtaleSite) (q : ModuleChart f V)
    (b : (schemeSpace Y).structureSheaf.obj.obj (op V)),
    ((moduleDirectImageModel f).projection
      (X.smallModuleEquivalence.inverse.obj M) V).app (op q)
      (((schemeSpace Y).smallModuleEquivalence.unitIso.inv.app _).val.app (op V)
        ((fullModuleSection (schemeSpace Y) _ ((c.hom.app M) s)).val.app (op V) b)) =
    (fullModuleSection X M s).val.app (op q.left) (moduleChartScalar f V q b)

/-- Unique compatible-section compositor.
Source: Stacks 03G8, 039Z (blueprint: def-sfb-space-affine-sections-compositors).
Proof: a global section is a compatible family on every scheme chart. For a target
chart V restrict that family to the charts of X times_Y V, multiplying by the
pulled-back coefficient b. The limit property of moduleDirectImageModel gives the
unique section on V. These sections commute with restrictions and module maps.
Conversely their projections recover the original family by descent. The two
operations are inverse and A-linear; projection uniqueness proves uniqueness. -/
theorem affineSectionsComposition_existsUnique :
    ∃! c, AffineSectionsCompositionNormalization A Y e X f c := by
  sorry

/-- The compositor specified by its actual action on compatible sections.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineSectionsComposition :=
  Classical.choose (affineSectionsComposition_existsUnique A Y e X f)

variable [HasDerivedCategory.{w} X.SmallModules]
  [HasDerivedCategory.{w} (schemeSpace Y).SmallModules]

/-- The K-injective derived comparison on cochain complexes.
Source: Stacks 070K (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineSectionsComplexUnit (P : CochainComplex X.SmallModules ℤ) :=
  derivedPushforwardComplexComparison
    (affineScalarSections A Y e X f)
    (affineDerivedSections A Y e X f)
    (affineScalarSections A Y e X f).rightDerivedFunctorUnit P

/-- The same unit for canonical derived direct image.
Source: Stacks 079V (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineDirectImageComplexUnit (P : CochainComplex X.SmallModules ℤ) :=
  derivedPushforwardComplexComparison
    (smallModuleDirectImage f)
    (derivedDirectImage f) (smallModuleDirectImage f).rightDerivedFunctorUnit P

/-- Derived composition is normalized by the actual ordinary compositor and derived units.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-sections-compositors). -/
def AffineDerivedSectionsCompositionNormalization
    (c : affineDerivedSections A Y e X f ≅
      derivedDirectImage f ⋙ affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)) : Prop :=
  ∀ P : CochainComplex X.SmallModules ℤ,
    affineSectionsComplexUnit A Y e X f P ≫ c.hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map
      (((affineSectionsComposition A Y e X f).hom.mapHomologicalComplex (.up ℤ)).app P) ≫
      affineSectionsComplexUnit A Y e (schemeSpace Y) (𝟙 _)
        (((smallModuleDirectImage f).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).map
        (affineDirectImageComplexUnit Y X f P)

/-- Derived global sections commute with direct image, with the universal normalization.
Source: Stacks 0B6C, 079V (blueprint: def-sfb-space-affine-sections-compositors).
Proof: injective module sheaves are acyclic for global sections and direct image;
more generally direct images of K-injective resolutions are global-section acyclic.
The ordinary compatible-section compositor therefore computes the composite on
K-injective resolutions. Universal right derivation descends this isomorphism and
gives the displayed unit equation. Its universal property proves uniqueness. -/
theorem affineDerivedSectionsComposition_existsUnique :
    ∃! c, AffineDerivedSectionsCompositionNormalization A Y e X f c := by
  sorry

/-- The normalized derived global-section compositor.
Source: Stacks 0B6C (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineDerivedSectionsComposition :=
  Classical.choose (affineDerivedSectionsComposition_existsUnique A Y e X f)

/-- Insertion of the coefficient as its scalar multiplication on the structure module.
Source: Stacks 071Q (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineStructureScalar : ModuleCat.of A A ⟶
    (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).obj
      (SheafOfModules.unit (schemeSpace Y).smallStructureRings) :=
  let M := (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)).obj
    (SheafOfModules.unit (schemeSpace Y).smallStructureRings)
  ModuleCat.ofHom (X := ModuleCat.of A A) (Y := M) (LinearMap.toSpanSingleton A M (𝟙 _))


/-- On an affine scheme, scalar multiplication identifies all regular-function sections.
Source: Stacks 071Q (blueprint: def-sfb-space-affine-sections-compositors).
Proof: the Gamma-Spec isomorphism identifies global functions with A. A module map
from O to O is multiplication by its value on one, so the displayed map is bijective
and linear, hence an isomorphism of A-modules. -/
@[instance] theorem affineStructureScalar_isIso :
    IsIso (affineStructureScalar A Y e) := by
  sorry

/-- The ordinary scalar insertion followed by the universal derived-sections unit.
Source: Stacks 071Q (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineStructureDerivedInsertion :
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).obj
        (schemeSpace Y).derivedStructure :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.app _) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).map (affineStructureScalar A Y e)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (affineScalarSections A Y e (schemeSpace Y) (𝟙 _)) (.up ℤ) 0).inv.app _) ≫
    affineSectionsComplexUnit A Y e (schemeSpace Y) (𝟙 _)
      ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
        (SheafOfModules.unit (schemeSpace Y).smallStructureRings)) ≫
    (affineDerivedSections A Y e (schemeSpace Y) (𝟙 _)).map
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app _)

/-- Affine acyclicity makes the specified insertion invertible in every degree.
Source: Stacks 071Q, 03P2 (blueprint: def-sfb-space-affine-sections-compositors).
Proof: degree zero is the preceding scalar isomorphism; positive cohomology vanishes
by affine quasi-coherent acyclicity on the small etale site, and negative cohomology
vanishes since the input is in degree zero. The derived unit is the ordinary
insertion on degree zero. A cohomology isomorphism in all degrees is invertible. -/
@[instance] theorem affineStructureDerivedInsertion_isIso :
    IsIso (affineStructureDerivedInsertion A Y e) := by
  sorry

/-- The canonical affine identification RΓ(Y,O_Y)=A[0].
Source: Stacks 071Q (blueprint: def-sfb-space-affine-sections-compositors). -/
def affineStructureDerivedIso := (asIso (affineStructureDerivedInsertion A Y e)).symm

end
end AlgebraicGeometry.AlgebraicSpace

