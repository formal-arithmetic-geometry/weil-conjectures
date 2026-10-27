module

public import Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.AlgebraicGeometry.MarkedSplitModuleDeformations

/-! # Split deformation coefficients on an algebraic space

Source: Stacks Project, defos.tex, Tag 0D17, split conormal coefficient;
Modules on Sites, Tag 03EK (blueprint: def-sfb-space-split-coefficient).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.AlgebraicSpace.SplitSpace

variable {K : Type u} [Field K] (X : AlgebraicSpace (Spec (.of K)))

/-- The actual field action on the regular functions of an affine chart.
Source: Stacks 0D17 (blueprint: def-sfb-space-split-coefficient). -/
def fieldMap (U : X.SmallEtaleModelᵒᵖ) : K →+* X.smallStructureSheaf.obj.obj U :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫
    Scheme.Γ.map ((X.smallEtaleInclusion.obj U.unop).obj.left.hom).op).hom

variable (M : ModuleCat.{u} K)

/-- The sectionwise tensor O(U) tensor_K M with its O(U)-module structure.
Source: Stacks 0D17, 03EK (blueprint: def-sfb-space-split-coefficient). -/
abbrev coefficientTerm (U : X.SmallEtaleModelᵒᵖ) :=
  (ModuleCat.extendScalars (fieldMap X U)).obj M

/-- Restriction of tensors is uniquely determined on pure tensors.
Source: Stacks 03EK (blueprint: def-sfb-space-split-coefficient).
Proof: naturality of the chart structure map makes restriction K-linear. The
balanced tensor universal property gives s tensor m mapping to res(s) tensor m.
It is semilinear over restriction of O. Pure tensors generate, proving uniqueness. -/
theorem coefficientRestriction_existsUnique {U V : X.SmallEtaleModelᵒᵖ} (f : U ⟶ V) :
    ∃! r : coefficientTerm X M U ⟶
        (ModuleCat.restrictScalars (X.smallStructureRings.obj.map f).hom).obj
          (coefficientTerm X M V),
      ∀ (s : X.smallStructureSheaf.obj.obj U) (m : M),
        r (s ⊗ₜ[K, fieldMap X U] m) =
          X.smallStructureSheaf.obj.map f s ⊗ₜ[K, fieldMap X V] m := by
  sorry

/-- The tensor restriction, selected by its unique generator formula.
Source: Stacks 03EK (blueprint: def-sfb-space-split-coefficient). -/
def coefficientRestriction {U V : X.SmallEtaleModelᵒᵖ} (f : U ⟶ V) :=
  (coefficientRestriction_existsUnique X M f).choose

/-- Tensor restriction obeys the presheaf laws.
Source: Stacks 03EK (blueprint: def-sfb-space-split-coefficient).
Proof: on s tensor m the identity restricts s identically; successive restrictions
compose by the regular-functions presheaf law. Tensor generation gives both equations. -/
theorem coefficientRestriction_laws :
    (∀ U : X.SmallEtaleModelᵒᵖ, coefficientRestriction X M (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.smallStructureRings.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (X.smallStructureRings.obj.map_id U))).inv.app _) ∧
    (∀ (U V W : X.SmallEtaleModelᵒᵖ) (f : U ⟶ V) (g : V ⟶ W),
      coefficientRestriction X M (f ≫ g) = coefficientRestriction X M f ≫
        (ModuleCat.restrictScalars (X.smallStructureRings.obj.map f).hom).map
          (coefficientRestriction X M g) ≫
        (ModuleCat.restrictScalarsComp' (X.smallStructureRings.obj.map f).hom
          (X.smallStructureRings.obj.map g).hom (X.smallStructureRings.obj.map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom (X.smallStructureRings.obj.map_comp f g))).inv.app _) := by
  sorry

/-- The actual sectionwise tensor presheaf, before sheafification.
Source: Stacks 0D17, 03EK (blueprint: def-sfb-space-split-coefficient). -/
def coefficientPresheaf : PresheafOfModules.{u} X.smallStructureRings.obj where
  obj := coefficientTerm X M
  map := coefficientRestriction X M
  map_id := (coefficientRestriction_laws X M).1
  map_comp := (coefficientRestriction_laws X M).2 _ _ _

/-- The coefficient O_X tensor_K M is the sheafification of its tensor presheaf.
Source: Stacks 0D17, 03EK (blueprint: def-sfb-space-split-coefficient). -/
def coefficient : X.SmallModules :=
  (PresheafOfModules.sheafification (R := X.smallStructureRings) (𝟙 _)).obj
    (coefficientPresheaf X M)

/-- Coefficient maps on section tensors commute with restriction.
Source: Stacks 03EK (blueprint: def-sfb-space-split-coefficient).
Proof: both composites send s tensor m to res(s) tensor h(m); tensor generation
proves equality. This also covers zero and noninjective h. -/
theorem coefficientMap_naturality {M N : ModuleCat.{u} K} (h : M ⟶ N)
    {U V : X.SmallEtaleModelᵒᵖ} (f : U ⟶ V) :
    coefficientRestriction X M f ≫
        (ModuleCat.restrictScalars (X.smallStructureRings.obj.map f).hom).map
          ((ModuleCat.extendScalars (fieldMap X V)).map h) =
      (ModuleCat.extendScalars (fieldMap X U)).map h ≫ coefficientRestriction X N f := by
  sorry

/-- The canonical coefficient map, sheafifying 1 tensor h.
Source: Stacks 0D17, 03EK (blueprint: def-sfb-space-split-coefficient). -/
def coefficientMap {M N : ModuleCat.{u} K} (h : M ⟶ N) :
    coefficient X M ⟶ coefficient X N :=
  (PresheafOfModules.sheafification (R := X.smallStructureRings) (𝟙 _)).map
    { app := fun U ↦ (ModuleCat.extendScalars (fieldMap X U)).map h
      naturality := coefficientMap_naturality X h }

variable [HasDerivedCategory.{w} X.SmallModules]

/-- The structure morphism to Spec K, represented by its actual sheaf map.
Source: Stacks 0D17 (blueprint: def-sfb-space-split-coefficient). -/
def structureMap : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (.of K)))) :=
  ObjectProperty.homMk (SplitModule.baseMap X)

/-- Ext with the naive cotangent complex and the specified degree-zero coefficient.
Source: Stacks 0D17 (blueprint: def-sfb-space-split-coefficient). -/
abbrev Ext (n : ℤ) :=
  derivedExt X (naiveCotangent (structureMap X)) (cotangentCoefficient X (coefficient X M)) n

/-- Coefficient functoriality on Ext is postcomposition with the shifted map.
Source: Stacks 0GQ8 (blueprint: def-sfb-space-split-coefficient). -/
def extMap {M N : ModuleCat.{u} K} (h : M ⟶ N) (n : ℤ) (e : Ext X M n) : Ext X N n :=
  e ≫ (shiftFunctor X.DerivedModules n).map
    ((DerivedCategory.singleFunctor X.SmallModules 0).map (coefficientMap X h))

end AlgebraicGeometry.AlgebraicSpace.SplitSpace
