/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CondensedCoefficientComparisons
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Sheaf.CategoryTheory.DerivedExactSquareComposition
import all Sheaf.Paper.ProperIntegralRationalScalarComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import Sheaf.AlgebraicGeometry.OpenCoefficientSquareActionIdentification
import Sheaf.Paper.ConstructibleCokernelsExtensions
import Sheaf.Paper.CondensedOpenRestrictedCounit
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

import all Sheaf.CategoryTheory.CompactSupportIdentityCalculus

/-! # Condensed compact-support projection constructions

Source: blueprint sk-thm-purity-transport, Steps 2--3; the compact-support
realization prerequisite, proof Steps 6--17 (agent-formulated constructions).
(blueprint: def-pur-condensed-compact-support-projection-core). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

/-- The existing Abelian structure of the fixed pro-etale sheaf category.
Source: CategoryTheory.sheafIsAbelian, with its original sheafification adjunction.
(blueprint: def-pur-condensed-compact-support-projection). -/
@[instance_reducible]
def fieldSheafAbelian (X : Scheme.{u}) :
    Abelian (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  sheafIsAbelian

attribute [local instance] fieldSheafAbelian

/-- The small colimits used by the fixed pro-etale sheaf category.
Source: the existing sheaf colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  ⟨fun _ _ ↦ Sheaf.instHasColimitsOfShape⟩

attribute [local instance] fieldSheafColimits

/-- The existing Grothendieck abelian property of the fixed pro-etale sheaf category.
Source: the Grothendieck abelian sheaf instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafGrothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  infer_instance

attribute [local instance] fieldSheafGrothendieck

/-- The large colimits used by the fixed pro-etale sheaf category.
Source: the existing Grothendieck abelian sheaf instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafBigColimits (X : Scheme.{u}) :
    HasColimitsOfSize.{u + 1, u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  IsGrothendieckAbelian.hasColimits _

attribute [local instance] fieldSheafBigColimits

/-- The coequalizers used by the fixed pro-etale sheaf category.
Source: the existing sheaf colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafCoequalizers (X : Scheme.{u}) :
    HasCoequalizers (Sheaf (ProEt.topology X) Ab.{u + 1}) :=
  Sheaf.instHasColimitsOfShape

attribute [local instance] fieldSheafCoequalizers

/-- Additivity of the fixed sheaf tensor product.
Source: the existing monoidal preadditive sheaf instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  infer_instance

attribute [local instance] fieldSheafMonoidalPreadditive

/-- The existing Abelian module structure with its fixed sheaf category named.
Source: Mod.instAbelian; its constructor and all selected data are unchanged.
(blueprint: def-pur-condensed-compact-support-projection). -/
@[instance_reducible]
def fieldModuleAbelian (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    Abelian (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  inferInstance

attribute [local instance] fieldModuleAbelian

/-- Internal modules over a monoid in this sheaf category are Grothendieck abelian.
Source: Mod.isGrothendieckAbelian; tensoring in the base preserves colimits.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleGrothendieck (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    IsGrothendieckAbelian.{u + 1}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  Mod.isGrothendieckAbelian.{u + 1} R

attribute [local instance] fieldModuleGrothendieck

/-- Internal modules admit the existing K-injective resolutions of a Grothendieck category.
Source: the Grothendieck abelian K-injective-resolution instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleKInjectiveResolutions (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    CategoryTheory.Abelian.HasKInjectiveResolutions
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleKInjectiveResolutions

/-- The existing derived category of internal modules, with the sheaf site fixed.
Source: HasDerivedCategory.ofIsGrothendieckAbelian. This names exactly its
K-injective-resolution construction, with the original universe of morphisms.
(blueprint: def-pur-condensed-compact-support-projection). -/
@[instance_reducible]
def fieldModuleDerivedCategory (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasDerivedCategory.{u + 1} (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance] fieldModuleDerivedCategory

/-- The existing small colimits of internal modules on the fixed sheaf site.
Source: module-object colimits are created by the forgetful functor.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfSize.{0, 0} (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  ⟨fun _ _ ↦ inferInstance⟩

attribute [local instance] fieldModuleColimits

/-- The existing large colimits of internal modules on the fixed sheaf site.
Source: the Grothendieck abelian module property.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleBigColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) :=
  IsGrothendieckAbelian.hasColimits _

attribute [local instance] fieldModuleBigColimits

/-- The existing functorial flat resolutions on the fixed pro-etale sheaf category.
Source: ProEtale.hasFunctorialFlatResolution_sheaf.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldSheafFlatResolution (X : Scheme.{u}) :
    CategoryTheory.Abelian.HasFunctorialFlatResolution
      (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  infer_instance

attribute [local instance] fieldSheafFlatResolution

/-- The existing functorial flat resolutions of internal modules over a condensed ring.
Source: the existing module-object functorial flat-resolution instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleFlatResolution (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    CategoryTheory.Abelian.HasFunctorialFlatResolution
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleFlatResolution

/-- The countable coproducts used by the module K-flat derivability structure.
Source: the existing internal-module colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleCountableCoproducts (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasCountableCoproducts (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleCountableCoproducts

/-- The integer colimits used by module K-flat derivation.
Source: the existing internal-module colimit instance.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleIntegerColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    HasColimitsOfShape ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleIntegerColimits

/-- Exactness of the integer colimits used by module K-flat derivation.
Source: the existing exact-colimit instance for Grothendieck module categories.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldModuleIntegerExactColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    HasExactColimitsOfShape ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R) := by
  infer_instance

attribute [local instance] fieldModuleIntegerExactColimits

/-- Left tensor preserves the integer colimits used by K-flat derivation.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldTensorColimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := by
  intro M
  infer_instance

attribute [local instance] fieldTensorColimits

/-- Right tensor preserves the integer colimits used by K-flat derivation.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldTensorColimitsRight (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    ∀ M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) := by
  intro M
  infer_instance

attribute [local instance] fieldTensorColimitsRight

-- Cache the graded tensor colimit instances used by each K-flat derived functor.
/-- The existing tensor has every graded binary coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedTensor (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    A.HasTensor B := by
  intro n
  infer_instance

attribute [local instance] fieldGradedTensor

/-- Left tensor preserves the graded triple coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedFour (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B C D : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    GradedObject.HasTensor₄ObjExt A B C D := by
  intro i j
  infer_instance

attribute [local instance] fieldGradedFour

/-- Right tensor preserves the graded binary coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedLeft (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensor₁₂Tensor A B C := by
  intro i j
  infer_instance

attribute [local instance] fieldGradedLeft

/-- Left tensor preserves the graded binary coproduct.
Source: the existing sheaf-module tensor colimit instances.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldGradedRight (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A B C : GradedObject ℤ (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) R)) :
    GradedObject.HasGoodTensorTensor₂₃ A B C := by
  intro i j
  infer_instance

attribute [local instance] fieldGradedRight

/-- Scalar extension has the existing K-flat quasi-isomorphism preservation property.
Source: Mod.preservesKFlatQuasiIso, proved by tensoring a K-flat acyclic cone.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldExtendScalarsKFlat (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] :
    (Mod.extendScalars φ).PreservesKFlatQuasiIso := by
  infer_instance

attribute [local instance] fieldExtendScalarsKFlat



namespace WeilConjectures.CompactSupportCondensedRealization

universe a av b bv d dv e ev h hv z zv

/-- Pasting the proper coefficient mate with the open coefficient square.
Source: blueprint proof Step 6; archived ChangeOfCoefficients.lean
(blueprint: def-pur-condensed-compact-support-projection). -/
def pasteScalar {C : Type a} {D : Type b} {H : Type d}
    {C' : Type e} {D' : Type h} {H' : Type z}
    [Category.{av} C] [Category.{bv} D] [Category.{dv} H]
    [Category.{ev} C'] [Category.{hv} D'] [Category.{zv} H']
    (j : C ⥤ D) (r : D ⥤ H) (j' : C' ⥤ D') (r' : D' ⥤ H')
    (tx : C ⥤ C') (tz : D ⥤ D') (ty : H ⥤ H')
    (p : r ⋙ ty ⟶ tz ⋙ r') (q : j ⋙ tz ⟶ tx ⋙ j') :
    (j ⋙ r) ⋙ ty ⟶ tx ⋙ (j' ⋙ r') :=
  (Functor.associator j r ty).hom ≫ Functor.whiskerLeft j p ≫
    (Functor.associator j tz r').inv ≫ Functor.whiskerRight q r' ≫
      (Functor.associator tx j' r').hom

private theorem pasteScalar_identity
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) (R : D ⥤ E) (X : C ⥤ C) (Z : D ⥤ D) (Y : E ⥤ E)
    (x : X ≅ 𝟭 C) (z : Z ≅ 𝟭 D) (y : Y ≅ 𝟭 E)
    (p : R ⋙ Y ⟶ Z ⋙ R) (o : J ⋙ Z ⟶ X ⋙ J)
    (hp : ∀ M, p.app M ≫ R.map (z.hom.app M) = y.hom.app (R.obj M))
    (ho : ∀ K, o.app K ≫ J.map (x.hom.app K) = z.hom.app (J.obj K)) (K : C) :
    (pasteScalar J R J R X Z Y p o).app K ≫
        (J ⋙ R).map (x.hom.app K) = y.hom.app ((J ⋙ R).obj K) := by
  simp only [pasteScalar, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Functor.comp_map]
  rw [Category.assoc, ← R.map_comp, ho, hp]
  rfl

private theorem pasteScalar_shift
    {C D H C' D' H' : Type*}
    [Category C] [Category D] [Category H] [Category C'] [Category D'] [Category H']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift H ℤ]
    [HasShift C' ℤ] [HasShift D' ℤ] [HasShift H' ℤ]
    (j : C ⥤ D) (r : D ⥤ H) (j' : C' ⥤ D') (r' : D' ⥤ H')
    (tx : C ⥤ C') (tz : D ⥤ D') (ty : H ⥤ H')
    [j.CommShift ℤ] [r.CommShift ℤ] [j'.CommShift ℤ] [r'.CommShift ℤ]
    [tx.CommShift ℤ] [tz.CommShift ℤ] [ty.CommShift ℤ]
    (p : r ⋙ ty ⟶ tz ⋙ r') (q : j ⋙ tz ⟶ tx ⋙ j')
    [NatTrans.CommShift p ℤ] [NatTrans.CommShift q ℤ] :
    NatTrans.CommShift (pasteScalar j r j' r' tx tz ty p q) ℤ := by
  dsimp only [pasteScalar]
  infer_instance

/-- Shorthand for the existing sectionwise finite-limit preservation instances.
Source: blueprint proof Steps 6 and 13; archived coefficient-change hypotheses
(blueprint: def-pur-condensed-compact-support-projection). -/
abbrev FlatCoefficientMap
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] : Prop :=
  ∀ W : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a W))

section CoefficientCompositionHelpers
set_option backward.defeqAttrib.useBackward false
private theorem pasteScalar_comp
    {C₀ D₀ E₀ C₁ D₁ E₁ C₂ D₂ E₂ : Type*}
    [Category C₀] [Category D₀] [Category E₀]
    [Category C₁] [Category D₁] [Category E₁]
    [Category C₂] [Category D₂] [Category E₂]
    (J₀ : C₀ ⥤ D₀) (R₀ : D₀ ⥤ E₀)
    (J₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ E₁)
    (J₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ E₂)
    (X₁ : C₀ ⥤ C₁) (Z₁ : D₀ ⥤ D₁) (Y₁ : E₀ ⥤ E₁)
    (X₂ : C₁ ⥤ C₂) (Z₂ : D₁ ⥤ D₂) (Y₂ : E₁ ⥤ E₂)
    (X : C₀ ⥤ C₂) (Z : D₀ ⥤ D₂) (Y : E₀ ⥤ E₂)
    (cx : X₁ ⋙ X₂ ⟶ X) (cz : Z₁ ⋙ Z₂ ⟶ Z) (cy : Y₁ ⋙ Y₂ ⟶ Y)
    (p₁ : R₀ ⋙ Y₁ ⟶ Z₁ ⋙ R₁) (p₂ : R₁ ⋙ Y₂ ⟶ Z₂ ⋙ R₂)
    (p : R₀ ⋙ Y ⟶ Z ⋙ R₂)
    (q₁ : J₀ ⋙ Z₁ ⟶ X₁ ⋙ J₁) (q₂ : J₁ ⋙ Z₂ ⟶ X₂ ⋙ J₂)
    (q : J₀ ⋙ Z ⟶ X ⋙ J₂)
    (hp : ∀ M, Y₂.map (p₁.app M) ≫ p₂.app (Z₁.obj M) ≫
      R₂.map (cz.app M) = cy.app (R₀.obj M) ≫ p.app M)
    (hq : ∀ K, Z₂.map (q₁.app K) ≫ q₂.app (X₁.obj K) ≫
      J₂.map (cx.app K) = cz.app (J₀.obj K) ≫ q.app K) (K : C₀) :
    Y₂.map ((pasteScalar J₀ R₀ J₁ R₁ X₁ Z₁ Y₁ p₁ q₁).app K) ≫
      (pasteScalar J₁ R₁ J₂ R₂ X₂ Z₂ Y₂ p₂ q₂).app (X₁.obj K) ≫
      (J₂ ⋙ R₂).map (cx.app K) =
    cy.app ((J₀ ⋙ R₀).obj K) ≫
      (pasteScalar J₀ R₀ J₂ R₂ X Z Y p q).app K := by
  simp only [pasteScalar, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% (p₂.naturality (q₁.app K))]
  rw [← R₂.map_comp, ← R₂.map_comp, hq, R₂.map_comp]
  rw [reassoc_of% (hp (J₀.obj K))]
  rfl

end CoefficientCompositionHelpers

section Projection
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [FlatCoefficientMap a]

/-- The actual small-Hom-universe derived extension of condensed coefficients.
Source: blueprint proof Steps 6 and 13
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalar (W : Scheme.{u}) :
    DerivedCategory
        (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)) ⥤
      DerivedCategory
        (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ' W)) :=
  (Mod.extendScalars (coefficientMap a W)).leftDerivedFunctor

/-- The original scalar/restriction adjunction with its canonical scalar functors named.
Source: the existing derived extension/restriction adjunction; blueprint Step 17.
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarAdjunction (W : Scheme.{u}) :
    condensedScalar a W ⊣ (Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap a W)).mapDerivedCategory :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a W)

attribute [local irreducible] condensedScalarAdjunction condensedScalar

/-- The tensor shift is induced by the exact restriction-of-scalars adjunction.
Source: blueprint proof Step 17; the canonical derived tensor adjunction
(blueprint: def-pur-condensed-compact-support-projection). -/
instance condensedScalarShift (W : Scheme.{u}) : (condensedScalar a W).CommShift ℤ :=
  (condensedScalarAdjunction a W).leftAdjointCommShift ℤ

/-- The archived proper coefficient comparison with its canonical scalar functors named.
Source: CondensedRing.derivedPushHom, the proper adjunction mate.
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedPushScalar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙ condensedScalar a Y ⟶
      condensedScalar a X ⋙ (CondensedRing.lowerStar Λ' f).rightDerivedFunctor :=
  Adjunction.pushHomOfComapIso
    (condensedScalarAdjunction a X) (condensedScalarAdjunction a Y)
    (CondensedRing.derivedComapLowerStarIso a f)

/-- The archived open coefficient comparison with its canonical scalar functors named.
Source: CondensedRing.derivedOpenImmersionShriekIso, the open adjunction mate.
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedOpenScalar {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        condensedScalar a Z ≅
      condensedScalar a X ⋙
        (CondensedRing.openImmersionLowerShriek Λ' j).mapDerivedCategory :=
  (conjugateIsoEquiv
    ((condensedScalarAdjunction a X).comp
      (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
    ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (condensedScalarAdjunction a Z))).symm
    (CondensedRing.derivedComapUpperStarIso a j)

private theorem scalarPush_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    condensedPushScalar a f = Adjunction.pushHomOfComapIso
      (condensedScalarAdjunction a X) (condensedScalarAdjunction a Y)
      (CondensedRing.derivedComapLowerStarIso a f) := by
  unfold condensedPushScalar
  rfl

omit [FlatCoefficientMap a] in
private theorem scalarOpen_eq {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    condensedOpenScalar a j =
      (conjugateIsoEquiv
        ((condensedScalarAdjunction a X).comp
          (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
        ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
          (condensedScalarAdjunction a Z))).symm
        (CondensedRing.derivedComapUpperStarIso a j) := by
  unfold condensedOpenScalar
  rfl

omit [FlatCoefficientMap a] in
private theorem scalarOpen_conjugate {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] :
    conjugateEquiv
      ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
        (condensedScalarAdjunction a Z))
      ((condensedScalarAdjunction a X).comp
        (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j))
      (condensedOpenScalar a j).inv =
        (CondensedRing.derivedComapUpperStarIso a j).inv := by
  rw [scalarOpen_eq]
  exact inverse_conjugate_cancel _ _ _

attribute [local irreducible] condensedPushScalar condensedOpenScalar

/-- The canonical coefficient projection for a fixed compactification, in proper-then-open
order, exactly as in the archived condensed module-object construction.
Source: archived ChangeOfCoefficients.lean, derivedLowerShriekHom; blueprint proof Step 6
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
        (condensedScalar a Y) ⟶
      (condensedScalar a X) ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c :=
  pasteScalar
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a Y)
    (condensedPushScalar a c.g)
    (condensedOpenScalar a c.i).hom

/-- The inherited shift of the archived proper/open support composite.
Source: blueprint proof Step 17; archived derived open and proper operations
(blueprint: def-pur-condensed-compact-support-projection). -/
instance condensedSupportShift
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).CommShift ℤ :=
  inferInstance

/-- The original condensed scalar projection respects the canonical derived shifts.
Source: blueprint proof Step 17; derived adjunction shift compatibility
(blueprint: def-pur-condensed-compact-support-projection).
Proof: the ordinary tensor and open squares commute with cochain shifts. Their
universal derived units and counits fix the same shifted square. Taking the proper
adjunction mate preserves this equation, as does the open comparison and their paste.
The zero and addition shift coherences descend from those on cochain complexes. -/
theorem condensedProjection_commShift {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : NatTrans.CommShift (condensedProjection a c) ℤ := by
  have : (condensedScalarAdjunction a X).CommShift ℤ :=
    (condensedScalarAdjunction a X).commShift_of_rightAdjoint ℤ
  have : (condensedScalarAdjunction a Y).CommShift ℤ :=
    (condensedScalarAdjunction a Y).commShift_of_rightAdjoint ℤ
  have : (condensedScalarAdjunction a c.Z).CommShift ℤ :=
    (condensedScalarAdjunction a c.Z).commShift_of_rightAdjoint ℤ
  have := rightNatIso_shift (CondensedRing.comapLowerStarIso a c.g)
  have := rightExactIso_shift
    (Mod.comap (coefficientMap a c.Z) :
      Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1}) (condensedRingObj Λ' c.Z) ⥤
        Mod (Sheaf (ProEt.topology c.Z) Ab.{u + 1}) (condensedRingObj Λ c.Z))
  have := rightCompIso_shift (Mod.comap (coefficientMap a c.Z))
    (CondensedRing.lowerStar Λ c.g)
  have := rightCompExactIso_shift (CondensedRing.lowerStar Λ' c.g)
    (Mod.comap (coefficientMap a Y))
  have : NatTrans.CommShift (CondensedRing.derivedComapLowerStarIso a c.g).hom ℤ := by
    dsimp only [CondensedRing.derivedComapLowerStarIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have : NatTrans.CommShift (CondensedRing.derivedComapUpperStarIso a c.i).hom ℤ := by
    dsimp only [CondensedRing.derivedComapUpperStarIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have : (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      Λ c.i).CommShift ℤ := by
    dsimp only [CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction]
    infer_instance
  have : (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
      Λ' c.i).CommShift ℤ := by
    dsimp only [CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction]
    infer_instance
  have hp : NatTrans.CommShift (condensedPushScalar a c.g) ℤ := by
    rw [scalarPush_eq]
    exact scalarPush_shift
        (condensedScalarAdjunction a c.Z)
        (condensedScalarAdjunction a Y)
        (CondensedRing.derivedComapLowerStarIso a c.g)
  have ho : NatTrans.CommShift (condensedOpenScalar a c.i).hom ℤ := by
    rw [scalarOpen_eq]
    exact inverseConjugate_shift
        ((condensedScalarAdjunction a X).comp
          (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' c.i))
        ((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).comp
          (condensedScalarAdjunction a c.Z))
        (CondensedRing.derivedComapUpperStarIso a c.i)
  exact pasteScalar_shift
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a Y)
    (condensedPushScalar a c.g)
    (condensedOpenScalar a c.i).hom


variable {Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ''] [IsCommMonObj Λ''] (b : Λ' ⟶ Λ'') [IsMonHom b]
  [FlatCoefficientMap b]
  [FlatCoefficientMap (a ≫ b)]

/-- Tensor transitivity is uniquely induced by the actual restriction compositor.
Source: blueprint proof Steps 9 and 13; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarComp (W : Scheme.{u}) :
    condensedScalar a W ⋙ condensedScalar b W ≅ condensedScalar (a ≫ b) W :=
  ((condensedScalarAdjunction a W).comp
      (condensedScalarAdjunction b W)).leftAdjointUniq
    ((condensedScalarAdjunction (a ≫ b) W).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (coefficientMap_comp a b W) ≪≫ Mod.comapComp _ _) ≪≫
        Functor.mapDerivedCategoryCompIso
          _ _))

section CoefficientCompositionProof

set_option backward.defeqAttrib.useBackward false
set_option linter.unusedSectionVars false
private def coefficientRestrictionComp (W : Scheme.{u}) :
    Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap (a ≫ b) W) ≅
      Mod.comap (coefficientMap b W) ⋙ Mod.comap (coefficientMap a W) :=
  Mod.comapCongr (coefficientMap_comp a b W) ≪≫ Mod.comapComp _ _

private def derivedCoefficientRestrictionComp (W : Scheme.{u}) :
    (Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap (a ≫ b) W)).mapDerivedCategory ≅
    (Mod.comap (coefficientMap b W)).mapDerivedCategory ⋙
      (Mod.comap (coefficientMap a W)).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (coefficientRestrictionComp a b W) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem derivedRestrictionComp_symm (W : Scheme.{u}) :
    exact_comp _ _ _ (coefficientRestrictionComp a b W).symm =
      (derivedCoefficientRestrictionComp a b W).symm := by
  apply Iso.ext
  dsimp only [exact_comp]
  simp only [derivedCoefficientRestrictionComp, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm]



private theorem scalarComp_eq (W : Scheme.{u}) :
    condensedScalarComp a b W =
      ((condensedScalarAdjunction a W).comp (condensedScalarAdjunction b W)).leftAdjointUniq
        ((condensedScalarAdjunction (a ≫ b) W).ofNatIsoRight
          (derivedCoefficientRestrictionComp a b W)) := by
  unfold condensedScalarComp derivedCoefficientRestrictionComp coefficientRestrictionComp
  rfl


attribute [local instance] fieldTensorColimits fieldTensorColimitsRight
  fieldGradedTensor fieldGradedFour fieldGradedLeft fieldGradedRight
attribute [local irreducible]
  CondensedRing.derivedComapLowerStarIso Mod.derivedExtendMapDerivedCategoryAdjunction
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars condensedScalarComp condensedProjection

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  CondensedRing.openImmersionLowerShriek


private theorem scalarPush_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (condensedScalar b Y).map ((condensedPushScalar a f).app K) ≫
      (condensedPushScalar b f).app ((condensedScalar a X).obj K) ≫
      (CondensedRing.lowerStar Λ'' f).rightDerivedFunctor.map
        ((condensedScalarComp a b X).hom.app K) =
    (condensedScalarComp a b Y).hom.app
      ((CondensedRing.lowerStar Λ f).rightDerivedFunctor.obj K) ≫
      (condensedPushScalar (a ≫ b) f).app K := by
  simp only [scalarPush_eq, scalarComp_eq]
  let rx := derivedCoefficientRestrictionComp a b X
  let ry := derivedCoefficientRestrictionComp a b Y
  have hr (W : Scheme.{u}) : CondensedRing.restriction_comp a b W =
      (coefficientRestrictionComp a b W).symm := by
    apply Iso.ext
    rfl
  have hc := square_horizontal
    (CondensedRing.lowerStar Λ'' f) (CondensedRing.lowerStar Λ' f)
    (CondensedRing.lowerStar Λ f)
    (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap (a ≫ b) X))
    (Mod.comap (coefficientMap b Y)) (Mod.comap (coefficientMap a Y))
    (Mod.comap (coefficientMap (a ≫ b) Y))
    (CondensedRing.comapLowerStarIso b f) (CondensedRing.comapLowerStarIso a f)
    (CondensedRing.comapLowerStarIso (a ≫ b) f)
    (CondensedRing.restriction_comp a b X) (CondensedRing.restriction_comp a b Y)
    (CondensedRing.coefficient_square_comp a b f)
  dsimp only [derived_square] at *
  simp only [hr, derivedRestrictionComp_symm] at hc
  have hp := push_pasting_canonical
    (condensedScalarAdjunction a X)
    (condensedScalarAdjunction b X)
    (condensedScalarAdjunction (a ≫ b) X)
    (condensedScalarAdjunction a Y)
    (condensedScalarAdjunction b Y)
    (condensedScalarAdjunction (a ≫ b) Y)
    (CondensedRing.derivedComapLowerStarIso a f)
    (CondensedRing.derivedComapLowerStarIso b f)
    (CondensedRing.derivedComapLowerStarIso (a ≫ b) f) rx ry (by
      simpa only [CondensedRing.derivedComapLowerStarIso, Iso.symm_hom, rx, ry] using hc) K
  dsimp only [rx, ry] at hp
  exact hp.symm


attribute [local irreducible] CondensedRing.comapUpperStarIso
  CondensedRing.openCoefficientCollapse

private theorem coefficientRestrictionComp_inv_hom (W : Scheme.{u})
    (N : Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ'' W)) :
    ((coefficientRestrictionComp a b W).inv.app N).hom = 𝟙 N.X := by
  exact comapComposite_inv_hom (coefficientMap_comp a b W) N

private theorem openCoefficient_hom_normalization
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ' Z)) :
    ((CondensedRing.comapUpperStarIso a j).hom.app N).hom ≫
      ((CondensedRing.openCoefficientCollapse Λ j).hom.app
        ((Mod.comap (coefficientMap a Z)).obj N)).hom =
    ((CondensedRing.openCoefficientCollapse Λ' j).hom.app N).hom := by
  apply (cancel_epi ((CondensedRing.openCoefficientCollapse Λ' j).inv.app N).hom).1
  have hc := (CondensedRing.openCoefficientSquare_actions_components j a N).2.2.1
  have hi := congrArg Mod.Hom.hom
    ((CondensedRing.openCoefficientCollapse Λ' j).inv_hom_id_app N)
  change _ ≫ _ = 𝟙 _ at hi
  rw [hc, hi]
  rfl

private theorem coefficientUpperStar_comp {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (N : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ'' Z)) :
    (Mod.comap (coefficientMap a X)).map
        ((CondensedRing.comapUpperStarIso b j).hom.app N) ≫
      (CondensedRing.comapUpperStarIso a j).hom.app
        ((Mod.comap (coefficientMap b Z)).obj N) ≫
      (CondensedRing.upperStar Λ j).map
        ((coefficientRestrictionComp a b Z).inv.app N) =
    (coefficientRestrictionComp a b X).inv.app
        ((CondensedRing.upperStar Λ'' j).obj N) ≫
      (CondensedRing.comapUpperStarIso (a ≫ b) j).hom.app N := by
  apply Mod.hom_ext
  change ((CondensedRing.comapUpperStarIso b j).hom.app N).hom ≫
      ((CondensedRing.comapUpperStarIso a j).hom.app
        ((Mod.comap (coefficientMap b Z)).obj N)).hom ≫
      ((CondensedRing.upperStar Λ j).map
        ((coefficientRestrictionComp a b Z).inv.app N)).hom =
    ((coefficientRestrictionComp a b X).inv.app
      ((CondensedRing.upperStar Λ'' j).obj N)).hom ≫
      ((CondensedRing.comapUpperStarIso (a ≫ b) j).hom.app N).hom
  rw [coefficientRestrictionComp_inv_hom]
  refine Eq.trans ?_ (Category.id_comp _).symm
  apply (cancel_mono ((CondensedRing.openCoefficientCollapse Λ j).hom.app
      ((Mod.comap (coefficientMap (a ≫ b) Z)).obj N)).hom).1
  have hn := congrArg Mod.Hom.hom ((CondensedRing.openCoefficientCollapse Λ j).hom.naturality
    ((coefficientRestrictionComp a b Z).inv.app N))
  change ((CondensedRing.upperStar Λ j).map
      ((coefficientRestrictionComp a b Z).inv.app N)).hom ≫ _ =
    _ ≫ (ProEtale.upperStar Ab.{u + 1} j).map
      (((coefficientRestrictionComp a b Z).inv.app N).hom) at hn
  rw [coefficientRestrictionComp_inv_hom] at hn
  have hmap := (ProEtale.upperStar Ab.{u + 1} j).map_id N.X
  rw [hmap] at hn
  replace hn := hn.trans (Category.comp_id _)
  simp only [Category.assoc]
  rw [hn]
  have ha := openCoefficient_hom_normalization a j
    ((Mod.comap (coefficientMap b Z)).obj N)
  have hb := openCoefficient_hom_normalization b j N
  have hab := openCoefficient_hom_normalization (a ≫ b) j N
  dsimp only [Functor.comp_obj, Mod.comap] at ha hb hab ⊢
  exact (congrArg
    (fun h ↦ ((CondensedRing.comapUpperStarIso b j).hom.app N).hom ≫ h) ha).trans
      (hb.trans hab.symm)




attribute [local irreducible] CondensedRing.derivedComapUpperStarIso
 
  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction


private theorem derivedUpperStar_comp {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (N : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ'' Z))) :
    (CondensedRing.derivedComapUpperStarIso a j).inv.app
        ((Mod.comap (coefficientMap b Z)).mapDerivedCategory.obj N) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        ((CondensedRing.derivedComapUpperStarIso b j).inv.app N) ≫
      (derivedCoefficientRestrictionComp a b X).inv.app
        ((CondensedRing.upperStar Λ'' j).mapDerivedCategory.obj N) =
    (CondensedRing.upperStar Λ j).mapDerivedCategory.map
        ((derivedCoefficientRestrictionComp a b Z).inv.app N) ≫
      (CondensedRing.derivedComapUpperStarIso (a ≫ b) j).inv.app N := by
  have ho (M : Mod (Sheaf (ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ'' Z)) :
      (CondensedRing.comapUpperStarIso (a ≫ b) j).hom.app M ≫
        (CondensedRing.upperStar Λ j).map
          ((coefficientRestrictionComp a b Z).hom.app M) =
      (coefficientRestrictionComp a b X).hom.app
        ((CondensedRing.upperStar Λ'' j).obj M) ≫
        (Mod.comap (coefficientMap a X)).map
          ((CondensedRing.comapUpperStarIso b j).hom.app M) ≫
        (CondensedRing.comapUpperStarIso a j).hom.app
          ((Mod.comap (coefficientMap b Z)).obj M) := by
    exact square_remove_inverses
      ((coefficientRestrictionComp a b X).app ((CondensedRing.upperStar Λ'' j).obj M))
      ((CondensedRing.upperStar Λ j).mapIso ((coefficientRestrictionComp a b Z).app M))
      _ _ (by
        simpa only [Functor.mapIso_inv, Iso.app_inv, Category.assoc] using
          coefficientUpperStar_comp a b j M)
  have hd := CategoryTheory.Functor.exactSquare_comp_inverse
    (Mod.comap (coefficientMap b Z)) (Mod.comap (coefficientMap a Z))
    (Mod.comap (coefficientMap (a ≫ b) Z))
    (Mod.comap (coefficientMap b X)) (Mod.comap (coefficientMap a X))
    (Mod.comap (coefficientMap (a ≫ b) X))
    (CondensedRing.upperStar Λ'' j) (CondensedRing.upperStar Λ' j)
    (CondensedRing.upperStar Λ j)
    (CondensedRing.comapUpperStarIso b j) (CondensedRing.comapUpperStarIso a j)
    (CondensedRing.comapUpperStarIso (a ≫ b) j)
    (coefficientRestrictionComp a b Z) (coefficientRestrictionComp a b X) ho N
  dsimp only [Functor.mapDerivedCategorySquareIso] at hd
  have hd' : (CondensedRing.derivedComapUpperStarIso (a ≫ b) j).hom.app N ≫
      (CondensedRing.upperStar Λ j).mapDerivedCategory.map
        ((derivedCoefficientRestrictionComp a b Z).hom.app N) =
    (derivedCoefficientRestrictionComp a b X).hom.app
      ((CondensedRing.upperStar Λ'' j).mapDerivedCategory.obj N) ≫
      (Mod.comap (coefficientMap a X)).mapDerivedCategory.map
        ((CondensedRing.derivedComapUpperStarIso b j).hom.app N) ≫
      (CondensedRing.derivedComapUpperStarIso a j).hom.app
        ((Mod.comap (coefficientMap b Z)).mapDerivedCategory.obj N) := by
    simpa only [CondensedRing.derivedComapUpperStarIso,
      derivedCoefficientRestrictionComp] using hd
  have h := IsIso.inv_eq_inv.mpr hd'
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app, Category.assoc] using h.symm

private theorem scalarComp_conjugate (W : Scheme.{u}) :
    conjugateEquiv
      ((condensedScalarAdjunction a W).comp
        (condensedScalarAdjunction b W))
      (condensedScalarAdjunction (a ≫ b) W)
      (condensedScalarComp a b W).inv =
        (derivedCoefficientRestrictionComp a b W).inv := by
  rw [scalarComp_eq]
  exact scalarComp_conjugate_generic
    (condensedScalarAdjunction a W)
    (condensedScalarAdjunction b W)
    (condensedScalarAdjunction (a ≫ b) W)
    (derivedCoefficientRestrictionComp a b W)


private theorem scalarOpen_comp {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j]
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (condensedScalar b Z).map ((condensedOpenScalar a j).hom.app K) ≫
      (condensedOpenScalar b j).hom.app
        ((condensedScalar a X).obj K) ≫
      (CondensedRing.openImmersionLowerShriek Λ'' j).mapDerivedCategory.map
        ((condensedScalarComp a b X).hom.app K) =
    (condensedScalarComp a b Z).hom.app
      ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K) ≫
      (condensedOpenScalar (a ≫ b) j).hom.app K := by
  apply Eq.symm
  apply normalizedCocycle
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ' j)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'' j)
    (condensedScalarAdjunction a X)
    (condensedScalarAdjunction a Z)
    (condensedScalarAdjunction b X)
    (condensedScalarAdjunction b Z)
    (condensedScalarAdjunction (a ≫ b) X)
    (condensedScalarAdjunction (a ≫ b) Z)
    (condensedOpenScalar a j)
    (condensedOpenScalar b j)
    (condensedOpenScalar (a ≫ b) j)
    (condensedScalarComp a b X) (condensedScalarComp a b Z)
    (CondensedRing.derivedComapUpperStarIso a j).symm
    (CondensedRing.derivedComapUpperStarIso b j).symm
    (CondensedRing.derivedComapUpperStarIso (a ≫ b) j).symm
    (derivedCoefficientRestrictionComp a b X).symm
    (derivedCoefficientRestrictionComp a b Z).symm
  · exact scalarOpen_conjugate a j
  · exact scalarOpen_conjugate b j
  · exact scalarOpen_conjugate (a ≫ b) j
  · exact scalarComp_conjugate a b X
  · exact scalarComp_conjugate a b Z
  · exact derivedUpperStar_comp a b j




end CoefficientCompositionProof

set_option backward.defeqAttrib.useBackward false in
attribute [local irreducible]
  Mod.derivedExtendMapDerivedCategoryAdjunction
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Mod.extendScalars condensedScalarComp in
/-- The original coefficient projections satisfy the full tensor cocycle, including
an arbitrary finite-valued closure coefficient as the last ring.
Source: blueprint proof Steps 9, 12--13; ringed coefficient projection cocycle
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two paths under the scalar adjunctions. Their transposes are
the same proper counit followed by the same open unit and the restriction compositor.
Ordinary adjunction triangle identities give equality before derivation. Universal
derived units and counits descend it, and proper/open pasting gives the displayed
cocycle on all objects. The closure case uses the identical original maps. -/
theorem condensedProjection_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      :
    (condensedScalar b Y).map ((condensedProjection a c).app K) ≫
        (condensedProjection b c).app ((condensedScalar a X).obj K) ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ'' c).map
          ((condensedScalarComp a b X).hom.app K) =
      (condensedScalarComp a b Y).hom.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K) ≫
        (condensedProjection (a ≫ b) c).app K := by
  exact pasteScalar_comp
    (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (CondensedRing.openImmersionLowerShriek Λ' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ' c.g).rightDerivedFunctor
    (CondensedRing.openImmersionLowerShriek Λ'' c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ'' c.g).rightDerivedFunctor
    (condensedScalar a X) (condensedScalar a c.Z) (condensedScalar a Y)
    (condensedScalar b X) (condensedScalar b c.Z) (condensedScalar b Y)
    (condensedScalar (a ≫ b) X) (condensedScalar (a ≫ b) c.Z)
    (condensedScalar (a ≫ b) Y)
    (condensedScalarComp a b X).hom (condensedScalarComp a b c.Z).hom
    (condensedScalarComp a b Y).hom
    (condensedPushScalar a c.g) (condensedPushScalar b c.g)
    (condensedPushScalar (a ≫ b) c.g)
    (condensedOpenScalar a c.i).hom
    (condensedOpenScalar b c.i).hom
    (condensedOpenScalar (a ≫ b) c.i).hom
    (scalarPush_comp a b c.g) (scalarOpen_comp a b c.i) K


/-- Identity scalar extension is exact, with its actual tensor-unit normalization.
Source: blueprint proof Step 9; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection).
Proof: the coefficient map is the identity by functoriality of coefficient pullback.
The ordinary scalar adjunction identifies its left adjoint with the identity by
Mod.extendScalarsId. Transport finite-limit preservation along that isomorphism. -/
theorem identityScalar_flat (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u}) :
    PreservesFiniteLimits (Mod.extendScalars (coefficientMap (𝟙 Λ₀) W)) := by
  exact preservesFiniteLimits_of_natIso
    (Mod.extendScalarsIsoOfEq (coefficientMap_id (Λ := Λ₀) W) ≪≫
      Mod.extendScalarsId).symm

attribute [instance] identityScalar_flat

/-- The derived scalar unit is induced by the original restriction identity.
Source: blueprint proof Step 9; Stacks 06YY
(blueprint: def-pur-condensed-compact-support-projection). -/
def condensedScalarId (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u}) :
    condensedScalar (𝟙 Λ₀) W ≅ 𝟭 _ :=
  (condensedScalarAdjunction (𝟙 Λ₀) W).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso
          (Mod.comapCongr (coefficientMap_id (Λ := Λ₀) W) ≪≫ Mod.comapId _) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm)

section CoefficientIdentityProof
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor

private def coefficientRestrictionId
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u}) :
    Mod.comap (D := Sheaf (ProEt.topology W) Ab.{u + 1})
      (coefficientMap (𝟙 Λ₀) W) ≅
      𝟭 (Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ₀ W)) :=
  Mod.comapCongr (coefficientMap_id (Λ := Λ₀) W) ≪≫
    Mod.comapId (condensedRingObj Λ₀ W)

private theorem coefficientRestrictionId_hom
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ₀ W)) :
    ((coefficientRestrictionId Λ₀ W).hom.app M).hom = 𝟙 M.X := by
  exact comapIdentity_hom (coefficientMap_id (Λ := Λ₀) W) M

private theorem coefficientLowerStar_id
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X)) :
    (CondensedRing.comapLowerStarIso (𝟙 Λ₀) f).hom.app M ≫
        (CondensedRing.lowerStar Λ₀ f).map
          ((coefficientRestrictionId Λ₀ X).hom.app M) =
      (coefficientRestrictionId Λ₀ Y).hom.app ((CondensedRing.lowerStar Λ₀ f).obj M) := by
  apply Mod.hom_ext
  have h := Mod.comapMapModComapIso_hom_app_hom
    ((f)_*[Ab.{u + 1}]) (coefficientMap (𝟙 Λ₀) X) (coefficientMap (𝟙 Λ₀) Y)
    (condensedPushforwardHom Λ₀ f) (condensedPushforwardHom Λ₀ f)
    (condensedPushforwardHom_comp_map_coefficientMap (𝟙 Λ₀) f).symm M
  change ((CondensedRing.comapLowerStarIso (𝟙 Λ₀) f).hom.app M).hom ≫
    ((f)_*[Ab.{u + 1}]).map (((coefficientRestrictionId Λ₀ X).hom.app M).hom) =
      ((coefficientRestrictionId Λ₀ Y).hom.app ((CondensedRing.lowerStar Λ₀ f).obj M)).hom
  change ((CondensedRing.comapLowerStarIso (𝟙 Λ₀) f).hom.app M).hom = _ at h
  rw [h, coefficientRestrictionId_hom, coefficientRestrictionId_hom]
  change (𝟙 ((f)_*[Ab.{u + 1}].obj M.X)) ≫ (f)_*[Ab.{u + 1}].map (𝟙 M.X) =
    𝟙 ((f)_*[Ab.{u + 1}].obj M.X)
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem coefficientUpperStar_id
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ₀ Y)) :
    (CondensedRing.comapUpperStarIso (𝟙 Λ₀) j).hom.app M ≫
        (CondensedRing.upperStar Λ₀ j).map
          ((coefficientRestrictionId Λ₀ Y).hom.app M) =
      (coefficientRestrictionId Λ₀ X).hom.app ((CondensedRing.upperStar Λ₀ j).obj M) := by
  apply Mod.hom_ext
  let κ := CondensedRing.openCoefficientCollapse Λ₀ j
  change ((CondensedRing.comapUpperStarIso (𝟙 Λ₀) j).hom.app M).hom ≫
      ((CondensedRing.upperStar Λ₀ j).map
        ((coefficientRestrictionId Λ₀ Y).hom.app M)).hom = _
  rw [coefficientRestrictionId_hom]
  have hn := congrArg Mod.Hom.hom
    (κ.hom.naturality ((coefficientRestrictionId Λ₀ Y).hom.app M))
  change ((CondensedRing.upperStar Λ₀ j).map
      ((coefficientRestrictionId Λ₀ Y).hom.app M)).hom ≫ (κ.hom.app M).hom =
    (κ.hom.app ((Mod.comap (coefficientMap (𝟙 Λ₀) Y)).obj M)).hom ≫
      (ProEtale.upperStar Ab.{u + 1} j).map
        (((coefficientRestrictionId Λ₀ Y).hom.app M).hom) at hn
  rw [coefficientRestrictionId_hom] at hn
  have hmap := (ProEtale.upperStar Ab.{u + 1} j).map_id M.X
  rw [hmap] at hn
  replace hn := hn.trans (Category.comp_id _)
  apply (cancel_mono (κ.hom.app M).hom).1
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (fun h ↦ ((CondensedRing.comapUpperStarIso (𝟙 Λ₀) j).hom.app M).hom ≫ h) hn).trans ?_
  exact (openCoefficient_hom_normalization (𝟙 Λ₀) j M).trans (Category.id_comp _).symm


private theorem identityScalar_normalization
    (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] (W : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ₀ W))) :
    (condensedScalarAdjunction (𝟙 Λ₀) W).unit.app K ≫
      (Mod.comap (coefficientMap (𝟙 Λ₀) W)).mapDerivedCategory.map
        ((condensedScalarId Λ₀ W).hom.app K) =
      (derivedIdentity (coefficientRestrictionId Λ₀ W)).inv.app K := by
  exact scalar_unit_normalization
    (condensedScalarAdjunction (𝟙 Λ₀) W)
    (derivedIdentity (coefficientRestrictionId Λ₀ W)) K

attribute [local irreducible]
  CondensedRing.derivedComapLowerStarIso
  CondensedRing.derivedComapUpperStarIso
  Mod.derivedExtendMapDerivedCategoryAdjunction Mod.extendScalars

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The original projection at identity coefficients is precisely the tensor unit.
Source: blueprint proof Step 9; ringed coefficient projection cocycle
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the proper projection at the identity map. Both routes have the
original proper counit as their transpose; the open comparison has the original
open unit. Adjunction uniqueness and the ordinary scalar identity identify the
pasted projection with the displayed tensor-unit equation. -/
theorem condensedProjection_id (Λ₀ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ₀] [IsCommMonObj Λ₀] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ₀ X))) :
    (condensedProjection (𝟙 Λ₀) c).app K ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).map
          ((condensedScalarId Λ₀ X).hom.app K) =
      (condensedScalarId Λ₀ Y).hom.app
        ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ₀ c).obj K) := by
  have hp := derived_square_identity (CondensedRing.lowerStar Λ₀ c.g)
    (Mod.comap (coefficientMap (𝟙 Λ₀) c.Z)) (Mod.comap (coefficientMap (𝟙 Λ₀) Y))
    (coefficientRestrictionId Λ₀ c.Z) (coefficientRestrictionId Λ₀ Y)
    (CondensedRing.comapLowerStarIso (𝟙 Λ₀) c.g) (coefficientLowerStar_id Λ₀ c.g)
  have ho := exact_square_identity (CondensedRing.upperStar Λ₀ c.i)
    (Mod.comap (coefficientMap (𝟙 Λ₀) c.Z)) (Mod.comap (coefficientMap (𝟙 Λ₀) X))
    (coefficientRestrictionId Λ₀ c.Z) (coefficientRestrictionId Λ₀ X)
    (CondensedRing.comapUpperStarIso (𝟙 Λ₀) c.i) (coefficientUpperStar_id Λ₀ c.i)
  have hp' : ∀ N, (CondensedRing.derivedComapLowerStarIso (𝟙 Λ₀) c.g).hom.app N ≫
      (CondensedRing.lowerStar Λ₀ c.g).rightDerivedFunctor.map
        ((derivedIdentity (coefficientRestrictionId Λ₀ c.Z)).hom.app N) =
      (derivedIdentity (coefficientRestrictionId Λ₀ Y)).hom.app
        ((CondensedRing.lowerStar Λ₀ c.g).rightDerivedFunctor.obj N) := by
    simpa only [CondensedRing.derivedComapLowerStarIso, derived_square] using hp
  have ho' : ∀ N, (CondensedRing.derivedComapUpperStarIso (𝟙 Λ₀) c.i).hom.app N ≫
      (CondensedRing.upperStar Λ₀ c.i).mapDerivedCategory.map
        ((derivedIdentity (coefficientRestrictionId Λ₀ c.Z)).hom.app N) =
      (derivedIdentity (coefficientRestrictionId Λ₀ X)).hom.app
        ((CondensedRing.upperStar Λ₀ c.i).mapDerivedCategory.obj N) := by
    simpa only [CondensedRing.derivedComapUpperStarIso,
      Functor.mapDerivedCategorySquareIso] using ho
  have hpush := scalar_push_identity
    (condensedScalarAdjunction (𝟙 Λ₀) c.Z)
    (condensedScalarAdjunction (𝟙 Λ₀) Y)
    (derivedIdentity (coefficientRestrictionId Λ₀ c.Z))
    (derivedIdentity (coefficientRestrictionId Λ₀ Y))
    (condensedScalarId Λ₀ c.Z) (condensedScalarId Λ₀ Y)
    (identityScalar_normalization Λ₀ c.Z) (identityScalar_normalization Λ₀ Y)
    (CondensedRing.lowerStar Λ₀ c.g).rightDerivedFunctor
    (CondensedRing.derivedComapLowerStarIso (𝟙 Λ₀) c.g) hp'
  have hopen := scalar_open_identity
    (condensedScalarAdjunction (𝟙 Λ₀) X)
    (condensedScalarAdjunction (𝟙 Λ₀) c.Z)
    (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ₀ c.i)
    (derivedIdentity (coefficientRestrictionId Λ₀ X))
    (derivedIdentity (coefficientRestrictionId Λ₀ c.Z))
    (condensedScalarId Λ₀ X) (condensedScalarId Λ₀ c.Z)
    (identityScalar_normalization Λ₀ X) (identityScalar_normalization Λ₀ c.Z)
    (CondensedRing.derivedComapUpperStarIso (𝟙 Λ₀) c.i) ho'
  dsimp only [condensedProjection, CondensedRing.rightDerivedLowerShriekOfCompactification]
  apply pasteScalar_identity
    (CondensedRing.openImmersionLowerShriek Λ₀ c.i).mapDerivedCategory
    (CondensedRing.lowerStar Λ₀ c.g).rightDerivedFunctor
    (condensedScalar (𝟙 Λ₀) X) (condensedScalar (𝟙 Λ₀) c.Z) (condensedScalar (𝟙 Λ₀) Y)
    (condensedScalarId Λ₀ X) (condensedScalarId Λ₀ c.Z) (condensedScalarId Λ₀ Y)
    (condensedPushScalar (𝟙 Λ₀) c.g)
    (condensedOpenScalar (𝟙 Λ₀) c.i).hom
  · rw [scalarPush_eq]
    exact hpush
  · rw [scalarOpen_eq]
    set_option backward.isDefEq.respectTransparency true in
      exact hopen

end CoefficientIdentityProof

end Projection

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A named presentation of the original derived pullback.
Source: the existing condensed upper-star construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedUpperStar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

/-- A named presentation of the original derived direct image.
Source: the existing condensed lower-star construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedLowerStar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctor

/-- A named presentation of the original exact open extension.
Source: the existing condensed open extension construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedOpenShriek (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

/-- The original derived adjunction in the named functor presentation.
Source: the archived derived upper-star/lower-star adjunction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fieldDerivedUpperStar Λ f ⊣ fieldDerivedLowerStar Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

/-- The original pullback compositor in the named functor presentation.
Source: the archived derived upper-star compositor.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedPullComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fieldDerivedUpperStar Λ (f ≫ g) ≅ fieldDerivedUpperStar Λ g ⋙ fieldDerivedUpperStar Λ f :=
  CondensedRing.leftDerivedUpperStarComp Λ f g

/-- The exact open adjunction expressed using the actual left-derived pullback.
Source: archived open-immersion derived adjunction; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldOpenAdjunction {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (fieldDerivedOpenShriek Λ j) ⊣
      (fieldDerivedUpperStar Λ j) :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

/-- Compose an inverse-image comparison with the proper counit.
Source: blueprint proof Steps 15--16; naturality of the compositor and counit.
(blueprint: def-pur-condensed-compact-support-projection). -/
def counitRestrictionNat
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) {P : E ⥤ D} {R : D ⥤ E} (ad : P ⊣ R)
    (V : D ⥤ C) (U : E ⥤ C) (α : U ≅ P ⋙ V) :
    (J ⋙ R) ⋙ U ⟶ J ⋙ V where
  app K := α.hom.app (R.obj (J.obj K)) ≫ V.map (ad.counit.app (J.obj K))
  naturality {K L} v := by
    have hα : U.map (R.map (J.map v)) ≫ α.hom.app (R.obj (J.obj L)) =
        α.hom.app (R.obj (J.obj K)) ≫ V.map (P.map (R.map (J.map v))) :=
      α.hom.naturality (R.map (J.map v))
    have hε : P.map (R.map (J.map v)) ≫ ad.counit.app (J.obj L) =
        ad.counit.app (J.obj K) ≫ J.map v := ad.counit.naturality (J.map v)
    change U.map (R.map (J.map v)) ≫
        (α.hom.app (R.obj (J.obj L)) ≫ V.map (ad.counit.app (J.obj L))) =
      (α.hom.app (R.obj (J.obj K)) ≫ V.map (ad.counit.app (J.obj K))) ≫ V.map (J.map v)
    rw [← Category.assoc, hα, Category.assoc, ← V.map_comp, hε, V.map_comp,
      Category.assoc]

/-- The original restriction normalization, assembled naturally in the input.
Source: blueprint proof Steps 15--16.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestrictionNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (fieldDerivedOpenShriek Λ c.i ⋙ fieldDerivedLowerStar Λ r.hom) ⋙
        fieldDerivedUpperStar Λ d.i ⟶
      fieldDerivedOpenShriek Λ c.i ⋙ fieldDerivedUpperStar Λ c.i :=
  counitRestrictionNat
    (fieldDerivedOpenShriek Λ c.i)
    (fieldDerivedAdjunction Λ r.hom)
    (fieldDerivedUpperStar Λ c.i)
    (fieldDerivedUpperStar Λ d.i)
    ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦
      (fieldDerivedUpperStar Λ h)) r.i_hom.symm)) ≪≫
      fieldDerivedPullComp Λ c.i r.hom)



attribute [local irreducible] fieldProperOpenRestrictionNat

/-- The restriction normalization of a proper refinement, before its invertibility
is asserted. Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (fieldDerivedUpperStar Λ d.i).obj
        ((fieldDerivedLowerStar Λ r.hom).obj ((fieldDerivedOpenShriek Λ c.i).obj K)) ⟶
      (fieldDerivedUpperStar Λ c.i).obj ((fieldDerivedOpenShriek Λ c.i).obj K) :=
  (fieldProperOpenRestrictionNat Λ r).app K

private theorem unique_normalized_lift
    {C D : Type*} [Category C] [Category D] {J : C ⥤ D} {U : D ⥤ C}
    (ad : J ⊣ U) (K : C) (M : D) {N : C} (β : U.obj M ⟶ N) [IsIso β]
    (z : K ⟶ N) : ∃! e : J.obj K ⟶ M, ad.homEquiv _ _ e ≫ β = z := by
  let e₀ := (ad.homEquiv K M).symm (z ≫ inv β)
  have h₀ : ad.homEquiv K M e₀ ≫ β = z := by
    simp only [e₀, Equiv.apply_symm_apply, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  refine ⟨e₀, h₀, fun e he ↦ ?_⟩
  apply (ad.homEquiv K M).injective
  exact (cancel_mono β).mp (he.trans h₀.symm)

/-- The proper/open refinement is uniquely fixed by the original open unit.
Source: blueprint proof Steps 15--16; Stacks 0F7B
(blueprint: def-pur-condensed-compact-support-projection).
Proof: restriction of direct image to the open is the direct image of the open
restriction, since open extension is an exact left adjoint. In the pulled-back square
the section defined by the refinement is clopen. Extension by zero restricts to the
original input on that component and vanishes on its complement. Thus the displayed
restriction normalization is invertible. The open Hom bijection supplies a unique
arrow with this transpose; no proper base change outside the open is needed. -/
theorem fieldProperOpen_existsUnique {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    ∃! e : (fieldDerivedOpenShriek Λ d.i).obj K.obj ⟶
        (fieldDerivedLowerStar Λ r.hom).obj
          ((fieldDerivedOpenShriek Λ c.i).obj K.obj),
      (fieldOpenAdjunction Λ d.i).homEquiv _ _ e ≫
          fieldProperOpenRestriction Λ r K.obj =
        (fieldOpenAdjunction Λ c.i).unit.app K.obj := by
  have hc := condensedOpen_restrictedCounit_isIso Λ r K.obj
  have : IsIso ((fieldDerivedUpperStar Λ c.i).map
      ((fieldDerivedAdjunction Λ r.hom).counit.app
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj))) := hc
  have : IsIso (fieldProperOpenRestriction Λ r K.obj) := by
    unfold fieldProperOpenRestriction fieldProperOpenRestrictionNat counitRestrictionNat
    dsimp only
    infer_instance
  exact unique_normalized_lift (fieldOpenAdjunction Λ d.i) K.obj _
    (fieldProperOpenRestriction Λ r K.obj) ((fieldOpenAdjunction Λ c.i).unit.app K.obj)

/-- The unit-normalized refinement arrow, without an arbitrary splitting.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldDerivedOpenShriek Λ d.i).obj K.obj ⟶
      (fieldDerivedLowerStar Λ r.hom).obj
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj) :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose

private theorem fieldProperOpen_spec {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (fieldOpenAdjunction Λ d.i).homEquiv _ _ (fieldProperOpen Λ r K) ≫
        fieldProperOpenRestriction Λ r K.obj =
      (fieldOpenAdjunction Λ c.i).unit.app K.obj :=
  (fieldProperOpen_existsUnique Λ r K).exists.choose_spec

attribute [local irreducible] fieldProperOpen fieldOpenAdjunction
  DerivedCategory.instPreadditive

section NaturalityProof

attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek

private theorem fieldHomology_additive
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C] (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).Additive := by
  have : (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor C n).Additive :=
    Functor.additive_of_iso (DerivedCategory.homologyFunctorFactorsh C n).symm
  exact (Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _).mpr inferInstance

attribute [local instance] fieldHomology_additive

private theorem fieldHomology_biprod
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (n : ℤ) (K L : DerivedCategory C) :
    PreservesBinaryBiproduct K L (DerivedCategory.homologyFunctor C n) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

attribute [local instance] fieldHomology_biprod

private theorem fieldBounded_biprod {X : Scheme.{u}}
    (K L : BoundedConstructible (condensedRingObj Λ X)) :
    boundedConstructible (condensedRingObj Λ X) (K.obj ⊞ L.obj) := by
  let P : ObjectProperty (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) := IsConstructibleModuleObject (condensedRingObj Λ X)
  let : ObjectProperty.IsClosedUnderExtensions P :=
    (CondensedRing.constructible_cokernels_extensions X (condensedRingObj Λ X)).2
  have hK := (mem_boundedConstructible_iff (condensedRingObj Λ X) K.obj).mp K.property
  have hL := (mem_boundedConstructible_iff (condensedRingObj Λ X) L.obj).mp L.property
  rw [mem_boundedConstructible_iff]
  refine ⟨?_, fun n ↦ ?_⟩
  · obtain ⟨a, b, hK⟩ := hK.1
    obtain ⟨c, d, hL⟩ := hL.1
    refine ⟨min a c, max b d, fun n hn ↦ ?_⟩
    have hk : n < a ∨ b < n := by omega
    have hl : n < c ∨ d < n := by omega
    exact ((biprod_isZero_iff _ _).mpr ⟨hK n hk, hL n hl⟩).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapBiprod K.obj L.obj)
  · exact (P.prop_biprod (hK.2 n) (hL.2 n)).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapBiprod K.obj L.obj).symm

private theorem fieldProperOpen_naturality_retract {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)}
    (M : BoundedConstructible (condensedRingObj Λ X))
    (i : K.obj ⟶ M.obj) (p : M.obj ⟶ K.obj)
    (j : L.obj ⟶ M.obj) (q : M.obj ⟶ L.obj)
    (hip : i ≫ p = 𝟙 K.obj) (hjq : j ≫ q = 𝟙 L.obj) (v : K ⟶ L) :
    (fieldDerivedOpenShriek Λ d.i).map v.hom ≫
        fieldProperOpen Λ r L =
      fieldProperOpen Λ r K ≫ (fieldDerivedLowerStar Λ r.hom).map
        ((fieldDerivedOpenShriek Λ c.i).map v.hom) := by
  exact normalized_lift_naturality_of_unique (fieldOpenAdjunction Λ d.i) _ _
    (fieldProperOpenRestrictionNat Λ r) (fieldOpenAdjunction Λ c.i).unit
    i p j q hip hjq v.hom (fieldProperOpen_existsUnique Λ r M)
    (fieldProperOpen Λ r K) (fieldProperOpen Λ r L)
    (fieldProperOpen_spec Λ r K) (fieldProperOpen_spec Λ r L)

/-- Naturality of the original unit-normalized proper/open comparison.
Source: blueprint Steps 15--16, using uniqueness at a binary sum.
(blueprint: def-pur-condensed-compact-support-projection). -/
theorem fieldProperOpen_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)} (v : K ⟶ L) :
    (fieldDerivedOpenShriek Λ d.i).map v.hom ≫
        fieldProperOpen Λ r L =
      fieldProperOpen Λ r K ≫ (fieldDerivedLowerStar Λ r.hom).map
        ((fieldDerivedOpenShriek Λ c.i).map v.hom) := by
  exact fieldProperOpen_naturality_retract Λ r
    ⟨K.obj ⊞ L.obj, fieldBounded_biprod Λ K L⟩
    biprod.inl biprod.fst biprod.inr biprod.snd biprod.inl_fst biprod.inr_snd v



end NaturalityProof

/-- Proper-image composition is the conjugate of the actual pullback composition.
Source: archived module-object derived operations; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fieldDerivedLowerStar Λ f) ⋙
        (fieldDerivedLowerStar Λ g) ≅
      fieldDerivedLowerStar Λ (f ≫ g) :=
  conjugateIsoEquiv
    ((fieldDerivedAdjunction Λ g).comp
      (fieldDerivedAdjunction Λ f))
    (fieldDerivedAdjunction Λ (f ≫ g))
    (fieldDerivedPullComp Λ f g)

/-- Apply direct image to a natural lift and then its natural compositor.
Source: blueprint Step 15, functoriality of composition.
(blueprint: def-pur-condensed-compact-support-projection). -/
def assembleLiftNat
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (F : C ⥤ D) (G : C ⥤ E) (P : E ⥤ D) (R : D ⥤ H) (S : E ⥤ H)
    (lift : F ⟶ G ⋙ P) (cmp : P ⋙ R ⟶ S) : F ⋙ R ⟶ G ⋙ S where
  app K := R.map (lift.app K) ≫ cmp.app (G.obj K)
  naturality {K L} v := by
    change R.map (F.map v) ≫ (R.map (lift.app L) ≫ cmp.app (G.obj L)) =
      (R.map (lift.app K) ≫ cmp.app (G.obj K)) ≫ S.map (G.map v)
    rw [← R.map_comp_assoc, lift.naturality, R.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun z ↦ R.map (lift.app K) ≫ z) (cmp.naturality (G.map v))

/-- The original normalized lift on bounded constructible inputs.
Source: blueprint Step 15.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (fieldDerivedOpenShriek Λ d.i) ⟶
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (fieldDerivedOpenShriek Λ c.i)) ⋙
          (fieldDerivedLowerStar Λ r.hom) where
  app := fieldProperOpen Λ r
  naturality := fun _ _ v ↦ fieldProperOpen_naturality Λ r v

/-- The original proper/open refinement assembled naturally.
Source: blueprint Step 15.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ d.i) ⋙
        fieldDerivedLowerStar Λ d.g ⟶
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙ fieldDerivedOpenShriek Λ c.i) ⋙
        fieldDerivedLowerStar Λ c.g :=
  assembleLiftNat _ _ _
    (fieldDerivedLowerStar Λ d.g)
    (fieldDerivedLowerStar Λ c.g)
    (fieldProperOpenNat Λ r)
    ((fieldPushComp Λ r.hom d.g).hom ≫
      (eqToIso (congrArg (fun h : c.Z ⟶ Y ↦
        (fieldDerivedLowerStar Λ h)) r.hom_g)).hom)

/-- The canonical refinement component, in the direction from coarser to finer.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementApp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).obj K.obj ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj :=
  (fieldRefinementNat Λ r).app K

/-- Naturality of the fixed refinement components.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection).
Proof: transpose the two composites under the open adjunction. Naturality of its
unit and of the proper counit makes the transposes equal; the Hom bijection then
gives the equation. Proper-image composition is itself natural. -/
theorem fieldRefinementApp_naturality {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    {K L : BoundedConstructible (condensedRingObj Λ X)} (v : K ⟶ L) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).map v.hom ≫
        fieldRefinementApp Λ r L =
      fieldRefinementApp Λ r K ≫
        (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).map v.hom := by
  exact (fieldRefinementNat Λ r).naturality v

/-- The specified condensed refinement as a whole natural transformation.
Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ d ⟶
      (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ c where
  app := fieldRefinementApp Λ r
  naturality := fun _ _ v ↦ fieldRefinementApp_naturality Λ r v


end WeilConjectures.CompactSupportCondensedRealization



namespace WeilConjectures.CompactSupportCondensedRealization

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp

private def fieldPushId (Z : Scheme.{u}) :
    (CondensedRing.lowerStar Λ (𝟙 Z)).rightDerivedFunctor ≅ 𝟭 _ :=
  conjugateIsoEquiv (fieldDerivedAdjunction Λ (𝟙 Z))
    Adjunction.id (CondensedRing.leftDerivedUpperStarId Λ Z).symm

private theorem fieldProperOpenRestriction_id {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    fieldProperOpenRestriction Λ (Compactification.Refinement.id c) K =
      (fieldDerivedUpperStar Λ c.i).map
        ((fieldPushId Λ c.Z).hom.app
          ((fieldDerivedOpenShriek Λ c.i).obj K)) := by
  exact restriction_identity_component
    (fieldDerivedAdjunction Λ (𝟙 c.Z))
    (CondensedRing.leftDerivedUpperStarId Λ c.Z)
    (fieldDerivedUpperStar Λ c.i)
    (CondensedRing.upperStar Λ (c.i ≫ 𝟙 c.Z)).leftDerivedFunctor
    (congrArg (fun h : X ⟶ c.Z ↦ (fieldDerivedUpperStar Λ h))
      (Category.comp_id c.i))
    (fieldDerivedPullComp Λ c.i (𝟙 c.Z))
    (fun M ↦ CondensedRing.leftDerivedUpperStarComp_id_right_app Λ c.i M)
    ((fieldDerivedOpenShriek Λ c.i).obj K)

private theorem fieldPushComp_id_left {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (M : DerivedCategory (Mod (Sheaf (ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (fieldPushComp Λ (𝟙 Z) g).hom.app M ≫
        (eqToIso (congrArg (fun h : Z ⟶ Y ↦
          (fieldDerivedLowerStar Λ h)) (Category.id_comp g))).hom.app M =
      (fieldDerivedLowerStar Λ g).map ((fieldPushId Λ Z).hom.app M) := by
  let L := fun h : Z ⟶ Y ↦ (fieldDerivedUpperStar Λ h)
  let R := fun h : Z ⟶ Y ↦ (fieldDerivedLowerStar Λ h)
  let ad := fun h : Z ⟶ Y ↦ fieldDerivedAdjunction Λ h
  let ai := fieldDerivedAdjunction Λ (𝟙 Z)
  let τ := (fieldDerivedPullComp Λ (𝟙 Z) g).hom
  let e := eqToHom (congrArg L (Category.id_comp g).symm)
  have hn : e ≫ τ = (Functor.rightUnitor (L g)).inv ≫
      Functor.whiskerLeft (L g) (CondensedRing.leftDerivedUpperStarId Λ Z).inv :=
    identity_comparison (F := L g) (F' := L (𝟙 Z ≫ g))
      (L := (CondensedRing.upperStar Λ (𝟙 Z)).leftDerivedFunctor)
      (congrArg L (Category.id_comp g)) τ
      (CondensedRing.leftDerivedUpperStarId Λ Z)
      (fun N ↦ CondensedRing.leftDerivedUpperStarComp_id_left_app Λ g N)
  exact conjugate_paste_identity L R ad (Category.id_comp g) ai
    (CondensedRing.leftDerivedUpperStarId Λ Z) τ hn M

private theorem fieldProperOpen_id {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : BoundedConstructible (condensedRingObj Λ X)) :
    fieldProperOpen Λ (Compactification.Refinement.id c) K =
      (fieldPushId Λ c.Z).inv.app
        ((fieldDerivedOpenShriek Λ c.i).obj K.obj) := by
  exact CategoryTheory.normalizedIdentityLift (fieldOpenAdjunction Λ c.i)
    ((fieldPushId Λ c.Z).app
      ((fieldDerivedOpenShriek Λ c.i).obj K.obj))
    (fieldProperOpenRestriction Λ (Compactification.Refinement.id c) K.obj)
    (fieldProperOpenRestriction_id Λ c K.obj)
    (fieldProperOpen_existsUnique Λ (Compactification.Refinement.id c) K)
    (fieldProperOpen Λ (Compactification.Refinement.id c) K)
    (fieldProperOpen_spec Λ (Compactification.Refinement.id c) K)

/-- The field refinement construction respects identities with its original unit.
Source: blueprint proof Steps 15--16; Stacks 0F7B
(blueprint: def-pur-condensed-compact-support-projection).
Proof: apply the open Hom bijection to the identity refinement. Its defining
normalization is the original open unit, so the unique arrow and the proper
identity compositor reduce to the identity transformation. -/
theorem fieldRefinement_id {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    fieldRefinement Λ (Compactification.Refinement.id c) = 𝟙 _ := by
  ext K
  change (fieldDerivedLowerStar Λ c.g).map
      (fieldProperOpen Λ (Compactification.Refinement.id c) K) ≫
    (fieldPushComp Λ (𝟙 c.Z) c.g).hom.app _ ≫
      (eqToIso (congrArg (fun h : c.Z ⟶ Y ↦
        (fieldDerivedLowerStar Λ h))
          (Category.id_comp c.g))).hom.app _ = 𝟙 _
  rw [fieldProperOpen_id, fieldPushComp_id_left, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  exact (fieldDerivedLowerStar Λ c.g).map_id _

end WeilConjectures.CompactSupportCondensedRealization

-- Export the proved property caches after checking the canonical constructions.
