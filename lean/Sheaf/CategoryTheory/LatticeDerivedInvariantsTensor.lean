/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.CategoryTheory.Action.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Sheaf.CategoryTheory.DerivedTensorRightExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # Normalized derived adjunction and tensor for discrete lattice actions

Source: main-20261015 direct-image proof, paragraph (3), agent expansion of the
ordinary internal discrete-lattice calculation
(blueprint: def-sfb-lattice-derived-invariants-tensor).

## Main definitions

* `trivialAdjunction`: the invariant-inclusion normalized adjunction.
* `derivedCore`: the unique strong derived tensor structure normalized on K-flat models.
* `derivedLax`: the tensor-of-counits lax structure on derived invariants.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

-- Prefer the canonical generic instances to avoid comparing the shortcut constructions.
attribute [instance 1100] HomologicalComplex.monoidalCategory
attribute [instance 1100] HomotopyCategory.MonoidalCategory.instMonoidalCategory
attribute [instance 1100] DerivedCategory.instMonoidalCategory_weilConjectures
attribute [instance 1100] DerivedCategory.instLaxMonoidalCochainComplexIntQ_weilConjectures

namespace Profinite.DiscreteLattice
namespace DerivedCup

/-- The canonical derived tensor normalization over independent localization universes.
All comparisons are elaborated for abstract coefficient categories, then specialized.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def derivedTensorNormalization
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u₃} C] [HasDerivedCategory.{u₄} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ X Y : GradedObject ℤ C, X.HasTensor Y]
    [∀ X Y : GradedObject ℤ D, X.HasTensor Y]
    [∀ X Y Z W : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X Y Z W]
    [∀ X Y Z W : GradedObject ℤ D, GradedObject.HasTensor₄ObjExt X Y Z W]
    [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ X Y Z : GradedObject ℤ D, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [∀ X Y Z : GradedObject ℤ D, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso D (.up ℤ))]
    (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint] [F.Monoidal]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (c : F.mapDerivedCategory.CoreMonoidal) : Prop :=
  (∀ P Q : CochainComplex C ℤ,
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
    (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
    (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
    F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫ DerivedCategory.Q.map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
    (c.μIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv ≫
      (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app Q) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ((F.mapHomologicalComplex (.up ℤ)).obj Q)) ∧
  c.εIso.hom ≫ F.mapDerivedCategory.map
      (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C))) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ C) =
    Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := D)) ≫
      (DerivedCategory.singleFunctor D 0).map (Functor.LaxMonoidal.ε F)

variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] (r : ℕ)

/-- The action category is Grothendieck abelian.
Source: paragraph (3), proof steps 1 and 13
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: use the section-module equivalence and the small action-site presentation;
module sheaves on that small ringed site are Grothendieck abelian. -/
@[instance] theorem actionGrothendieck : IsGrothendieckAbelian.{u + 1} (Equivariant R r) := by
  sorry

/-- Tensoring an action module has a right adjoint.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: transport the tensor-Hom adjunction on the small action site; the transported
tensor is the diagonal tensor since both are generated by balanced local pure tensors. -/
@[instance] theorem actionTensorLeftAdjoint (P : Equivariant R r) :
    (tensorLeft P).IsLeftAdjoint := by
  sorry

/-- The closed tensor uses the universal right adjoint, not a chosen tensor product.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionClosed : MonoidalClosed (Equivariant R r) :=
  ⟨fun P ↦ ⟨_, Adjunction.ofIsLeftAdjoint (tensorLeft P)⟩⟩

/-- Functorial flat resolutions in the diagonal action tensor category.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: the action-site tensor equivalence transports the functorial flat resolution
of module sheaves on a small ringed site, including its epimorphic augmentation. -/
@[instance] theorem actionFlatResolutions :
    Abelian.HasFunctorialFlatResolution (Equivariant R r) := by
  sorry

/-- Trivial discrete action leaves the module and all its maps unchanged.
Source: paragraph (3), proof step 1
(blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def trivial : Modules R ⥤ Equivariant R r where
  obj M := Action.trivial (Group r) M
  map f := ⟨f, fun _ ↦ (Category.id_comp f).trans (Category.comp_id f).symm⟩

/-- Addition is the original addition of maps.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance trivialAdditive : (trivial R r).Additive where
  map_add := by intros; rfl

/-- Trivial action is exact and left adjoint to the actual invariant limit.
Source: paragraph (3), proof steps 1 and 13
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: kernels and cokernels are formed on underlying modules. An equivariant map
from a trivial module is exactly a cone on the action diagram; the limit universal
property gives the adjunction with the invariant inclusion as its inverse transpose. -/
theorem trivialProperties : PreservesFiniteLimits (trivial R r) ∧
    PreservesFiniteColimits (trivial R r) ∧ Nonempty (trivial R r ⊣ invariants R r) := by
  sorry

/-- Exactness on kernels, inherited from componentwise kernels.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance trivialLimits : PreservesFiniteLimits (trivial R r) := (trivialProperties R r).1

/-- Exactness on cokernels, inherited from componentwise cokernels.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance trivialColimits : PreservesFiniteColimits (trivial R r) :=
  (trivialProperties R r).2.1

/-- The unique invariant-inclusion adjunction fixes the normalization.
Source: paragraph (3), proof step 1
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: a map to the invariant limit is uniquely determined by its composite with
its inclusion. The limit cone condition is exactly equivariance from a trivial action. -/
theorem trivialAdjunctionExists : ∃! adj : trivial R r ⊣ invariants R r,
    ∀ (M : Modules R) (P : Equivariant R r) (f : M ⟶ (invariants R r).obj P),
      ((adj.homEquiv M P).symm f).hom = f ≫ limit.π
        ((Action.functorCategoryEquivalence (Modules R) (Group r)).functor.obj P)
          PUnit.unit := by
  sorry

/-- The invariant inclusion determines this adjunction uniquely.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def trivialAdjunction : trivial R r ⊣ invariants R r :=
  (trivialAdjunctionExists R r).exists.choose

/-- The normalized adjunction supplies the left-adjoint property.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance trivialLeftAdjoint : (trivial R r).IsLeftAdjoint :=
  (trivialAdjunction R r).isLeftAdjoint

/-- The two universal total right-derived pairs have a unique unit-compatible comparison.
Source: paragraph (3), proof steps 4, 5 and 9
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: the universal bijections give transformations in both directions preserving
the computation units; uniqueness makes their two composites identities. -/
theorem ordinaryDerivedIsoExists : ∃! e : derivedInvariants R r ≅
    (invariants R r).rightDerivedFunctor,
    (invariants R r).rightDerivedFunctorOfQuasiIsoResolutionsUnit (resolutions R r) ≫
      Functor.whiskerLeft DerivedCategory.Qh.{u + 2} e.hom =
        (invariants R r).rightDerivedFunctorUnit := by
  sorry

/-- The unique comparison preserving the universal derived unit.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def ordinaryDerivedIso : derivedInvariants R r ≅ (invariants R r).rightDerivedFunctor :=
  (ordinaryDerivedIsoExists R r).exists.choose

/-- The canonical shift structure is transported through the normalized comparison.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance derivedCommShift : (derivedInvariants R r).CommShift ℤ :=
  Functor.CommShift.ofIso (ordinaryDerivedIso R r).symm ℤ

/-- Ordinary derived invariants carry distinguished triangles to distinguished triangles.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance derivedTriangulated : (derivedInvariants R r).IsTriangulated := by
  have : NatTrans.CommShift (ordinaryDerivedIso R r).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (ordinaryDerivedIso R r).symm ℤ
  exact Functor.isTriangulated_of_iso (ordinaryDerivedIso R r).symm

/-- The derived adjunction is the normalized exact-left derived adjunction.
Source: paragraph (3), proof steps 9 and 13
(blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def derivedAdjunction : (trivial R r).mapDerivedCategory.{u + 2, u + 2} ⊣ derivedInvariants R r :=
  ((trivialAdjunction R r).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
    (ordinaryDerivedIso R r).symm

/-- Countable total tensors use colimits in the same fixed coefficient universe.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionSmallColimits : HasColimitsOfSize.{0, 0} (Equivariant R r) :=
  hasColimitsOfSizeShrink _

/-- Identity underlying tensor and unit maps determine the ordinary strong tensor structure.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: the diagonal action on two trivial modules is trivial. Identity maps on underlying
modules give the tensorator and unit; faithfulness of forgetting proves all coherence laws. -/
theorem trivialCoreExists : ∃! c : (trivial R r).CoreMonoidal,
    c.εIso.hom.hom = 𝟙 _ ∧ ∀ M N : Modules R, (c.μIso M N).hom.hom = 𝟙 _ := by
  sorry

/-- The unique identity-coordinate tensor structure on trivial action.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def trivialCore : (trivial R r).CoreMonoidal := (trivialCoreExists R r).exists.choose

/-- The tensorator and unit are the identity on underlying modules.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance trivialMonoidal : (trivial R r).Monoidal := (trivialCore R r).toMonoidal

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance moduleGradedTensor (X Y : GradedObject ℤ (Modules R)) : X.HasTensor Y :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance moduleGradedFour (X Y Z W : GradedObject ℤ (Modules R)) :
    GradedObject.HasTensor₄ObjExt X Y Z W :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance moduleGradedLeft (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance moduleGradedRight (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionGradedTensor (X Y : GradedObject ℤ (Equivariant R r)) : X.HasTensor Y :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionGradedFour (X Y Z W : GradedObject ℤ (Equivariant R r)) :
    GradedObject.HasTensor₄ObjExt X Y Z W :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionGradedLeft (X Y Z : GradedObject ℤ (Equivariant R r)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  inferInstance

/-- The existing colimit tensor supplies its graded universal-property instance.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionGradedRight (X Y Z : GradedObject ℤ (Equivariant R r)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  inferInstance

/-- Cache the existing K-flat derivability proof for the recorded module localization.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance moduleHasDerivedTensor :
    (DerivedCategory.Qh.{u + 2} (C := Modules R)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso (Modules R) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory (Modules R)

/-- Cache the existing K-flat derivability proof for the ordinary action localization.
Source: paragraph (3), proof step 13 (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance actionHasDerivedTensor :
    (DerivedCategory.Qh.{u + 2} (C := Equivariant R r)).HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso (Equivariant R r) (.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory (Equivariant R r)

attribute [local irreducible] Functor.mapDerivedCategory

/-- The exact inflation tensorator is fixed on flat K-flat representatives and at the unit.
This writes the cochain normalization in the lattice localization universe u+2, retaining
the same canonical K-flat derived tensor as the generic comparison interface.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def IsDerivedTensorNormalized :=
  derivedTensorNormalization.{u + 2, u + 2, u + 2, u + 2, u + 1, u + 1}
    (trivial R r)

/-- There is exactly one strong derived tensor structure with this model and unit.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor).
Proof: trivial inflation is exact, strong monoidal, left adjoint and preserves flat
objects because forgetting creates exactness. Apply the two-variable derived tensor
comparison on flat K-flat resolutions. The displayed equation determines each tensorator
there; naturality determines it everywhere. The localized ordinary unit fixes the unit.
Associativity and both unit laws descend from those of the ordinary identity tensorator. -/
theorem derivedCoreExists : ∃! c, IsDerivedTensorNormalized R r c := by
  sorry

/-- The representative and unit equations determine the strong structure uniquely.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
def derivedCore := (derivedCoreExists R r).exists.choose

/-- The normalized derived trivial-action functor is strong monoidal.
Source: paragraph (3) (blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance derivedTrivialMonoidal : (trivial R r).mapDerivedCategory.{u + 2, u + 2}.Monoidal :=
  (derivedCore R r).toMonoidal

/-- Derived invariants have the lax tensor structure adjoint to the tensor of counits.
Source: paragraph (3), proof step 13
(blueprint: def-sfb-lattice-derived-invariants-tensor). -/
instance derivedLax : (derivedInvariants R r).LaxMonoidal :=
  (derivedAdjunction R r).rightAdjointLaxMonoidal

end DerivedCup
end Profinite.DiscreteLattice
