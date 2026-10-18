/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SectionModuleOperationsData

import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Normalized tensors on the existing pro-etale module functors

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pd-proetale-section-module-functors).

## Main definitions

- `coefficientMap`: the structural section-ring map adjunct to the condensed coefficient map.
- `pushforward`, `pullback`, `adjunction`: the actual ringed module operations and adjunction.
- `ordinaryTensorComparison`, `totalComparison`: uniquely normalized tensor comparisons.
- `pushforwardComposition`, `pullbackComposition`: geometric pasting and its adjunction mate.
- `extension`, `openAdjunction`: the actual open extension and restriction adjunction.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing ringed adjunction supplies this compact left-adjoint instance.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
instance pullback_isLeftAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).IsLeftAdjoint := (adjunction Λ f).isLeftAdjoint

/-- The existing ringed adjunction supplies this compact right-adjoint instance.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
instance pushforward_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).IsRightAdjoint := (adjunction Λ f).isRightAdjoint

/-- The sectionwise pullback is additive.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: its adjunction identifies it with scalar extension after additive inverse image. -/
@[instance] theorem pullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).Additive := by
  sorry

/-- The additive pullback preserves zero maps without unfolding its composite construction.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) pullback_preservesZero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (pullback Λ f)

/-- The fixed additive equivalence preserves zero maps.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) equivalence_preservesZero (X : Scheme.{u}) :
    (equivalence Λ X).functor.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (equivalence Λ X).functor

/-- Direct image is additive on the unchanged underlying sheaf maps.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: evaluate addition of maps on each base-changed site object. -/
@[instance] theorem pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).Additive := by
  sorry

/-- Pullback is exact for pulled-back condensed coefficients: alpha_f is invertible.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: transport the exact internal upperStar; its coefficient scalar change is an
isomorphism and inverse image is exact. -/
@[instance] theorem pullback_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pullback Λ f) := by
  sorry

/-- Pullback preserves finite colimits by its module adjunction.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors).
Proof: a left adjoint preserves colimits. -/
@[instance] theorem pullback_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback Λ f) := by
  sorry

/-- The existing exact-equivalence theorem supplies this compact finite-limit instance.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors). -/
instance equivalence_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (equivalence Λ X).functor :=
  ((InternalModuleOperations.internal_module_operations_transport Λ).1 X).2.2.1

/-- The existing exact-equivalence theorem supplies this compact finite-colimit instance.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors). -/
instance equivalence_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (equivalence Λ X).functor :=
  ((InternalModuleOperations.internal_module_operations_transport Λ).1 X).2.2.2.1

/-- The sectionwise equivalence preserves homology.
Source: Stacks 00YV (blueprint: def-pd-proetale-section-module-functors).
Proof: unchanged underlying sheaves identify kernels, images and cokernels. -/
@[instance] theorem equivalence_preservesHomology (X : Scheme.{u}) :
    (equivalence Λ X).functor.PreservesHomology := by
  sorry

/-- The internal relative tensor preserves zero maps in its first variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) internalTensor_preservesZero (X : Scheme.{u}) :
    (curriedTensor (internalModules Λ X)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (curriedTensor (internalModules Λ X))

/-- The internal relative tensor preserves zero maps in its second variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) internalTensorObj_preservesZero (X : Scheme.{u})
    (M : internalModules Λ X) :
    ((curriedTensor (internalModules Λ X)).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive ((curriedTensor (internalModules Λ X)).obj M)

/-- The sectionwise relative tensor preserves zero maps in its first variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) sectionTensor_preservesZero (X : Scheme.{u}) :
    (curriedTensor (modules Λ X)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (curriedTensor (modules Λ X))

/-- The sectionwise relative tensor preserves zero maps in its second variable.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
instance (priority := 2000) sectionTensorObj_preservesZero (X : Scheme.{u})
    (M : modules Λ X) :
    ((curriedTensor (modules Λ X)).obj M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive ((curriedTensor (modules Λ X)).obj M)

/-- The actual sectionwise pairing on internal direct image specifies its lax structure.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors). -/
def InternalPushNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (CondensedRing.lowerStar Λ f).LaxMonoidal) : Prop :=
  ∀ (M N : internalModules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((CondensedRing.lowerStar Λ f).obj M).X.obj.obj U)
    (y : ((CondensedRing.lowerStar Λ f).obj N).X.obj.obj U),
    ((m.μ M N).hom.hom.app U)
        (internalPureTensor Λ Y _ _ U x y) =
      internalPureTensor Λ X M N
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U) x y

/-- Direct image has the uniquely specified local-pure-tensor lax structure.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors).
Proof: its sectionwise bilinear pairing is balanced through the adjunct coefficient
map and restriction-compatible. Sheafify and use the relative-tensor coequalizer.
The associativity and unit equations hold on pure tensors. Local generation gives
uniqueness of the tensor maps; the regular-module unit and the unitor law then give
uniqueness of the unit map as well. -/
theorem internalPushNormalized_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! m : (CondensedRing.lowerStar Λ f).LaxMonoidal, InternalPushNormalized Λ f m := by
  sorry

/-- Choose the uniquely characterized direct-image pairing, not an arbitrary map.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance internalPushLax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar Λ f).LaxMonoidal :=
  (internalPushNormalized_existsUnique Λ f).exists.choose

/-- The actual oplax module pullback is the mate of the specified direct-image pairing.
Source: Stacks 03D7 and 03EL
(blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance internalPullOplax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).OplaxMonoidal :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).leftAdjointOplaxMonoidal

/-- The pullback mate tensor component is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: on extension-of-scalars pure tensors the map sends s tensor (m tensor n)
to (s tensor m) tensor (1 tensor n). Its inverse multiplies the two scalar factors.
Both respect balancing and commute with restriction, so sheafify to inverse maps. -/
@[instance] theorem internalPull_delta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    IsIso (Functor.OplaxMonoidal.δ (CondensedRing.upperStar Λ f) M N) := by
  sorry

/-- The unit component of the pullback mate is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: scalar extension sends the regular module to the regular module; multiplication
and insertion of 1 are mutually inverse by the unit and balancing relations. -/
@[instance] theorem internalPull_eta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Functor.OplaxMonoidal.η (CondensedRing.upperStar Λ f)) := by
  sorry

/-- Strong module pullback, retaining the mate oplax maps just constructed.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance internalPullMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (CondensedRing.upperStar Λ f)

/-- Pullback preserves flat internal modules.
Source: Stacks 03EL and 0G7E
(blueprint: def-pd-proetale-section-module-functors).
Proof: tensor with a pulled-back flat module is the pullback of tensor before scalar
extension. Exact inverse image and flatness make its acyclic short-exact test exact. -/
@[instance] theorem internalPull_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).PreservesFlat := by
  sorry

/-- The sectionwise pure-tensor normalization of ringed direct image.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors). -/
def PushNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (pushforward Λ f).LaxMonoidal) : Prop :=
  ∀ (M N : modules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((pushforward Λ f).obj M).val.obj U)
    (y : ((pushforward Λ f).obj N).val.obj U),
    ((m.μ M N).val.app U)
        (sectionPureTensor Λ Y _ _ U x y) =
      sectionPureTensor Λ X M N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U) x y

/-- The ringed direct-image pairing is uniquely specified, including its unit.
Source: Stacks 03EK and 03D7
(blueprint: def-pd-proetale-section-module-functors).
Proof: the sectionwise balanced pairing sheafifies. Coherence is checked on pure
tensors. The tensor universal property gives uniqueness of the tensorator, and its
regular-module unit equation forces the coefficient-map unit. -/
theorem pushNormalized_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! m : (pushforward Λ f).LaxMonoidal, PushNormalized Λ f m := by
  sorry

/-- The specified ringed direct-image pairing.
Source: Stacks 03D7 (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance pushLax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pushforward Λ f).LaxMonoidal :=
  (pushNormalized_existsUnique Λ f).exists.choose

/-- The specified ordinary ringed pullback comparison, as the mate of direct image.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance pullOplax {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).OplaxMonoidal := (adjunction Λ f).leftAdjointOplaxMonoidal

/-- The ordinary ringed pullback comparison is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: its pure-tensor formula is s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n); the inverse multiplies the scalar factors.
The balancing relations give well-defined mutually inverse maps before sheafification. -/
@[instance] theorem pull_delta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ Y) :
    IsIso (Functor.OplaxMonoidal.δ (pullback Λ f) M N) := by
  sorry

/-- The ordinary ringed pullback comparison on the unit is invertible.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors).
Proof: extension of scalars of a regular module is the regular module. -/
@[instance] theorem pull_eta_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (Functor.OplaxMonoidal.η (pullback Λ f)) := by
  sorry

/-- The strong ringed pullback retains the specified oplax mate maps.
Source: Stacks 03EL (blueprint: def-pd-proetale-section-module-functors). -/
noncomputable instance pullMonoidal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).Monoidal := Functor.Monoidal.ofOplaxMonoidal (pullback Λ f)

/-- The existing pure-tensor comparison is uniquely specified by its local formula.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors).
Proof: use internal_section_tensor_comparison for existence. Local pure tensors
generate the relative tensor after sheafification; their displayed images
therefore determine the sheaf-module map and hence the isomorphism uniquely. -/
theorem ordinaryTensorComparison_existsUnique (X : Scheme.{u})
    (M N : internalModules Λ X) :
    ∃! t : (equivalence Λ X).functor.obj (M ⊗ N) ≅
        (equivalence Λ X).functor.obj M ⊗ (equivalence Λ X).functor.obj N,
      ∀ (U : X.ProEtᵒᵖ) (x : M.X.obj.obj U) (y : N.X.obj.obj U),
        (t.hom.val.app U)
            (internalPureTensor Λ X M N U x y) =
          sectionPureTensor Λ X
            ((equivalence Λ X).functor.obj M) ((equivalence Λ X).functor.obj N) U x y := by
  sorry

/-- The existing ordinary tensor comparison, selected by its unique pure-tensor formula.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
def ordinaryTensorComparison (X : Scheme.{u}) (M N : internalModules Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      (equivalence Λ X).functor.obj M ⊗ (equivalence Λ X).functor.obj N :=
  (ordinaryTensorComparison_existsUnique Λ X M N).exists.choose

/-- The total-complex comparison is uniquely determined on each direct-sum summand.
Source: Stacks 06YN (blueprint: def-pd-proetale-section-module-functors).
Proof: sum the normalized ordinary comparisons in each degree. Naturality commutes
with the two differential components, with the same sign (-1)^p. The coproduct
universal property gives uniqueness; the summed inverses give an inverse chain map. -/
theorem totalComparison_existsUnique (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    ∃! t : ((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor _)) ≅
      CochainComplex.mapBifunctor
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
        (curriedTensor _),
    ∀ (p q n : ℤ) (h : p + q = n),
      (equivalence Λ X).functor.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q n h) ≫ t.hom.f n =
        (ordinaryTensorComparison Λ X (P.X p) (Q.X q)).hom ≫
          CochainComplex.ιMapBifunctor
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
            (curriedTensor _) p q n h := by
  sorry

/-- The uniquely specified direct-sum total-complex comparison.
Source: Stacks 06YN (blueprint: def-pd-proetale-section-module-functors). -/
def totalComparison (X : Scheme.{u}) (P Q : CochainComplex (internalModules Λ X) ℤ) :=
  (totalComparison_existsUnique Λ X P Q).exists.choose

/-- Extension by zero is additive, since all its three specified factors are additive.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: its underlying maps are extension-by-zero maps of abelian sheaves; addition
is computed on each summand before sheafification. -/
@[instance] theorem extension_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extension Λ j).Additive := by
  sorry

/-- Extension by zero preserves finite limits.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: exactness of the internal open extension transfers through the two exact
equivalences, or can be checked on the unchanged underlying abelian sheaves. -/
@[instance] theorem extension_preservesFiniteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (extension Λ j) := by
  sorry

/-- Extension by zero preserves finite colimits.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: it is the left adjoint in the specified open adjunction. -/
@[instance] theorem extension_preservesFiniteColimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (extension Λ j) := by
  sorry

/-- The regular-unit comparison is uniquely specified by fixing every scalar section.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors).
Proof: the unit clause of internal_section_tensor_comparison supplies the map.
The scalar identities determine every component, hence the natural isomorphism. -/
theorem ordinaryUnitComparison_existsUnique (X : Scheme.{u}) :
    ∃! t : (equivalence Λ X).functor.obj (𝟙_ (internalModules Λ X)) ≅ 𝟙_ (modules Λ X),
      ∀ (U : X.ProEtᵒᵖ) (r : (condensedRingObj Λ X).obj.obj U), (t.hom.val.app U) r = r := by
  sorry

/-- The normalized tensor unit comparison fixes every section of the regular module.
Source: Stacks 03EK (blueprint: def-pd-proetale-section-module-functors). -/
def ordinaryUnitComparison (X : Scheme.{u}) :
    (equivalence Λ X).functor.obj (𝟙_ (internalModules Λ X)) ≅ 𝟙_ (modules Λ X) :=
  (ordinaryUnitComparison_existsUnique Λ X).exists.choose

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
