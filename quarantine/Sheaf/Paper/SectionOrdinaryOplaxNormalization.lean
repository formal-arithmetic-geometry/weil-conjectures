/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.ProEtaleSectionModuleFunctors
public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison
import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Ordinary pullback on balanced generators

Source: Stacks Project, Modules on Sites, Tags 03D7, 03EK and 03EL
(blueprint: lem-pd-section-ordinary-oplax-normalization).

The generators below are applications of the existing relative-tensor projections.
In particular, inverse-image sections range over every object of the source site;
they are not restricted to global sections or sections pulled from the target.
The scalar formulas characterize the normalized canonical ringed comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual inverse-image module before extension of scalars.
Source: Stacks 03D7 (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)

/-- The inverse-image tensor identification applied to a local balanced pure tensor.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
def normalizationInverseImageTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
    (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W) :
    ((normalizationInverseImage Λ f).obj (M ⊗ N)).X.obj.obj W :=
  ((Functor.LaxMonoidal.μ (normalizationInverseImage Λ f) M N).hom.hom.app W)
    (InternalAbelianSheafModule.comparison_internalTmul
      (Scheme.ProEt.topology X) ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y))
      ((normalizationInverseImage Λ f).obj M) ((normalizationInverseImage Λ f).obj N) W m n)

/-- The local scalar-extension generator s tensor m, using the actual coequalizer projection.
Source: Stacks 03D7 and 03EK (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
def normalizationScalarTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : internalModules Λ Y) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
    (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W) :
    ((CondensedRing.upperStar Λ f).obj M).X.obj.obj W :=
  ((Mod.extendπ (condensedPullbackHom Λ f) ((normalizationInverseImage Λ f).obj M)).hom.app W)
    (((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X) ((normalizationInverseImage Λ f).obj M).X).app W)
      (s ⊗ₜ[ℤ] m))

/-- The actual composite oplax tensor map: abelian inverse image followed by scalar extension.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInternalTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N

/-- The inverse of the actual composite oplax tensor map, supplied by its strong structure.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInternalTensorInv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :=
  (CondensedRing.monoidal_upperStar Λ f).toLaxMonoidal.μ M N

/-- The actual composite oplax unit, retaining the scalar-extension multiplication map.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInternalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.η

/-- The specified ringed-section adjunction mate tensor map.
Source: Stacks 03D7 and 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationSectionTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ Y) :=
  (pullOplax Λ f).δ M N

/-- The specified ringed-section adjunction mate unit map.
Source: Stacks 03D7 and 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullOplax Λ f).η

/-- The specified internal oplax maps are the normalized ordinary ringed comparisons.
Source: Stacks Project, Modules on Sites, Tags 03D7, 03EK and 03EL
(blueprint: lem-pd-section-ordinary-oplax-normalization).

Proof: (1) The fixed internal-section tensor comparison identifies the relative tensor,
regular unit and constraints by the identity on pure tensors. Operations transport identifies
both specified adjunctions, including unit and counit; their unit is geometric insertion followed
by insertion of 1 in scalar extension. (2) The sheaf-pushforward generator comparison identifies
the actual abelian direct-image pairing. Scalar restriction changes only its action; projecting
to the balanced tensor gives the section-module pairing, and its unit is the coefficient map.
(3) The ambient inverse-image tensor map is its specified adjunction mate. Precompose with the
balancing projection and use naturality of the adjunction unit. The extension-restriction Hom
bijection is precomposition with insertion of 1, so its tensor mate sends the inserted pair to
the tensor of the two inserted sections. The composite module adjunction therefore gives the
same mate equation. (4) Monoidal-adjunction transport through the fixed equivalences identifies
these maps with the ringed adjunction mates, hence with the canonical normalized comparison of
Tag 03EL. Its forward formula splits the leading scalar as s and 1. (5) The inverse multiplies
the two leading scalars: the inner balancing relations and outer S-balancing give well-defined
maps, and the two composites fix every pure tensor. The unit and its inverse are multiplication
and insertion of 1. Tensor and sheafification universal properties extend these identities.
(6) Both associativity paths send a triple tensor to the tensor with scalars s, 1, 1;
the two unit paths give s alpha(r) tensor m. Balancing and sheafification prove the stated
constraint equalities, and composing with inverses gives the inverse constraint equalities. -/
theorem section_ordinary_oplax_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ M N : internalModules Λ Y,
      (equivalence Λ X).functor.map (normalizationInternalTensor Λ f M N) ≫
          (ordinaryTensorComparison Λ X
            ((CondensedRing.upperStar Λ f).obj M) ((CondensedRing.upperStar Λ f).obj N)).hom ≫
          ((pullComparison Λ f).hom.app M ⊗ₘ (pullComparison Λ f).hom.app N) =
        (pullComparison Λ f).hom.app (M ⊗ N) ≫
          (pullback Λ f).map (ordinaryTensorComparison Λ Y M N).hom ≫
          normalizationSectionTensor Λ f
            ((equivalence Λ Y).functor.obj M) ((equivalence Λ Y).functor.obj N)) ∧
    ((equivalence Λ X).functor.map (normalizationInternalUnit Λ f) ≫
        (ordinaryUnitComparison Λ X).hom =
      (pullComparison Λ f).hom.app (𝟙_ (internalModules Λ Y)) ≫
        (pullback Λ f).map (ordinaryUnitComparison Λ Y).hom ≫
        normalizationSectionUnit Λ f) ∧
    (∀ (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
        (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
        (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W),
      ((normalizationInternalTensor Λ f M N).hom.hom.app W)
          (normalizationScalarTensor Λ f (M ⊗ N) W s
            (normalizationInverseImageTensor Λ f M N W m n)) =
        internalPureTensor Λ X _ _ W
          (normalizationScalarTensor Λ f M W s m)
          (normalizationScalarTensor Λ f N W 1 n)) ∧
    (∀ (M N : internalModules Λ Y) (W : X.ProEtᵒᵖ) (s t : (ring Λ X).obj.obj W)
        (m : ((normalizationInverseImage Λ f).obj M).X.obj.obj W)
        (n : ((normalizationInverseImage Λ f).obj N).X.obj.obj W),
      ((normalizationInternalTensorInv Λ f M N).hom.hom.app W)
          (internalPureTensor Λ X _ _ W
            (normalizationScalarTensor Λ f M W s m)
            (normalizationScalarTensor Λ f N W t n)) =
        normalizationScalarTensor Λ f (M ⊗ N) W (s * t)
          (normalizationInverseImageTensor Λ f M N W m n)) ∧
    (∀ (W : X.ProEtᵒᵖ) (s : (ring Λ X).obj.obj W)
        (r : ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)).obj.obj W),
      ((normalizationInternalUnit Λ f).hom.hom.app W)
          (normalizationScalarTensor Λ f (𝟙_ (internalModules Λ Y)) W s r) =
        s * (@id ((ring Λ X).obj.obj W) ((condensedPullbackHom Λ f).hom.app W r))) ∧
    (∀ M N P : modules Λ Y,
      (pullback Λ f).map (α_ M N P).hom ≫
          normalizationSectionTensor Λ f M (N ⊗ P) ≫
          (pullback Λ f).obj M ◁ normalizationSectionTensor Λ f N P =
        normalizationSectionTensor Λ f (M ⊗ N) P ≫
          normalizationSectionTensor Λ f M N ▷ (pullback Λ f).obj P ≫
          (α_ _ _ _).hom) ∧
    (∀ M : modules Λ Y,
      normalizationSectionTensor Λ f (𝟙_ (modules Λ Y)) M ≫
          normalizationSectionUnit Λ f ▷ (pullback Λ f).obj M ≫ (λ_ _).hom =
        (pullback Λ f).map (λ_ M).hom) ∧
    (∀ M : modules Λ Y,
      normalizationSectionTensor Λ f M (𝟙_ (modules Λ Y)) ≫
          (pullback Λ f).obj M ◁ normalizationSectionUnit Λ f ≫ (ρ_ _).hom =
        (pullback Λ f).map (ρ_ M).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
