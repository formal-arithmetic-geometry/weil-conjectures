/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.EtaleSumTensorTestComparison
/-!
# Canonical constant-scalar restriction for Tor-amplitude models

Source: Stacks Project, Tag 0F1M, lemma-bounded-below-tor-amplitude
(blueprint: lem-kun-tor-model-restriction).

The scalar restriction below identifies a module over the constant ring sheaf with a
module-valued sheaf, using the sheafification unit on constants. It lets the existing
ringed-site K-flat and flatness predicates use the same representative as the recorded
module-valued derived category. The representative in the theorem is fixed before the
universal quantification over pullbacks.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u uD vD

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The constant commutative coefficient ring on the small etale site.
Source: Stacks Tag 0F1M (blueprint: lem-kun-tor-model-restriction). -/
def torModelCoefficientRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology CommRingCat.{u + 1} :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- Forget commutativity of the constant coefficient sheaf.
Source: Stacks Tag 0F1M (blueprint: lem-kun-tor-model-restriction). -/
abbrev torModelRing (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology RingCat.{u + 1} :=
  (sheafCompose T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (torModelCoefficientRing Λ T)

/-- The unit from constant scalars to the constant ring sheaf.
Source: Stacks Tag 0H7J, used in 0F1M (blueprint: lem-kun-tor-model-restriction). -/
def torModelScalarUnit (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (torModelRing Λ T).obj :=
  Functor.whiskerRight
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the action to constant scalars, keeping the underlying sheaf and maps.
Source: Stacks Modules on Sites, Section 093I, and Tag 0F1M
(blueprint: lem-kun-tor-model-restriction). -/
def torModelRestriction (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (torModelRing Λ T) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M :=
    { obj :=
        { obj := fun X ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).obj X
          map := fun f ↦
            ((PresheafOfModules.restrictScalars (torModelScalarUnit Λ T)).obj M.val).map f
          map_id := fun X ↦ by ext x; simp; rfl
          map_comp := fun f g ↦ by ext x; simp; rfl }
      property := by
        apply Presheaf.isSheaf_of_isSheaf_comp T.smallEtaleTopology _
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
        exact M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((torModelScalarUnit Λ T).app X).hom).map (f.val.app X)
      naturality := fun {_ _} g ↦ by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x }
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Scalar restriction is additive, so it applies termwise to complexes.
Source: Stacks Section 093I, used in Tag 0F1M (blueprint: lem-kun-tor-model-restriction).
Proof: all maps are the original additive maps, restricted to constant scalars, so
restriction carries the pointwise sum of two maps to their pointwise sum. -/
@[instance]
theorem torModelRestriction_additive (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    (torModelRestriction Λ T).Additive := by
  constructor
  intro M N f g
  ext X x
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Forgetting commutativity identifies the two constant-ring sheafification units.
Source: Stacks Project, Modules on Sites, Section 03CV
(blueprint: lem-kun-tor-model-restriction).
Proof: compose the functorial sheafification comparison with its inverse and use
the compatibility of its unit with the forgetful functor. -/
theorem torModelScalarUnit_transport (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    torModelScalarUnit Λ T ≫ (constantModuleHomRingIso T.smallEtaleTopology Λ).inv.hom =
      toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ)) := by
  let : T.smallEtaleTopology.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification T.smallEtaleTopology _
      (FD := fun A B : CommRingCat.{u + 1} ↦ A →+* B)
      (CD := fun A : CommRingCat.{u + 1} ↦ A)
      (FE := fun A B : RingCat.{u + 1} ↦ A →+* B)
      (CE := fun A : RingCat.{u + 1} ↦ A)
  have h := sheafComposeIso_hom_fac T.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of Λ))
  change _ ≫ (constantModuleHomRingIso T.smallEtaleTopology Λ).hom.hom =
    torModelScalarUnit Λ T at h
  rw [← h, Category.assoc]
  have hi := congrArg (fun f ↦ f.hom)
    (constantModuleHomRingIso T.smallEtaleTopology Λ).hom_inv_id
  change (constantModuleHomRingIso T.smallEtaleTopology Λ).hom.hom ≫
    (constantModuleHomRingIso T.smallEtaleTopology Λ).inv.hom = 𝟙 _ at hi
  rw [hi, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction after the existing constant-coefficient realization is the identity.
Source: Stacks Project, Modules on Sites, Sections 093I and 03CV
(blueprint: lem-kun-tor-model-restriction).
The maps in both directions are the identity on sections; linearity follows from
compatibility of the constant-ring sheafification units with forgetting commutativity. -/
def torModelRealizationRestrictionIso (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) :
    Scheme.etaleSumTensorTestRealization T Λ ⋙ torModelRestriction Λ T ≅ 𝟭 _ := by
  refine NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun X ↦ ?_) ?_
    · let f : F.obj.obj X ⟶
          ((torModelRestriction Λ T).obj
            ((Scheme.etaleSumTensorTestRealization T Λ).obj F)).obj.obj X :=
        ConcreteCategory.ofHom (C := ModuleCat.{u + 1} Λ)
          (X := F.obj.obj X)
          (Y := ((torModelRestriction Λ T).obj
            ((Scheme.etaleSumTensorTestRealization T Λ).obj F)).obj.obj X)
          (show (F.obj.obj X) →ₗ[Λ]
          (((torModelRestriction Λ T).obj
            ((Scheme.etaleSumTensorTestRealization T Λ).obj F)).obj.obj X) from
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun r x ↦ by
              let h := (PresheafOfModules.toSheafify
                (toSheafify T.smallEtaleTopology
                  ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of Λ)))
                (M₀ := Scheme.etaleConstantModulePresheaf T Λ F)
                (A := (sheafCompose T.smallEtaleTopology
                  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
                (𝟙 _)).app X
              have hs := ConcreteCategory.congr_hom
                (NatTrans.congr_app (torModelScalarUnit_transport Λ T) X) r
              change r • x =
                ((constantModuleHomRingIso T.smallEtaleTopology Λ).inv.hom.app X
                  ((torModelScalarUnit Λ T).app X r)) •
                  (show ((Scheme.etaleConstantModuleFunctor T Λ).obj F).val.obj X from x)
              change (constantModuleHomRingIso T.smallEtaleTopology Λ).inv.hom.app X
                ((torModelScalarUnit Λ T).app X r) = _ at hs
              erw [hs]
              exact h.hom.map_smul r x })
      exact (LinearEquiv.toModuleIso
        { f.hom with invFun := fun x ↦ x
                     left_inv := fun _ ↦ rfl
                     right_inv := fun _ ↦ rfl }).symm
    · intro X Y g
      ext x
      rfl
  · intro F G f
    ext X x
    rfl

/-- Restricting the action to constants is an equivalence. Its inverse is the
existing constant-module realization followed by the canonical ring transport.
Source: Stacks Project, Modules on Sites, Sections 093I and 03CV
(blueprint: lem-kun-tor-model-restriction).

Proof: the displayed natural isomorphism identifies realization followed by
restriction with the identity. Realization is already an equivalence, so
cancelling it proves that restriction is an equivalence. -/
theorem torModelRestriction_isEquivalence
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    (torModelRestriction Λ T).IsEquivalence := by
  let E := Scheme.etaleSumTensorTestRealization T Λ
  let := Scheme.etaleSumTensorTestRealization_isEquivalence T Λ
  let : (E ⋙ torModelRestriction Λ T).IsEquivalence :=
    Functor.isEquivalence_of_iso (torModelRealizationRestrictionIso Λ T).symm
  exact Functor.isEquivalence_of_comp_left E (torModelRestriction Λ T)

end AlgebraicGeometry.Etale
