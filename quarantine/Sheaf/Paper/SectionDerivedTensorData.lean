/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.ProEtaleSectionModuleFunctors
public import Sheaf.Paper.SectionModuleOperationsData
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Sheaf.Algebra.Homology.KFlatModuleObject
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ProjectionMateExact


/-! # Canonical derived section-module tensor data

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pd-section-derived-tensor-data).

## Main definitions

- `derivedEquivalence`: localization of the fixed termwise section equivalence.
- `derivedPullback`, `derivedPushforward`: the actual ringed derived operations.
- `tensor`, `tensorUnit`, `tensorComparison`: normalized conjugate K-flat tensor data.
- `totalTensor`: the signed direct-sum total of the ordinary relative tensor.
- `localizedTotalComparison`: the specified total comparison after localization.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- Read the source functor of the specified comparison without re-inferring its
large derived-functor instance arguments. This returns the actual source itself.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def comparisonSource {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} (_e : F ≅ G) : C ⥤ D := F

/-- Countable coproducts supply the internal graded tensor in every degree.
Source: Stacks 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: the degree-n index consists of pairs of integers with sum n, hence is
countable. The internal Grothendieck module category has this coproduct. -/
@[instance] theorem internal_hasGradedTensor (X : Scheme.{u})
    (P Q : GradedObject ℤ (internalModules Λ X)) : GradedObject.HasTensor P Q := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Countable coproducts supply the section-module graded tensor in every degree.
Source: Stacks 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: use the coproduct over integer pairs of fixed total degree, whose existence
transfers through the fixed section-module equivalence. -/
@[instance] theorem section_hasGradedTensor (X : Scheme.{u})
    (P Q : GradedObject ℤ (modules Λ X)) : GradedObject.HasTensor P Q := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- The internal signed sum-total of two unbounded cochain complexes exists.
Source: Stacks 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: in each degree take the countable coproduct of relative tensor summands.
The two differential components, with the sign on the second, give its total. -/
@[instance] theorem internal_hasCochainTotal (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    CochainComplex.HasMapBifunctor P Q (curriedTensor (internalModules Λ X)) := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- The section-module signed sum-total of two unbounded cochain complexes exists.
Source: Stacks 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: use the section-module countable coproducts over pairs of fixed degree;
the standard signed differential is the one of the existing total construction. -/
@[instance] theorem section_hasCochainTotal (X : Scheme.{u})
    (P Q : CochainComplex (modules Λ X) ℤ) :
    CochainComplex.HasMapBifunctor P Q (curriedTensor (modules Λ X)) := by
  infer_instance

/-- Relative tensor commutes with the countable sums defining the internal graded tensor.
Source: Stacks 03EK and 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem internal_goodTensorLeft (X : Scheme.{u})
    (P Q S : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the internal graded tensor.
Source: Stacks 03EK and 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem internal_goodTensorRight (X : Scheme.{u})
    (P Q S : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the internal graded tensor.
Source: Stacks 03EK and 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem internal_quadrupleTensorExt (X : Scheme.{u})
    (P Q S T : GradedObject ℤ (internalModules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q S T := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the section graded tensor.
Source: Stacks 03EK and 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem section_goodTensorLeft (X : Scheme.{u})
    (P Q S : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensor₁₂Tensor P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the section graded tensor.
Source: Stacks 03EK and 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem section_goodTensorRight (X : Scheme.{u})
    (P Q S : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasGoodTensorTensor₂₃ P Q S := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Relative tensor commutes with the countable sums defining the section graded tensor.
Source: Stacks 03EK and 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: a balanced bilinear map from a coproduct is a family of balanced bilinear
maps from its summands. Hence tensoring preserves each coproduct over integer
indices of fixed sum. Iterating this property gives the triple and quadruple
comparison universal properties of the existing graded tensor construction. -/
@[instance] theorem section_quadrupleTensorExt (X : Scheme.{u})
    (P Q S T : GradedObject ℤ (modules Λ X)) :
    GradedObject.HasTensor₄ObjExt P Q S T := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- The existing internal total derived pullback, with its category arguments fixed.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def internalDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (internalModules Λ Y) ⥤ DerivedCategory (internalModules Λ X) :=
  comparisonSource (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)

/-- The existing internal total derived pushforward, with its category arguments fixed.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def internalDerivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (internalModules Λ X) ⥤ DerivedCategory (internalModules Λ Y) :=
  comparisonSource (CondensedRing.rightDerivedLowerStarIso Λ f)

/-- The existing internal derived open extension, with category arguments fixed.
Source: Stacks 03DJ (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def internalDerivedExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (internalModules Λ U) ⥤ DerivedCategory (internalModules Λ X) :=
  ((CondensedRing.openImmersionLowerShriek Λ j) : internalModules Λ U ⥤
    internalModules Λ X).mapDerivedCategory

/-- The localization of the fixed termwise sectionwise functor.
Source: Stacks 05RU (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def derivedFunctor (X : Scheme.{u}) :
    DerivedCategory (internalModules Λ X) ⥤ DerivedCategory (modules Λ X) :=
  (equivalence Λ X).functor.mapDerivedCategory

/-- Localizing the termwise equivalence again gives an equivalence.
Source: Stacks 05RU (blueprint: def-pd-section-derived-tensor-data).
Proof: localize the inverse and the original unit and counit; exactness preserves
quasi-isomorphisms, so the two triangle identities survive localization. -/
@[instance] theorem derivedFunctor_isEquivalence (X : Scheme.{u}) :
    (derivedFunctor Λ X).IsEquivalence := by
  change (equivalence Λ X).functor.mapDerivedCategory.IsEquivalence
  infer_instance

/-- The induced derived equivalence, with the fixed localization functor as forward functor.
Source: Stacks 05RU (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def derivedEquivalence (X : Scheme.{u}) :
    DerivedCategory (internalModules Λ X) ≌ DerivedCategory (modules Λ X) :=
  (derivedFunctor Λ X).asEquivalence

/-- Ringed-topos derived pullback, levelwise since these coefficients pull back exactly.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def derivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (modules Λ Y) ⥤ DerivedCategory (modules Λ X) :=
  (pullback Λ f).mapDerivedCategory

/-- K-injective resolutions transfer through the sectionwise exact equivalence.
Source: Stacks 070H (blueprint: def-pd-section-derived-tensor-data).
Proof: a chain map from an acyclic complex is null-homotopic on one side exactly
when its underlying linear maps give that same null-homotopy on the other. Transfer
the functorial internal K-injective resolution through the equivalence. -/
@[instance] theorem section_hasKInjectiveResolutions (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (modules Λ X) := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  infer_instance

/-- Functorial flat resolutions transfer through the fixed exact tensor equivalence.
Source: Stacks 03EK and 06YU (blueprint: def-pd-section-derived-tensor-data).
Proof: conjugate the existing internal functorial flat-resolution functor by the
section equivalence, and transfer its augmentation using the counit. The existing
internal_section_tensor_comparison preserves flat objects and exactness, hence
preserves the flatness and epimorphism requirements of this resolution. -/
@[instance] theorem section_hasFunctorialFlatResolutions (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (modules Λ X) := by
  have _hderived := ‹∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)›
  classical
  let E := equivalence Λ X
  obtain ⟨_, e, _, _, _, hn, _⟩ :=
    InternalAbelianSheafModule.internal_section_tensor_comparison
      (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  have hflat (M : internalModules Λ X) (hM : ObjectProperty.flat M) :
      ObjectProperty.flat (E.functor.obj M) := by
    let i : E.functor ⋙ tensorRight (E.functor.obj M) ≅ tensorRight M ⋙ E.functor :=
      NatIso.ofComponents (fun N ↦ (e N M).symm) (by
        intro N N' f
        dsimp
        rw [← cancel_epi (e N M).hom, ← cancel_mono (e N' M).hom]
        simpa using (hn N N' M M f (𝟙 M)).symm)
    let j : tensorRight (E.functor.obj M) ≅ E.inverse ⋙ tensorRight M ⋙ E.functor :=
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse i
    have := hM.tensorRight.preservesFiniteLimits
    have := hM.tensorRight.preservesFiniteColimits
    have hright : exactFunctor _ _ (tensorRight (E.functor.obj M)) :=
      (exactFunctor _ _).prop_of_iso j.symm
        ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight (E.functor.obj M)).symm hright, hright⟩
  obtain ⟨L⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution (internalModules Λ X))
  let T := E.inverse ⋙ L.F ⋙ ObjectProperty.flat.ι ⋙ E.functor
  let π : T ⟶ 𝟭 (modules Λ X) :=
    Functor.whiskerLeft E.inverse (Functor.whiskerRight L.π E.functor) ≫ E.counitIso.hom
  refine ⟨{ F := ObjectProperty.lift _ T (fun M ↦ hflat _ (L.F.obj (E.inverse.obj M)).property)
            π := π
            epi_π_app := ?_ }⟩
  intro M
  dsimp [π]
  infer_instance

/-- Actual K-injective derived ringed-site direct image.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-tensor-data). -/
@[implicit_reducible]
def derivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (modules Λ X) ⥤ DerivedCategory (modules Λ Y) :=
  (pushforward Λ f).rightDerivedFunctor

/-- The canonical sectionwise derived tensor, constructed by exact equivalence transport.
Its K-flat representative characterization is stated below, so this construction uses
precisely the ordinary sectionwise derived tensor, with no arbitrary bifunctor choice.
Source: Stacks 06YU (blueprint: def-pd-section-derived-tensor-data). -/
def tensor (X : Scheme.{u}) :
    DerivedCategory (modules Λ X) × DerivedCategory (modules Λ X) ⥤
      DerivedCategory (modules Λ X) :=
  ((derivedEquivalence Λ X).inverse.prod (derivedEquivalence Λ X).inverse) ⋙
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ (derivedEquivalence Λ X).functor

/-- The tensor unit in the transported K-flat tensor model.
Source: Stacks 06YU (blueprint: def-pd-section-derived-tensor-data). -/
def tensorUnit (X : Scheme.{u}) : DerivedCategory (modules Λ X) :=
  ((derivedEquivalence Λ X).functor).obj (𝟙_ (DerivedCategory (internalModules Λ X)))

/-- The tensor comparison is uniquely specified by the equivalence unit.
Source: Stacks 06YU (blueprint: def-pd-section-derived-tensor-data).
Proof: apply the derived equivalence to the tensor of its unit isomorphisms.
Naturality is the tensor of the two unit naturality equations. -/
theorem tensorComparison_existsUnique (X : Scheme.{u}) :
    ∃! t : Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ (derivedEquivalence Λ
      X).functor ≅
        (((derivedEquivalence Λ X).functor).prod ((derivedEquivalence Λ X).functor)) ⋙ tensor Λ X,
      ∀ M N : DerivedCategory (internalModules Λ X),
        t.hom.app (M, N) = ((derivedEquivalence Λ X).functor).map
          (((CondensedRing.derivedTensor Λ X).map
            ((derivedEquivalence Λ X).unitIso.hom.app M)).app N ≫
              ((CondensedRing.derivedTensor Λ X).obj
                ((derivedEquivalence Λ X).inverse.obj (((derivedEquivalence Λ X).functor).obj
      M))).map
                  ((derivedEquivalence Λ X).unitIso.hom.app N)) := by
  let E := derivedEquivalence Λ X
  let B := Functor.uncurry.obj (CondensedRing.derivedTensor Λ X)
  let t : B ⋙ E.functor ≅ E.functor.prod E.functor ⋙ tensor Λ X :=
    Functor.isoWhiskerRight (NatIso.prod E.unitIso E.unitIso) (B ⋙ E.functor)
  refine ⟨t, ?_, ?_⟩
  · intro M N
    rfl
  · intro s hs
    apply Iso.ext
    apply NatTrans.ext
    funext ⟨M, N⟩
    exact hs M N

/-- The tensor comparison selected by its unique equivalence-unit normalization.
Source: Stacks 06YU (blueprint: def-pd-section-derived-tensor-data). -/
def tensorComparison (X : Scheme.{u}) :
    Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ (derivedEquivalence Λ X).functor ≅
      ((derivedEquivalence Λ X).functor.prod (derivedEquivalence Λ X).functor) ⋙ tensor Λ X :=
  (tensorComparison_existsUnique Λ X).exists.choose

/-- The sectionwise tensor of cochain complexes is the signed direct-sum total.
Source: Stacks 06YN (blueprint: def-pd-section-derived-tensor-data). -/
def totalTensor (X : Scheme.{u}) :
    CochainComplex (modules Λ X) ℤ × CochainComplex (modules Λ X) ℤ ⥤
      CochainComplex (modules Λ X) ℤ :=
  Functor.uncurry.obj ((curriedTensor (modules Λ X)).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The functor-level signed tensor is the same object-level signed direct-sum total.
Source: Stacks 06YN (blueprint: def-pd-section-derived-tensor-data).
Proof: unfold totalTensor, Functor.uncurry and map₂HomologicalComplex. Its object
is exactly the total complex mapBifunctor with the up-integer total shape. -/
theorem totalTensor_obj (X : Scheme.{u}) (P Q : CochainComplex (modules Λ X) ℤ) :
    (totalTensor Λ X).obj (P, Q) =
      CochainComplex.mapBifunctor P Q (curriedTensor (modules Λ X)) := by
  rfl

/-- The specified localization comparison of the fixed termwise section equivalence.
Source: Stacks 05RU and 06YU (blueprint: def-pd-section-derived-tensor-data). -/
def sectionLocalizationComparison (X : Scheme.{u})
    (P : CochainComplex (internalModules Λ X) ℤ) :
    (derivedEquivalence Λ X).functor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (equivalence Λ X).functor.mapDerivedCategoryFactors.app P

/-- The fixed ordinary total comparison localized after the section factor map.
Source: Stacks 06YU (blueprint: def-pd-section-derived-tensor-data). -/
def localizedTotalComparison (X : Scheme.{u})
    (P Q : CochainComplex (internalModules Λ X) ℤ) :
    (derivedEquivalence Λ X).functor.obj
        ((DerivedCategory.Q (C := internalModules Λ X)).obj
          (CochainComplex.mapBifunctor P Q (curriedTensor (internalModules Λ X)))) ⟶
      (DerivedCategory.Q (C := modules Λ X)).obj
        ((totalTensor Λ X).obj
          ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
            (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))) :=
  (sectionLocalizationComparison Λ X
      (CochainComplex.mapBifunctor P Q (curriedTensor (internalModules Λ X)))).hom ≫
    (DerivedCategory.Q (C := modules Λ X)).map (totalComparison Λ X P Q).hom ≫
    (DerivedCategory.Q (C := modules Λ X)).map
      (eqToHom (totalTensor_obj Λ X
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)).symm)

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
