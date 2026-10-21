/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.PointFdComplexes
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.LinearAlgebra.Trace
public import Sheaf.CategoryTheory.DerivedCategory.PerfectCategoricalTrace
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence

import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Sheaf.Algebra.Homology.BoundedFreeProjectiveCohomologySplitting
import Sheaf.Paper.CondensedFiniteFreeTensorExact
public import Sheaf.CategoryTheory.InternalSectionTensorComparison
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace
import Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def

/-! # Finite-dimensional realization and supertraces at a condensed coefficient point

Source: Weil blueprint, sec-zeta-weil/sk-thm-rationality/sk-thm-rationality.proof.md,
first sentence, coefficient-point comparison obligation
(blueprint: lem-zl-condensed-point-supertrace).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Internal modules over the specified pulled-back finite-subextension-valued ring.
Source: rationality proof, first sentence (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable abbrev PointCondensedModules (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (padicAlgClRingObj (Spec (.of k)) l)

/-- The exact bounded constructible full subcategory specified in the comparison.
Source: rationality proof, first sentence (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable abbrev PointCondensedCategory (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] :=
  BoundedConstructible (padicAlgClRingObj (Spec (.of k)) l)

/-- The coproducts used by finite-complex total tensor, from the existing internal
module colimit interface. No new colimit construction is chosen.
Source: rationality proof, step 7 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable instance pointSupertraceModuleColimits
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    HasColimitsOfSize.{0, 0} (PointCondensedModules k l) :=
  InternalAbelianSheafModule.comparison_internalColimits
    (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l)

/-- The existing total relative tensor structure, with its parameters fixed explicitly.
Source: rationality proof, step 7 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable instance (priority := 2000) pointSupertraceComplexMonoidal
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    MonoidalCategory (CochainComplex (PointCondensedModules k l) ℤ) :=
  CategoryTheory.Mod.monoidalCategoryCochainComplex
    (C := Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (R := padicAlgClRingObj (Spec (.of k)) l)

/-- The underlying total-tensor operation of the preceding canonical structure.
Source: rationality proof, step 7 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable instance (priority := 2000) pointSupertraceComplexMonoidalStruct
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    MonoidalCategoryStruct (CochainComplex (PointCondensedModules k l) ℤ) :=
  (pointSupertraceComplexMonoidal k l).toMonoidalCategoryStruct

/-- The existing coproduct totalization for each pair of internal complexes.
Source: rationality proof, step 7 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable instance pointSupertraceTotalExists
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (K L : CochainComplex (PointCondensedModules k l) ℤ) :
    K.HasMapBifunctor L (curriedTensor (PointCondensedModules k l)) :=
  InternalAbelianSheafModule.comparison_internalTotalExists
    (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l) K L

/-- The canonical Koszul braiding on the coefficient derived category.
Source: rationality proof, step 7 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable instance pointSupertraceSourceBraiding
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l) :
    BraidedCategory (DerivedCategory (ModuleCat.{0} E.val)) :=
  DerivedCategory.perfectTraceCanonicalBraiding (ModuleCat.{0} E.val)

/-- The canonical Koszul braiding on the internal-module derived category.
Source: rationality proof, step 7 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable instance pointSupertraceTargetBraiding
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :
    BraidedCategory (DerivedCategory (PointCondensedModules k l)) :=
  DerivedCategory.perfectTraceCanonicalBraiding (PointCondensedModules k l)

/-- A bounded finite-dimensional representative with an arbitrary basis in every degree.
The rank has finite support, including the identically zero rank.
Source: rationality proof, steps 2--4 (blueprint: lem-zl-condensed-point-supertrace). -/
structure PointSupertraceFrame (E : Type) [Field E] where
  complex : CochainComplex (ModuleCat.{0} E) ℤ
  rank : ℤ → ℕ
  basis : ∀ i : ℤ, Module.Basis (Fin (rank i)) E (complex.X i)
  bounded : ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s → rank i = 0

/-- The actual ring of sections at the geometric point, recovered from its ring object.
Source: rationality proof, step 1 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable abbrev pointSupertraceSectionRing
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime] :=
  (InternalAbelianSheafModule.sectionRingSheaf
    (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l)).obj.obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

/-- Evaluation of internal modules with the scalar identification at the geometric point.
Source: rationality proof, step 6 (blueprint: lem-zl-condensed-point-supertrace). -/
noncomputable def pointSupertraceEvaluation
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (κ : PadicAlgCl l ≃+* pointSupertraceSectionRing k l) :
    PointCondensedModules k l ⥤ ModuleCat.{u + 1} (PadicAlgCl l) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology (Spec (.of k))) (padicAlgClRingObj (Spec (.of k)) l)).functor ⋙
    SheafOfModules.evaluation _ (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⋙
    ModuleCat.restrictScalars κ.toRingHom

/-- The exact strong symmetric monoidal realization and its inherited domains.
Source: rationality proof, coefficient-point comparison
(blueprint: lem-zl-condensed-point-supertrace). -/
class CondensedPointRealizationData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) where
  [sourceMonoidal : (DerivedCategory.pointFiniteDimensional E.val).IsMonoidal]
  [targetMonoidal : (boundedConstructible (padicAlgClRingObj (Spec (.of k)) l)).IsMonoidal]
  [sourceTriangulated : (DerivedCategory.pointFiniteDimensional E.val).IsTriangulated]
  [targetTriangulated :
    (boundedConstructible (padicAlgClRingObj (Spec (.of k)) l)).IsTriangulated]
  rho : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory ⥤
    PointCondensedCategory k l

  [braided : rho.Braided]
  [additive : rho.Additive]
  [commShift : rho.CommShift ℤ]
  [exact : rho.IsTriangulated]
  source_symmetry :
    ∀ X Y : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
      (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)
  target_symmetry : ∀ X Y : PointCondensedCategory k l,
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)

attribute [instance_reducible]
  CondensedPointRealizationData.braided
  CondensedPointRealizationData.commShift

attribute [instance]
  CondensedPointRealizationData.sourceMonoidal
  CondensedPointRealizationData.targetMonoidal
  CondensedPointRealizationData.sourceTriangulated
  CondensedPointRealizationData.targetTriangulated
  CondensedPointRealizationData.braided
  CondensedPointRealizationData.additive
  CondensedPointRealizationData.commShift
  CondensedPointRealizationData.exact

/-- The actual constant scalars, their pullback and faithful action on the unit.
Source: rationality proof, coefficient-point comparison
(blueprint: lem-zl-condensed-point-supertrace). -/
class CondensedPointScalarData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E] where
  baseScalar : PadicAlgCl l →+* End
    (𝟙_ (CategoryTheory.Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.padicAlgClRingObj l)))
  baseScalar_apply : ∀ (a : PadicAlgCl l) (S : Profinite.{u}ᵒᵖ)
    (x : (Profinite.padicAlgClRingObj l).obj.obj S) (t : S.unop),
    ((((baseScalar a).hom.hom.app S) x).down.val t) = a * x.down.val t
  scalar : PadicAlgCl l →+* End (𝟙_ (PointCondensedModules k l))
  scalar_pullback : ∀ a : PadicAlgCl l, (scalar a).hom =
    (upperStarFromPoint (Spec (.of k))).map (baseScalar a).hom
  pointRingIso : PadicAlgCl l ≃+* pointSupertraceSectionRing k l
  pointRingIso_apply : ∀ a : PadicAlgCl l,
    pointRingIso a = ((scalar a).hom.hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))
        (1 : pointSupertraceSectionRing k l)
  subfieldScalar : E.val →+* End
    (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (padicSubfieldRingObj (Spec (.of k)) l E)))
  coefficient_map_scalar : ∀ a : E.val,
    (subfieldScalar a).hom ≫ padicSubfieldRingObjToPadicAlgCl (Spec (.of k)) l E =
      padicSubfieldRingObjToPadicAlgCl (Spec (.of k)) l E ≫ (scalar a.val).hom
  epsilon : E.val →+* End (𝟙_ (PointCondensedCategory k l))
  epsilon_injective : Function.Injective epsilon
  epsilon_eq : ∀ a : E.val, (epsilon a).hom =
    (DerivedCategory.singleFunctorObjUnitIso (PointCondensedModules k l)).inv ≫
      (DerivedCategory.singleFunctor (PointCondensedModules k l) 0).map (scalar a.val) ≫
      (DerivedCategory.singleFunctorObjUnitIso (PointCondensedModules k l)).hom

/-- The basis matrices, their descent, and their total-tensor normalization.
Source: rationality proof, coefficient-point comparison
(blueprint: lem-zl-condensed-point-supertrace). -/
class CondensedPointMatrixData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  frame_mem : ∀ F : PointSupertraceFrame E.val,
    DerivedCategory.pointFiniteDimensional E.val (DerivedCategory.Q.obj F.complex)
  model : PointSupertraceFrame E.val → CochainComplex (PointCondensedModules k l) ℤ
  termIso : ∀ (F : PointSupertraceFrame E.val) (i : ℤ),
    (model F).X i ≅ ⨁ (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l))
  differential_matrix : ∀ (F : PointSupertraceFrame E.val) (i j : ℤ)
    (a : Fin (F.rank i)) (b : Fin (F.rank j)),
    biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
      (termIso F i).inv ≫ (model F).d i j ≫ (termIso F j).hom ≫
      biproduct.π (fun _ : Fin (F.rank j) ↦ 𝟙_ (PointCondensedModules k l)) b =
        S.scalar ((F.basis j).repr ((F.complex.d i j).hom (F.basis i a)) b).val
  modelIso : ∀ F : PointSupertraceFrame E.val,
    (R.rho.obj ⟨DerivedCategory.Q.obj F.complex, frame_mem F⟩).obj ≅
      DerivedCategory.Q.obj (model F)
  modelMap : ∀ (F G : PointSupertraceFrame E.val),
    (F.complex ⟶ G.complex) → (model F ⟶ model G)
  chain_map_matrix : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex)
    (i : ℤ) (a : Fin (F.rank i)) (b : Fin (G.rank i)),
    biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
      (termIso F i).inv ≫ (modelMap F G f).f i ≫ (termIso G i).hom ≫
      biproduct.π (fun _ : Fin (G.rank i) ↦ 𝟙_ (PointCondensedModules k l)) b =
        S.scalar ((G.basis i).repr ((f.f i).hom (F.basis i a)) b).val
  chain_map_descent : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex),
    (R.rho.map (ObjectProperty.homMk (DerivedCategory.Q.map f))).hom ≫ (modelIso G).hom =
      (modelIso F).hom ≫ DerivedCategory.Q.map (modelMap F G f)
  quasi_iso : ∀ (F G : PointSupertraceFrame E.val) (f : F.complex ⟶ G.complex),
    QuasiIso f → IsIso (DerivedCategory.Q.map (modelMap F G f))

/-- The total-tensor comparison of the same matrix realization, normalized on pure tensors.
Source: rationality proof, step 7
(blueprint: lem-zl-condensed-point-supertrace). -/
class CondensedPointTensorModelData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E] where
  tensorModel : ∀ (F G H : PointSupertraceFrame E.val)
    (_t : F.complex ⊗ G.complex ≅ H.complex), M.model F ⊗ M.model G ≅ M.model H

/-- Normalization of the comparison on every pair of finite basis labels.
Source: rationality proof, step 7
(blueprint: lem-zl-condensed-point-supertrace). -/
def pointSupertraceTensorMatrix
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E]
    [T : CondensedPointTensorModelData k l E] : Prop :=
  ∀ (F G H : PointSupertraceFrame E.val)
    (t : F.complex ⊗ G.complex ≅ H.complex) (i j n : ℤ) (h : i + j = n)
    (a : Fin (F.rank i)) (b : Fin (G.rank j)) (c : Fin (H.rank n)),
    ((biproduct.ι (fun _ : Fin (F.rank i) ↦ 𝟙_ (PointCondensedModules k l)) a ≫
      (M.termIso F i).inv) ⊗ₘ
      (biproduct.ι (fun _ : Fin (G.rank j) ↦ 𝟙_ (PointCondensedModules k l)) b ≫
        (M.termIso G j).inv)) ≫
      CochainComplex.ιMapBifunctor (M.model F) (M.model G) (curriedTensor _) i j n h ≫
      (T.tensorModel F G H t).hom.f n ≫ (M.termIso H n).hom ≫
      biproduct.π (fun _ : Fin (H.rank n) ↦ 𝟙_ (PointCondensedModules k l)) c =
        (λ_ (𝟙_ (PointCondensedModules k l))).hom ≫ S.scalar
          ((H.basis n).repr ((t.hom.f n).hom
            ((HomologicalComplex.ιTensorObj F.complex G.complex i j n h).hom
              ((F.basis i a) ⊗ₜ[E.val] (G.basis j b)))) c).val

/-- Agreement with the canonical derived tensor and localization comparisons.
Source: rationality proof, step 7
(blueprint: lem-zl-condensed-point-supertrace). -/
def pointSupertraceTensorDescent
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E]
    [T : CondensedPointTensorModelData k l E] : Prop :=
  ∀ (F G H : PointSupertraceFrame E.val)
    (t : F.complex ⊗ G.complex ≅ H.complex),
    Functor.LaxMonoidal.μ
      (R.rho ⋙ (boundedConstructible (padicAlgClRingObj (Spec (.of k)) l)).ι)
      ⟨DerivedCategory.Q.obj F.complex, M.frame_mem F⟩
      ⟨DerivedCategory.Q.obj G.complex, M.frame_mem G⟩ ≫
      (R.rho.map (ObjectProperty.homMk
        (Functor.LaxMonoidal.μ DerivedCategory.Q F.complex G.complex ≫
          DerivedCategory.Q.map t.hom))).hom ≫ (M.modelIso H).hom =
      ((M.modelIso F).hom ⊗ₘ (M.modelIso G).hom) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q (M.model F) (M.model G) ≫
        DerivedCategory.Q.map (T.tensorModel F G H t).hom

/-- Cohomology realization and its geometric-point vector space.
Source: rationality proof, coefficient-point comparison
(blueprint: lem-zl-condensed-point-supertrace). -/
class CondensedPointCohomologyData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  cohomology_mem : ∀ (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)
    (i : ℤ), DerivedCategory.pointFiniteDimensional E.val
      ((DerivedCategory.singleFunctor (ModuleCat.{0} E.val) 0).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).obj C.obj))
  cohomologyIso : ∀ (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)
    (i : ℤ),
    (DerivedCategory.singleFunctor (PointCondensedModules k l) 0).obj
      ((DerivedCategory.homologyFunctor (PointCondensedModules k l) i).obj (R.rho.obj C).obj) ≅
    (R.rho.obj ⟨(DerivedCategory.singleFunctor (ModuleCat.{0} E.val) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).obj C.obj),
        cohomology_mem C i⟩).obj
  cohomology_evaluation :
    ∀ (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory) (i : ℤ),
    Nonempty (((pointSupertraceEvaluation k l S.pointRingIso).obj
      ((DerivedCategory.homologyFunctor (PointCondensedModules k l) i).obj (R.rho.obj C).obj))
        ≃ₗ[PadicAlgCl l] (PadicAlgCl l ⊗[E.val]
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).obj C.obj)))

/-- The actual derived dual, canonical evaluation, and transported supertrace.
Source: rationality proof, coefficient-point comparison
(blueprint: lem-zl-condensed-point-supertrace). -/
class CondensedPointDualityData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] where
  dual_mem : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    DerivedCategory.pointFiniteDimensional E.val
      ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))))
  pairing : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    ExactPairing (R.rho.obj C)
      (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))), dual_mem C⟩)
  pairing_evaluation : ∀ C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory,
    (pairing C).evaluation' =
      Functor.LaxMonoidal.μ R.rho _ C ≫ R.rho.map (ObjectProperty.homMk
        ((β_ ((ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val)))) C.obj).hom ≫
          (ihom.ev C.obj).app (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))))) ≫
        (Functor.Monoidal.εIso R.rho).inv
  conjugate_trace :
    ∀ (C : (DerivedCategory.pointFiniteDimensional E.val).FullSubcategory)
      (P : PointCondensedCategory k l) (w : P ≅ R.rho.obj C),
    ∃ ep : ExactPairing P
      (R.rho.obj ⟨(ihom C.obj).obj (𝟙_ (DerivedCategory (ModuleCat.{0} E.val))), dual_mem C⟩),
      ep.evaluation' = (𝟙 _ ⊗ₘ w.hom) ≫ (pairing C).evaluation' ∧
      ep.coevaluation' = (pairing C).coevaluation' ≫ (w.inv ⊗ₘ 𝟙 _) ∧
      ∀ (v : P ⟶ P) (f : C ⟶ C), v ≫ w.hom = w.hom ≫ R.rho.map f →
        @trace _ _ _ _ P { rightDual := _, exact := ep } v =
          S.epsilon (∑ᶠ i : ℤ, i.negOnePow • LinearMap.trace E.val
            ((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).obj C.obj)
            (((DerivedCategory.homologyFunctor (ModuleCat.{0} E.val) i).map f.hom).hom))
  unit_trace : ∃ h : HasRightDual (𝟙_ (PointCondensedCategory k l)),
    @trace _ _ _ _ _ h (𝟙 _) = S.epsilon 1


/-- All conclusions of the comparison, with the same realization and scalars shared
by its matrix, cohomology and duality clauses. These are conclusions, not assumptions.
Source: rationality proof, all eleven steps
(blueprint: lem-zl-condensed-point-supertrace). -/
structure CondensedPointSupertraceData
    (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) where
  [realization : CondensedPointRealizationData k l E]
  [scalars : CondensedPointScalarData k l E]
  [matrices : CondensedPointMatrixData k l E]
  [tensor : CondensedPointTensorModelData k l E]
  tensor_matrix : pointSupertraceTensorMatrix k l E
  tensor_descent : pointSupertraceTensorDescent k l E
  [cohomology : CondensedPointCohomologyData k l E]
  [duality : CondensedPointDualityData k l E]

/-- The finite-dimensional coefficient-point realization exists.
Source: rationality proof, realization construction
(blueprint: lem-zl-condensed-point-supertrace-realization)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_realization_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    Nonempty (CondensedPointRealizationData k l E) := by
  sorry

/-- The normalized scalar action at the coefficient point exists.
Source: rationality proof, scalar normalization
(blueprint: lem-zl-condensed-point-supertrace-scalars)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_scalar_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E] :
    Nonempty (CondensedPointScalarData k l E) := by
  sorry

/-- Matrix models compatible with the realization and scalar action exist.
Source: rationality proof, basis matrices (blueprint: lem-zl-condensed-point-supertrace-matrices)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_matrix_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] :
    Nonempty (CondensedPointMatrixData k l E) := by
  sorry

/-- A compatible total-tensor model exists.
Source: rationality proof, total tensor model
(blueprint: lem-zl-condensed-point-supertrace-tensor-model)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_tensor_model_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E] :
    Nonempty (CondensedPointTensorModelData k l E) := by
  sorry

/-- The tensor model satisfies its matrix and descent normalization equations.
Source: rationality proof, tensor normalization
(blueprint: lem-zl-condensed-point-supertrace-tensor-laws)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_tensor_compatibility
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E]
    [M : CondensedPointMatrixData k l E]
    [T : CondensedPointTensorModelData k l E] :
    pointSupertraceTensorMatrix k l E ∧ pointSupertraceTensorDescent k l E := by
  sorry

/-- The cohomology realization and evaluation comparison exist.
Source: rationality proof, cohomology comparison
(blueprint: lem-zl-condensed-point-supertrace-cohomology)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_cohomology_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] :
    Nonempty (CondensedPointCohomologyData k l E) := by
  sorry

/-- The transported duality and trace comparison exist.
Source: rationality proof, duality and trace
(blueprint: lem-zl-condensed-point-supertrace-duality)
(blueprint: lem-zl-condensed-point-supertrace).

Proof: this is the independent construction obligation in the parent proof plan.
-/
theorem condensed_point_duality_exists
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l)
    [R : CondensedPointRealizationData k l E]
    [S : CondensedPointScalarData k l E] :
    Nonempty (CondensedPointDualityData k l E) := by
  sorry

/-- The matrix realization over the actual condensed algebraic-closure coefficients exists,
and its duality and categorical trace agree with the ordinary cohomological supertrace.

Source: rationality proof, first sentence, explicit comparison obligation
(blueprint: lem-zl-condensed-point-supertrace).

Proof:
1. The geometric-field/profinite-site comparison identifies evaluation at the point
   with singleton evaluation. Finite-subextension-valued sections there equal Ω.
   Multiplication by constant scalars therefore gives an injective scalar map: apply
   H⁰ and evaluate at 1 to test a scalar endomorphism
   (lem-weil-pbc-geometric-field-proetale-evaluation).
2. Replace a finite basis by the corresponding biproduct of regular modules. Replace
   each matrix entry by scalar multiplication. Ring laws prove composition and d²=0.
   Changing bases gives D⁻¹AB and the canonical comparison matrices B,D; these compose.
3. Split cycles, boundaries and cohomology over E, since vector spaces are projective.
   Every object in the cohomologically defined domain has a bounded finite-dimensional
   representative. Bounded projective complexes compute derived maps modulo homotopy
   (lem-pc-ring-derived-map-representative, Stacks 064B).
4. Quasi-isomorphisms have homotopy inverses between these representatives. The matrix
   construction preserves homotopies, hence descends to the specified full subcategory.
5. Split a finite complex into its cohomology and contractible two-term summands
   (lem-wf-bounded-free-complex-projective-cohomology-splitting). Realization preserves that
   decomposition. Finite free modules are finitely presented and constructible on the
   single stratum. This proves bounded constructibility and the cohomology comparison.
6. Evaluate the finite free cohomology module: coordinates identify it with Ω⊗_E Hⁱ.
   The coordinate formulas are inverse and commute with every linear map and basis change.
7. The realized terms are flat (lem-weil-pbc-condensed-finite-free-tensor-exact). Transport the
   bounded-flat K-flat criterion through lem-pe-internal-section-tensor-comparison (Stacks
   06YQ). Derived tensor is ordinary total tensor here. Pair the basis labels to obtain
   the displayed tensor matrices. Associators and unitors fix labels; symmetry exchanges
   labels with the same Koszul sign. These are the coherent strong symmetric comparisons.
8. Shifts negate the same differentials and cones have the same block matrices.
   Every distinguished triangle is a cone triangle up to isomorphism, so realization
   is exact with its shift comparison (def-weil-abstract-derived-category).
9. Use the signed finite-free dual complex from lem-trf-chain-supertrace, with degree-j dual
   differential (-1)^(j+1)φd. Realize evaluation and coevaluation through the monoidal
   comparisons. Functoriality carries both triangle identities to internal module maps.
   Its derived object is RHom_E(C,E); the displayed evaluation characterizes the pairing.
10. Expand the trace using those finite matrices. The degree-i diagonal coefficient has
    sign (-1)^(-i²)=(-1)^i. The ordinary-field lem-trf-chain-supertrace and clause (4) of
    prop-trf-trace-formal-laws identify the alternating term trace with the cohomology trace.
11. Transport the pairing across w using w⁻¹ on coevaluation and w on evaluation
    (lem-trf-exact-pairing-iso-transport). The intertwining equality cancels w and w⁻¹ in the
    trace composite. Taking C=E[0], f=1 gives the unit assertion.
-/
theorem condensed_point_supertrace
    (k : Type u) [Field k] [IsAlgClosed k]
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] [CharP k p] (_hpl : p ≠ l)
    (E : PadicAlgCl.FiniteIntermediateField l) :
    Nonempty (CondensedPointSupertraceData k l E) := by
  classical
  obtain ⟨R⟩ := condensed_point_realization_exists k p l _hpl E
  letI : CondensedPointRealizationData k l E := R
  obtain ⟨S⟩ := condensed_point_scalar_exists k p l _hpl E
  letI : CondensedPointScalarData k l E := S
  obtain ⟨M⟩ := condensed_point_matrix_exists k p l _hpl E
  letI : CondensedPointMatrixData k l E := M
  obtain ⟨T⟩ := condensed_point_tensor_model_exists k p l _hpl E
  letI : CondensedPointTensorModelData k l E := T
  obtain ⟨hTM, hTD⟩ := condensed_point_tensor_compatibility k p l _hpl E
  obtain ⟨C⟩ := condensed_point_cohomology_exists k p l _hpl E
  letI : CondensedPointCohomologyData k l E := C
  obtain ⟨D⟩ := condensed_point_duality_exists k p l _hpl E
  letI : CondensedPointDualityData k l E := D
  exact ⟨hTM, hTD⟩


end AlgebraicGeometry.ProEtale
