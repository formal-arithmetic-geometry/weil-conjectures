/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement

/-! # Integer shifts of the normalized slice tensor comparison

Source: Stacks Project, more-algebra.tex, Tag 0FNH, item-shift-tensor;
sites-cohomology.tex, Tags 06YS, 06YU and 07A4. The slice squares and their
representative-independent descent are the agent-written refinement in the DAG.
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility).
-/

@[expose] public noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.checkUnivs false
set_option Elab.async true
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v u w w' a b

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open MonoidalCategory


namespace CategoryTheory

/-- The two natural integer shift comparisons of a specified tensor bifunctor.
Their normalization is stated separately on actual total-tensor representatives.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
structure TensorIntegerShiftComparisons
    {D : Type a} [Category.{b} D] [HasShift D ℤ] (B : D × D ⥤ D) where
  /-- Extract the shift in the first argument, naturally in both inputs. -/
  first : ∀ n : ℤ, (shiftFunctor D n).prod (𝟭 D) ⋙ B ≅ B ⋙ shiftFunctor D n
  /-- Extract the shift in the second argument, naturally in both inputs. -/
  second : ∀ n : ℤ, (𝟭 D).prod (shiftFunctor D n) ⋙ B ≅ B ⋙ shiftFunctor D n

set_option linter.defProp false in
@[instance_reducible]
private def cachedCompose {C : Type c} [Category.{v} C] [EssentiallySmall.{a} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{a} RingCat.{a}) := by
  exact (equivSmallModel.{a} C).hasSheafCompose J
    ((equivSmallModel.{a} C).inverse.inducedTopology J)
    (forget₂ CommRingCat.{a} RingCat.{a})

attribute [local instance 1000001] cachedCompose

private def tensorFirstShiftIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int] (n : ℤ) :
    (shiftFunctor D n).prod (𝟭 D) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun X ↦ ((T.flip.obj X.2).commShiftIso n).app X.1) (by
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
    change ((T.map (f₁⟦n⟧')).app X₂ ≫ (T.obj (Y₁⟦n⟧)).map f₂) ≫
        ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ =
      ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫
        ((T.map f₁).app X₂ ≫ (T.obj Y₁).map f₂)⟦n⟧'
    have hh := NatTrans.shift_app_comm (T.flip.map f₂) n Y₁
    change ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ ≫
      ((T.obj Y₁).map f₂)⟦n⟧' = (T.obj (Y₁⟦n⟧)).map f₂ ≫
        ((T.flip.obj Y₂).commShiftIso n).hom.app Y₁ at hh
    have h₁ := (T.flip.obj X₂).commShiftIso_hom_naturality f₁ n
    change (T.map (f₁⟦n⟧')).app X₂ ≫
        ((T.flip.obj X₂).commShiftIso n).hom.app Y₁ =
      ((T.flip.obj X₂).commShiftIso n).hom.app X₁ ≫
        ((T.map f₁).app X₂)⟦n⟧' at h₁
    rw [Category.assoc, ← hh, ← Category.assoc, h₁, Category.assoc,
      CategoryTheory.Functor.map_comp])

private def tensorSecondShiftIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int] (n : ℤ) :
    (𝟭 D).prod (shiftFunctor D n) ⋙ Functor.uncurry.obj T ≅
      Functor.uncurry.obj T ⋙ shiftFunctor D n :=
  NatIso.ofComponents (fun X ↦ ((T.obj X.1).commShiftIso n).app X.2) (by
    rintro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ ⟨f₁, f₂⟩
    change ((T.map f₁).app (X₂⟦n⟧) ≫ (T.obj Y₁).map (f₂⟦n⟧')) ≫
        ((T.obj Y₁).commShiftIso n).hom.app Y₂ =
      ((T.obj X₁).commShiftIso n).hom.app X₂ ≫
        ((T.map f₁).app X₂ ≫ (T.obj Y₁).map f₂)⟦n⟧'
    rw [Category.assoc, (T.obj Y₁).commShiftIso_hom_naturality f₂ n, ← Category.assoc,
      ← NatTrans.shift_app_comm (T.map f₁), Category.assoc, CategoryTheory.Functor.map_comp])


private theorem tensor_first_ι {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).PreservesZeroMorphisms]
    (P Q : CochainComplex D ℤ) [CochainComplex.HasMapBifunctor P Q F]
    (n p q k : ℤ) (h : p + q = k) (h' : (p + n) + q = k + n) :
    HomologicalComplex.ιMapBifunctor (P⟦n⟧) Q F (.up ℤ) p q k h ≫
      (CochainComplex.mapBifunctorShift₁Iso P Q F n).hom.f k =
      HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) (p + n) q (k + n) h' := by
  have hh := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f P Q F n
    p q k h (p + n) (k + n) rfl rfl
  change _ = (F.map (𝟙 (P.X (p + n)))).app (Q.X q) ≫
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) (p + n) q (k + n) h' ≫ 𝟙 _ at hh
  change @Eq ((F.obj (P.X (p + n))).obj (Q.X q) ⟶
    (CochainComplex.mapBifunctor P Q F).X (k + n)) _ _
  simpa only [F.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id] using hh

private theorem tensor_second_ι {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).Additive]
    (P Q : CochainComplex D ℤ) [CochainComplex.HasMapBifunctor P Q F]
    (n p q k : ℤ) (h : p + q = k) (h' : p + (q + n) = k + n) :
    HomologicalComplex.ιMapBifunctor P (Q⟦n⟧) F (.up ℤ) p q k h ≫
      (CochainComplex.mapBifunctorShift₂Iso P Q F n).hom.f k =
      (n * p).negOnePow •
        HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p (q + n) (k + n) h' := by
  have hh := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f P Q F n
    p q k h (q + n) (k + n) rfl rfl
  change _ = (p * n).negOnePow • (F.obj (P.X p)).map (𝟙 (Q.X (q + n))) ≫
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p (q + n) (k + n) h' ≫ 𝟙 _ at hh
  change @Eq ((F.obj (P.X p)).obj (Q.X (q + n)) ⟶
    (CochainComplex.mapBifunctor P Q F).X (k + n)) _ _
  simpa only [Functor.map_id, Linear.units_smul_comp, Category.id_comp,
    Category.comp_id, mul_comm] using hh


@[no_expose] private def tensor_shifts_data {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (P Q : CochainComplex D ℤ), CochainComplex.HasMapBifunctor P Q F] :
    TensorIntegerShiftComparisons (Functor.uncurry.obj F.map₂CochainComplex) :=
  ⟨tensorFirstShiftIso F.map₂CochainComplex, tensorSecondShiftIso F.map₂CochainComplex⟩

private theorem tensor_shifts_first {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (P Q : CochainComplex D ℤ), CochainComplex.HasMapBifunctor P Q F]
    (P Q : CochainComplex D ℤ) (n p q k : ℤ)
    (h : p + q = k) (h' : (p + n) + q = k + n) :
    HomologicalComplex.ιMapBifunctor (P⟦n⟧) Q F (.up ℤ) p q k h ≫
      (((tensor_shifts_data F).first n).hom.app (P, Q)).f k =
    HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) (p + n) q (k + n) h' :=
  tensor_first_ι F P Q n p q k h h'

private theorem tensor_shifts_second {D : Type*} [Category D] [Preadditive D]
    (F : D ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (P Q : CochainComplex D ℤ), CochainComplex.HasMapBifunctor P Q F]
    (P Q : CochainComplex D ℤ) (n p q k : ℤ)
    (h : p + q = k) (h' : p + (q + n) = k + n) :
    HomologicalComplex.ιMapBifunctor P (Q⟦n⟧) F (.up ℤ) p q k h ≫
      (((tensor_shifts_data F).second n).hom.app (P, Q)).f k =
    (n * p).negOnePow •
      HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) p (q + n) (k + n) h' :=
  tensor_second_ι F P Q n p q k h h'

attribute [local irreducible] tensor_shifts_data

private theorem coefficientTensorPreadditive
    {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) :
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    MonoidalPreadditive (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
  SheafOfModules.cochainModulesPreadditive R

attribute [local irreducible] SheafOfModules.monoidalCategory
  derivedInternalHomOfUniverses CoefficientClosedStructure.tensor
  Functor.mapHomologicalComplexUpToQuasiIso
  Functor.mapHomologicalComplexUpToQuasiIsoFactors

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)

omit [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}] in
private theorem tensor_section_units_smul {M N : Mod} (r : ℤˣ) (f : M ⟶ N)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    ((r • f).val.app V) x = r • (f.val.app V) x := by
  change ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ V).map
    (r • f)) x = _
  rw [Functor.map_units_smul]
  rfl

private theorem coefficient_total_exists :
    let := SheafOfModules.isMonoidal_W_independentCoefficients A
    let := SheafOfModules.monoidalCategory A
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
    ∀ (P Q : CochainComplex Mod ℤ),
      CochainComplex.HasMapBifunctor P Q (MonoidalCategory.curriedTensor Mod) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  intro P Q
  infer_instance

/-- The canonical total shifts, characterized on sheafified pure-tensor summands.
The first comparison is unsigned; the second has coefficient (-1)^(np).
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
def TotalTensorIntegerShiftFormula
    (s : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, c, v} J A)) : Prop :=
  (∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q k : ℤ) (h : p + q = k) (h' : (p + n) + q = k + n) (V : Cᵒᵖ)
    (x : (P.X (p + n)).val.obj V) (y : (Q.X q).val.obj V),
    (((s.first n).hom.app (P, Q)).f k).val.app V
      (coefficientTensorGenerator.{u, c, v} J A (P⟦n⟧) Q p q k h V x y) =
      coefficientTensorGenerator.{u, c, v} J A P Q (p + n) q (k + n) h' V x y) ∧
  (∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q k : ℤ) (h : p + q = k) (h' : p + (q + n) = k + n) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X (q + n)).val.obj V),
    (((s.second n).hom.app (P, Q)).f k).val.app V
      (coefficientTensorGenerator.{u, c, v} J A P (Q⟦n⟧) p q k h V x y) =
      (n * p).negOnePow •
        coefficientTensorGenerator.{u, c, v} J A P Q p (q + n) (k + n) h' V x y)

/-- Flat-term K-flat complexes remain so under all integer shifts, and the
canonical natural chain shift comparisons exist.

Proof: use the unsigned and signed total shifts of
lem-weil-pbc-total-tensor-integer-shifts. If E is acyclic,
Tot(E tensor P[n]) is the shift of Tot(E tensor P), hence acyclic by
def-pc-kflat-complex; shifting reindexes kernels and images and changes
differentials only by units. Terms of P[n] are terms of P, so remain flat.
The summand formulas characterize the natural comparisons in both variables.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
theorem total_tensor_integer_shift_models :
    (∀ (P : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := A) (P.X p)) →
      ∀ n : ℤ,
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (P⟦n⟧) ∧
        ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := A) ((P⟦n⟧).X p)) ∧
    ∃ s : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, c, v} J A),
      TotalTensorIntegerShiftFormula.{c, v, u} J A s := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  let := coefficientTensorPreadditive A
  have := coefficient_total_exists.{c, v, u} J A
  let F := MonoidalCategory.curriedTensor (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))
  let s := tensor_shifts_data F
  constructor
  · intro P hP fP n
    refine ⟨?_, fun p ↦ fP (p + n)⟩
    exact SheafOfModules.KFlatFixedTensor.shift_kFlat.{c, v, max c v u}
      (R := A) P hP n
  · refine ⟨s, ?_, ?_⟩
    · intro P Q n p q k h h' V x y
      let z := (((PresheafOfModules.sheafificationAdjunction.{max c v u}
        (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).obj)).unit.app
            ((P.X (p + n)).val ⊗ (Q.X q).val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X (p + n))
          (Q.X q)).inv.val).app V (x ⊗ₜ[A.obj.obj V] y))
      have hi := tensor_shifts_first F P Q n p q k h h'
      change (((HomologicalComplex.ιMapBifunctor (P⟦n⟧) Q F (.up ℤ) p q k h) ≫
        ((s.first n).hom.app (P, Q)).f k).val.app V) z =
        (HomologicalComplex.ιMapBifunctor P Q F (.up ℤ)
          (p + n) q (k + n) h').val.app V z
      exact congrArg (fun f ↦ f.val.app V z) hi
    · intro P Q n p q k h h' V x y
      let z := (((PresheafOfModules.sheafificationAdjunction.{max c v u}
        (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).obj)).unit.app
            ((P.X p).val ⊗ (Q.X (q + n)).val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p)
          (Q.X (q + n))).inv.val).app V (x ⊗ₜ[A.obj.obj V] y))
      have hi := tensor_shifts_second F P Q n p q k h h'
      change (((HomologicalComplex.ιMapBifunctor P (Q⟦n⟧) F (.up ℤ) p q k h) ≫
        ((s.second n).hom.app (P, Q)).f k).val.app V) z =
        (n * p).negOnePow •
          (HomologicalComplex.ιMapBifunctor P Q F (.up ℤ)
            p (q + n) (k + n) h').val.app V z
      exact (congrArg (fun f ↦ f.val.app V z) hi).trans
        (tensor_section_units_smul.{c, v, u} J A (n * p).negOnePow
          (HomologicalComplex.ιMapBifunctor P Q F (.up ℤ)
            p (q + n) (k + n) h') V z)

attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  SheafOfModules.forget SheafOfModules.instPreadditive
  CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

/-- The identity-on-sections shift isomorphism of actual termwise restriction.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
def sliceTensorComplexRestrictionShift (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (P : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) (n : ℤ) :
    (ringedSliceComplexRestriction.{c, v, u} J A U).obj (P⟦n⟧) ≅
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)⟦n⟧ :=
  letI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  ((SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapHomologicalComplex (.up ℤ)).commShiftIso n |>.app P

/-- The pure-tensor normalization of one chain comparison m, extracted
verbatim from RingedSliceTensorModel, without choosing an arbitrary map.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
def SliceTensorChainModelFormula (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (m : (ringedSliceComplexRestriction.{c, v, u} J A U).obj
      ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)) : Prop :=
  ∀ (p q k : ℤ) (h : p + q = k) (V : Over U)
    (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
    (m.hom.f k).val.app (op V)
      (coefficientTensorGenerator.{u, c, v} J A P Q p q k h (op V.left) x y) =
    coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q k h (op V) x y

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The canonical derived shifts are the localized chain shifts conjugated by
the recorded tensor-model isomorphisms. These equations fix their normalization.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
def DerivedTensorIntegerShiftFormula
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (s : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, c, v} J A))
    (t : TensorIntegerShiftComparisons S.tensor) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := A) (P.X p))
    (_fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := A) (Q.X p)) (n : ℤ),
    (∀ hn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (P⟦n⟧),
      (T.iso J A S (P⟦n⟧) Q hn hQ).hom ≫
        S.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 _)) ≫
        (t.first n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map ((s.first n).hom.app (P, Q)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≫
        (T.iso J A S P Q hP hQ).hom⟦n⟧') ∧
    (∀ hn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (Q⟦n⟧),
      (T.iso J A S P (Q⟦n⟧) hP hn).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 _) ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
        (t.second n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map ((s.second n).hom.app (P, Q)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≫
        (T.iso J A S P Q hP hQ).hom⟦n⟧')

/-- The two chain squares commute for every normalized flat-term K-flat pair,
including shifted pairs. The component equalities give the common value of both routes.

Proof: by total_tensor_integer_shift_models the shifted pairs are still resolving
pairs (Step 1). RingedSliceTensorModel supplies the normalized m maps on all
three pairs using lem-weil-pbc-ringed-slice-evaluation-transpose (Step 2).
In first degree p the first-variable shift is unsigned: both routes are the
same restricted pure tensor of degrees (p+n,q) (Step 3). In the second
square both routes multiply that of degrees (p,q+n) by (-1)^(np), because
restriction and the tensor comparison preserve additive inverses (Step 4).
Agreement on sheafified tensor generators and all sum inclusions implies
equality of the chain maps. This also proves the displayed component formulas.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
theorem slice_tensor_integer_shift_chain
    (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (s : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, c, v} J A))
    (sU : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over
      U)))
    (_hs : TotalTensorIntegerShiftFormula.{c, v, u} J A s)
    (_hsU : TotalTensorIntegerShiftFormula.{max c v, v, u} (J.over U) (A.over U) sU)
    (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := A) (P.X p))
    (_fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := A) (Q.X p))
    (n : ℤ)
    (m : (ringedSliceComplexRestriction.{c, v, u} J A U).obj ((coefficientTotalTensor.{u, c, v} J
      A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj (P),
        (ringedSliceComplexRestriction.{c, v, u} J A U).obj (Q)))
    (m1 : (ringedSliceComplexRestriction.{c, v, u} J A U).obj ((coefficientTotalTensor.{u, c, v} J
      A).obj (P⟦n⟧, Q)) ≅
      (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj (P⟦n⟧),
        (ringedSliceComplexRestriction.{c, v, u} J A U).obj (Q)))
    (m2 : (ringedSliceComplexRestriction.{c, v, u} J A U).obj ((coefficientTotalTensor.{u, c, v} J
      A).obj (P, Q⟦n⟧)) ≅
      (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj (P),
        (ringedSliceComplexRestriction.{c, v, u} J A U).obj (Q⟦n⟧)))
    (_hm : SliceTensorChainModelFormula.{c, v, u} J A U P Q m)
    (_hm1 : SliceTensorChainModelFormula.{c, v, u} J A U (P⟦n⟧) Q m1)
    (_hm2 : SliceTensorChainModelFormula.{c, v, u} J A U P (Q⟦n⟧) m2) :
    (m1.hom ≫
        (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).map
          (Prod.mkHom (sliceTensorComplexRestrictionShift.{c, v, u} J A U P n).hom (𝟙 _)) ≫
        (sU.first n).hom.app ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) =
      (ringedSliceComplexRestriction.{c, v, u} J A U).map ((s.first n).hom.app (P, Q)) ≫
        (sliceTensorComplexRestrictionShift.{c, v, u} J A U ((coefficientTotalTensor.{u, c, v} J
          A).obj (P, Q)) n).hom ≫
        m.hom⟦n⟧') ∧
    (m2.hom ≫
        (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).map
          (Prod.mkHom (𝟙 _) (sliceTensorComplexRestrictionShift.{c, v, u} J A U Q n).hom) ≫
        (sU.second n).hom.app ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) =
      (ringedSliceComplexRestriction.{c, v, u} J A U).map ((s.second n).hom.app (P, Q)) ≫
        (sliceTensorComplexRestrictionShift.{c, v, u} J A U ((coefficientTotalTensor.{u, c, v} J
          A).obj (P, Q)) n).hom ≫
        m.hom⟦n⟧') ∧
    (∀ (p q k : ℤ) (h : p + q = k) (h' : (p + n) + q = k + n) (V : Over U)
      (x : (P.X (p + n)).val.obj (op V.left))
      (y : (Q.X (q)).val.obj (op V.left)),
      ((m1.hom ≫
        (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).map
          (Prod.mkHom (sliceTensorComplexRestrictionShift.{c, v, u} J A U P n).hom (𝟙 _)) ≫
        (sU.first n).hom.app ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)).f k).val.app (op V)
        (coefficientTensorGenerator.{u, c, v} J A (P⟦n⟧) Q
          p q k h (op V.left) x y) =
      coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)
        (p + n) q (k + n) h' (op V) x y) ∧
    (∀ (p q k : ℤ) (h : p + q = k) (h' : p + (q + n) = k + n) (V : Over U)
      (x : (P.X (p)).val.obj (op V.left))
      (y : (Q.X (q + n)).val.obj (op V.left)),
      ((m2.hom ≫
        (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).map
          (Prod.mkHom (𝟙 _) (sliceTensorComplexRestrictionShift.{c, v, u} J A U Q n).hom) ≫
        (sU.second n).hom.app ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)).f k).val.app (op V)
        (coefficientTensorGenerator.{u, c, v} J A P (Q⟦n⟧)
          p q k h (op V.left) x y) =
      (n * p).negOnePow •
      coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)
        p (q + n) (k + n) h' (op V) x y) := by
  sorry

/-- The inherited exact-derived restriction shift, with no new choice of shifts.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
def sliceTensorDerivedRestrictionShift (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    [hU : HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (M : DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))) (n : ℤ) :
    (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (M⟦n⟧) ≅
      ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M)⟦n⟧ :=
  letI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  letI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).2.1
  letI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).2.2
  letI : HasDerivedCategory.{w'} (SheafOfModules.{max c v u}
    (((sheafCompose J
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) := hU
  ((SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapDerivedCategory.commShiftIso n).app M

/-- The normalized slice tensor comparison commutes with both derived integer
shifts, naturally in both unbounded inputs and for every normalized presentation.

Proof (Steps 5-6 of the node): choose flat-term K-flat resolutions of both
inputs by lem-pc-kflat-resolution. Apply lem-weil-pbc-derived-tensor-shift-descent
over the site and its slice to obtain the shifts characterized by the model
equations. The previous chain theorem proves both squares on every resolving
pair, with the prescribed signs. Exact restriction and its factorization
commute with shifts by lem-weil-pbc-exact-functor-derived-factorization, so
localization transports these chain squares to the displayed derived squares;
the intermediate inverse model isomorphisms cancel. The arbitrary-transformation
uniqueness clause of lem-weil-pbc-site-derived-tensor-descent extends equality
from resolving pairs to all pairs. It also makes the result independent of
resolutions, inverse quasi-isomorphisms, their words, and tensor presentations.
Source: Stacks 0FNH, item-shift-tensor, and 06YU, 07A4
(blueprint: lem-weil-pbc-slice-tensor-integer-shift-compatibility). -/
theorem slice_tensor_integer_shift_compatibility
    (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU
      (RingedSliceFlatRestriction.{c, v, u} J A U))
    (_hd : RingedSliceTensorModel.{c, v, u, w, w'} J A U S T SU TU d)
    (s : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, c, v} J A))
    (sU : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over
      U)))
    (_hs : TotalTensorIntegerShiftFormula.{c, v, u} J A s)
    (_hsU : TotalTensorIntegerShiftFormula.{max c v, v, u} (J.over U) (A.over U) sU) :
    (∃ (t : TensorIntegerShiftComparisons S.tensor)
      (tU : TensorIntegerShiftComparisons SU.tensor),
      DerivedTensorIntegerShiftFormula.{c, v, u, w} J A S T s t ∧
      DerivedTensorIntegerShiftFormula.{max c v, v, u, w'} (J.over U) (A.over U) SU TU sU tU) ∧
    ∀ (t : TensorIntegerShiftComparisons S.tensor)
      (tU : TensorIntegerShiftComparisons SU.tensor)
      (_ht : DerivedTensorIntegerShiftFormula.{c, v, u, w} J A S T s t)
      (_htU : DerivedTensorIntegerShiftFormula.{max c v, v, u, w'} (J.over U) (A.over U) SU TU sU
        tU)
      (M N : DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))) (n : ℤ),
      ((d.rho (M⟦n⟧) N).hom ≫
        SU.tensor.map (Prod.mkHom (sliceTensorDerivedRestrictionShift.{c, v, u, w, w'} J A U M
          n).hom (𝟙 _)) ≫
        (tU.first n).hom.app ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M,
          (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj N) =
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map ((t.first n).hom.app (M, N)) ≫
        (sliceTensorDerivedRestrictionShift.{c, v, u, w, w'} J A U (S.tensor.obj (M, N)) n).hom ≫
        (d.rho M N).hom⟦n⟧') ∧
      ((d.rho M (N⟦n⟧)).hom ≫
        SU.tensor.map (Prod.mkHom (𝟙 _) (sliceTensorDerivedRestrictionShift.{c, v, u, w, w'} J A U
          N n).hom) ≫
        (tU.second n).hom.app ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj M,
          (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj N) =
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map ((t.second n).hom.app (M, N)) ≫
        (sliceTensorDerivedRestrictionShift.{c, v, u, w, w'} J A U (S.tensor.obj (M, N)) n).hom ≫
        (d.rho M N).hom⟦n⟧') := by
  sorry

end CategoryTheory
