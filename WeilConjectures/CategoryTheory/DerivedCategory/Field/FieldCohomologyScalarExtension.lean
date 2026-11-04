/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Cohomology and exact scalar extension

Source: Stacks Project, Algebra, Tag 00H9; Homology, Tags 010N and 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).

## Main definitions and statements

* `fieldComplexHomologyIso`: the canonical exact scalar/cohomology comparison on complexes.
* `fieldDerivedHomologyIso`: its uniquely normalized localization lift.
* `fieldDerivedHomologyIso_tower`: compatibility with tensor towers.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {K L : Type u} [Field K] [Field L]

/-- The canonical map on cohomology of complexes, in the direction from the tensored
complex to the tensor of its cohomology. Its inverse sends a tensor of a cycle class
to the class of that tensor. It is already an isomorphism by exactness.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldComplexHomologyIso (f : K →+* L) (i : ℤ) :
    (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} L) (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (ComplexShape.up ℤ) i ⋙
        ModuleCat.extendScalars f :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.homologyFunctorIso (ModuleCat.extendScalars f))

/-- The prescribed component of the derived cohomology comparison.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldDerivedHomologyComponent (f : K →+* L) (i : ℤ)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (homologyFunctor (ModuleCat.{u} L) i).obj
        ((fieldDerivedScalarExtension f).obj (DerivedCategory.Q.obj C)) ≅
      (ModuleCat.extendScalars f).obj
        ((homologyFunctor (ModuleCat.{u} K) i).obj (DerivedCategory.Q.obj C)) :=
  (homologyFunctor (ModuleCat.{u} L) i).mapIso
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app C) ≪≫
    (homologyFunctorFactors (ModuleCat.{u} L) i).app _ ≪≫
    (fieldComplexHomologyIso f i).app C ≪≫
    (ModuleCat.extendScalars f).mapIso
      ((homologyFunctorFactors (ModuleCat.{u} K) i).app C).symm

/-- The natural cohomology comparison descends uniquely through localization.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).
Proof: the complex-level comparison is natural by the kernel/image universal
properties and is unchanged by quasi-isomorphisms. Descend it along Q. Its values
on Q C are prescribed and Q is essentially surjective, so this lift is unique. -/
theorem existsUnique_fieldDerivedHomologyIso (f : K →+* L) (i : ℤ) :
    ∃! e : fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i ≅
        homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f,
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldDerivedHomologyComponent f i C := by
  let e₀ : DerivedCategory.Q ⋙
      (fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i) ≅
      DerivedCategory.Q ⋙
        (homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.extendScalars f).mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (homologyFunctorFactors (ModuleCat.{u} L) i) ≪≫
      fieldComplexHomologyIso f i ≪≫
      Functor.isoWhiskerRight (homologyFunctorFactors (ModuleCat.{u} K) i).symm _ ≪≫
      Functor.associator _ _ _
  let h := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := ModuleCat.{u} K))
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ)) (ModuleCat.{u} L)
  refine ⟨h.preimageIso e₀, ?_, ?_⟩
  · intro C
    apply Iso.ext
    exact congr_app (h.map_preimage e₀.hom) C
  · intro e he
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    exact congrArg Iso.hom (he C) |>.trans (congr_app (h.map_preimage e₀.hom) C).symm

/-- The canonical derived cohomology comparison, uniquely normalized on complexes.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldDerivedHomologyIso (f : K →+* L) (i : ℤ) :
    fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i ≅
      homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f :=
  (existsUnique_fieldDerivedHomologyIso f i).exists.choose

end DerivedCategory
