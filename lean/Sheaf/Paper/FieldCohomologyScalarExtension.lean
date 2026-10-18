/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.FieldDerivedScalarTower
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

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
  sorry

/-- The canonical derived cohomology comparison, uniquely normalized on complexes.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldDerivedHomologyIso (f : K →+* L) (i : ℤ) :
    fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i ≅
      homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f :=
  (existsUnique_fieldDerivedHomologyIso f i).exists.choose

/-- Tensor/cohomology comparison is compatible with the scalar tower comparison.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).
Proof: on complexes the two routes send a tensor of a cycle class to the same
class, using tensor associativity. The kernel/image universal properties give
this equality, and uniqueness of localization extends it to derived objects. -/
theorem fieldDerivedHomologyIso_tower {M : Type u} [Field M]
    (f : K →+* L) (g : L →+* M) (i : ℤ)
    (C : DerivedCategory (ModuleCat.{u} K)) :
    (homologyFunctor (ModuleCat.{u} M) i).mapIso ((fieldScalarTower f g).app C) ≪≫
        (fieldDerivedHomologyIso (g.comp f) i).app C =
      (fieldDerivedHomologyIso g i).app ((fieldDerivedScalarExtension f).obj C) ≪≫
        (ModuleCat.extendScalars g).mapIso ((fieldDerivedHomologyIso f i).app C) ≪≫
        ((ModuleCat.extendScalarsComp f g).app
          ((homologyFunctor (ModuleCat.{u} K) i).obj C)).symm := by
  sorry

/-- Scalar extension preserves finite-dimensional cohomology and quasi-isomorphisms.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).
Proof: use the canonical homology comparison. Finite dimensionality survives tensor
extension. A quasi-isomorphism is an isomorphism on every cohomology module; tensor
extension preserves those isomorphisms, and naturality gives the same property for
the map between the scalar-extended complexes. -/
theorem fieldComplexScalarExtension_properties (f : K →+* L) :
    (∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
      (∀ i : ℤ, FiniteDimensional K (C.homology i)) → ∀ i : ℤ,
        FiniteDimensional L
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
            |>.homology i)) ∧
    (∀ (C D : CochainComplex (ModuleCat.{u} K) ℤ) (g : C ⟶ D),
      QuasiIso g →
        QuasiIso
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
  sorry

end DerivedCategory
