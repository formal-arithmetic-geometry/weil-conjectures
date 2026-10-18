/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.FieldComplexScalarExtension

/-! # Canonical derived scalar-extension comparisons

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: lem-weil-derived-field-scalar-extension-tower).

## Main definitions and statements

* `fieldScalarTower`, `fieldScalarUnit`: the uniquely normalized tensor comparisons.
* `fieldScalarTower_assoc`, `fieldScalarTower_units`: their coherence.
* `fieldScalarTower_commShift`: compatibility with the triangulated shifts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {K L M : Type u} [Field K] [Field L] [Field M]

/-- The prescribed component of the tower comparison on a representing complex.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTowerComponent (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    ((fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g).obj
      (DerivedCategory.Q.obj C)) ≅
      (fieldDerivedScalarExtension (g.comp f)).obj (DerivedCategory.Q.obj C) :=
  (fieldDerivedScalarExtension g).mapIso
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app C) ≪≫
    (ModuleCat.extendScalars g).mapDerivedCategoryFactors.app
      ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj C) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
        (ComplexShape.up ℤ)).app C) ≪≫
    ((ModuleCat.extendScalars (g.comp f)).mapDerivedCategoryFactors.app C).symm

/-- The prescribed component of the unit comparison on a representing complex.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarUnitComponent (K : Type u) [Field K]
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldDerivedScalarExtension (RingHom.id K)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj C :=
  (ModuleCat.extendScalars (RingHom.id K)).mapDerivedCategoryFactors.app C ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId K) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (ComplexShape.up ℤ)).app C)

/-- Localization gives the unique tower comparison with these prescribed components.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: the termwise tensor tower isomorphism is natural and inverts quasi-isomorphisms.
Lift it through Q using localization. Every derived object is represented by a complex,
and precomposition with Q is fully faithful on the resulting functors, so the
prescribed components determine the lift uniquely. -/
theorem existsUnique_fieldScalarTower (f : K →+* L) (g : L →+* M) :
    ∃! e : fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
        fieldDerivedScalarExtension (g.comp f),
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldScalarTowerComponent f g C := by
  sorry

/-- Localization gives the unique unit comparison with the termwise normalization.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: lift the termwise tensor unit through Q. The localization's uniqueness and
essential surjectivity give uniqueness of the normalized natural isomorphism. -/
theorem existsUnique_fieldScalarUnit (K : Type u) [Field K] :
    ∃! e : fieldDerivedScalarExtension (RingHom.id K) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} K)),
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldScalarUnitComponent K C := by
  sorry

/-- The canonical tower comparison, selected from a uniquely determined natural isomorphism.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTower (f : K →+* L) (g : L →+* M) :
    fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
      fieldDerivedScalarExtension (g.comp f) :=
  (existsUnique_fieldScalarTower f g).exists.choose

/-- The canonical unit comparison, selected with its termwise normalization.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarUnit (K : Type u) [Field K] :
    fieldDerivedScalarExtension (RingHom.id K) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} K)) :=
  (existsUnique_fieldScalarUnit K).exists.choose

/-- Associativity of the canonical tower comparisons.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: precompose with Q and use the prescribed components. Both routes become
associativity of the ordinary tensor product (ModuleCat.extendScalars_assoc).
Localization detects equality of natural transformations. -/
theorem fieldScalarTower_assoc {N : Type u} [Field N]
    (f : K →+* L) (g : L →+* M) (h : M →+* N) :
    Functor.isoWhiskerRight (fieldScalarTower f g) (fieldDerivedScalarExtension h) ≪≫
        fieldScalarTower (g.comp f) h =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (fieldDerivedScalarExtension f) (fieldScalarTower g h) ≪≫
        fieldScalarTower f (h.comp g) := by
  sorry

/-- Unit coherence of the normalized tower comparisons.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: on representing complexes both equations are the ordinary tensor unit
identities; localization detects equality. -/
theorem fieldScalarTower_units (f : K →+* L) :
    fieldScalarTower f (RingHom.id L) =
        Functor.isoWhiskerLeft _ (fieldScalarUnit L) ≪≫ Functor.rightUnitor _ ∧
      fieldScalarTower (RingHom.id K) f =
        Functor.isoWhiskerRight (fieldScalarUnit K) _ ≪≫ Functor.leftUnitor _ := by
  sorry

/-- The normalized unit and tower comparisons commute with the exact-functor shifts.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: on Q C these are maps of the termwise tensor/shift comparisons; those
commute with shifts degree by degree, including the differential signs.
Localization detects equality, giving the stated shift compatibilities. -/
theorem fieldScalarTower_commShift (f : K →+* L) (g : L →+* M) :
    NatTrans.CommShift (fieldScalarTower f g).hom ℤ ∧
      NatTrans.CommShift (fieldScalarUnit K).hom ℤ := by
  sorry

end DerivedCategory
