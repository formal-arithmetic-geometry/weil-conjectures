/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdQbarCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldCohomologyScalarExtension
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-! # Cohomology modules of coefficient complexes

Source: Weil blueprint, `def-weil-ordinary-compact-cohomology`, order 1510,
with the four coefficient categories of `def-weil-finite-coefficient-point`, order 1509
(blueprint: def-weil-coefficient-cohomology-modules).

The generic ring-level functor is Mathlib's `DerivedCategory.homologyFunctor`.
Its value on a representing complex is ker(d)/im(d), by
`DerivedCategory.homologyFunctorFactors` and `ShortComplex.moduleCatHomologyIso`.
The first three functors below are its restrictions to the prescribed full subcategories.
For the global datum D and coefficient datum c, specialize their rings to
`Padic.coefficientExtensionRing c.l E n`, `Padic.coefficientExtensionIntegers c.l E`,
and E, respectively; the integral ideal is `Padic.coefficientExtensionIdeal c.l E 1`.
The finite-stage Qbar functor has literally the scalar-extended cohomology as object data.

## Main definitions

* `coefficientCohomologyModules`: the four functors for the fixed global coefficient datum.
* `coefficientQbarCohomology`: literal scalar-extended cohomology on a finite-stage pair.
* `coefficientCohomologyChangeStage`: the canonical identification after enlarging the stage.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Cohomology restricted to bounded complexes with finite cohomology.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientFiniteCohomology (R : Type u) [CommRing R] (i : ℤ) :
    (pointFiniteCohomology R).FullSubcategory ⥤ ModuleCat.{u} R :=
  (pointFiniteCohomology R).ι ⋙ homologyFunctor (ModuleCat.{u} R) i

/-- Cohomology restricted to bounded derived-complete complexes with finite generated
cohomology. Source: blueprint order 1510
(blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientFgCohomology (R : Type u) [CommRing R] (I : Ideal R) (i : ℤ) :
    (pointFgComplete R I).FullSubcategory ⥤ ModuleCat.{u} R :=
  (pointFgComplete R I).ι ⋙ homologyFunctor (ModuleCat.{u} R) i

/-- Cohomology restricted to bounded finite-dimensional coefficient complexes.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientFdCohomology (F : Type u) [Field F] (i : ℤ) :
    (pointFiniteDimensional F).FullSubcategory ⥤ ModuleCat.{u} F :=
  (pointFiniteDimensional F).ι ⋙ homologyFunctor (ModuleCat.{u} F) i

/-- Finite coefficient cohomology is a finite set, as required by its defining category.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules).
Proof: apply the finite-cohomology clause of the full-subcategory membership proof. -/
theorem coefficientFiniteCohomology_finite (R : Type u) [CommRing R] (i : ℤ)
    (C : (pointFiniteCohomology R).FullSubcategory) :
    Finite ((coefficientFiniteCohomology R i).obj C) := by
  exact C.property.2 i

/-- Integral coefficient cohomology is finitely generated.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules).
Proof: apply the finitely-generated-cohomology clause of full-subcategory membership. -/
theorem coefficientFgCohomology_finite (R : Type u) [CommRing R] (I : Ideal R) (i : ℤ)
    (C : (pointFgComplete R I).FullSubcategory) :
    Module.Finite R ((coefficientFgCohomology R I i).obj C) := by
  exact C.property.2.1 i

/-- Field coefficient cohomology is finite-dimensional.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules).
Proof: apply the finite-dimensional-cohomology clause of full-subcategory membership. -/
theorem coefficientFdCohomology_finite (F : Type u) [Field F] (i : ℤ)
    (C : (pointFiniteDimensional F).FullSubcategory) :
    FiniteDimensional F ((coefficientFdCohomology F i).obj C) := by
  exact C.property.2 i

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- Stagewise H^i(E,C) = Ω tensor_E H^i(C). The factors are reversed from the
blueprint's H^i(C) tensor_E Ω by the canonical tensor commutor. The map of a
morphism is cohomology of its realization, conjugated by the uniquely normalized
scalar/cohomology comparison; hence it is independent of its common-stage representative.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientQbarCohomology (i : ℤ) :
    PointFdQbar l Ω ⥤ ModuleCat.{u} Ω :=
  (pointFdQbarRealization l Ω ⋙ homologyFunctor (ModuleCat.{u} Ω) i).copyObj
    (fun X ↦ (ModuleCat.extendScalars (R := X.1.val) (S := Ω) X.1.val.subtype).obj
      ((homologyFunctor (ModuleCat.{u} X.1.val) i).obj X.2.obj))
    (fun X ↦ (fieldDerivedHomologyIso (K := X.1.val) (L := Ω) X.1.val.subtype i).app X.2.obj)

/-- The scalar-extended cohomology remains finite-dimensional over the closure.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules).
Proof: finite-dimensional cohomology at E is part of membership in D^b_fd(E).
Scalar extension preserves finite generation; over Ω this is finite dimensionality. -/
theorem coefficientQbarCohomology_finite (i : ℤ) (C : PointFdQbar l Ω) :
    FiniteDimensional Ω ((coefficientQbarCohomology l Ω i).obj C) := by
  have := (inferInstance : IsAlgClosure (Padic l) Ω)
  let : FiniteDimensional C.1.val
      ((homologyFunctor (ModuleCat.{u} C.1.val) i).obj C.2.obj) := C.2.property.2 i
  let := C.1.val.subtype.toAlgebra
  change Module.Finite Ω
    (TensorProduct C.1.val Ω ((homologyFunctor (ModuleCat.{u} C.1.val) i).obj C.2.obj))
  infer_instance

/-- On a morphism represented at one common stage, the map is exactly extension of
scalars of its ordinary cohomology map.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules).
Proof: unfold copyObj. Naturality of the normalized cohomology comparison cancels
its conjugating components, leaving scalar extension of the stage cohomology map. -/
theorem coefficientQbarCohomology_map_stage (i : ℤ)
    (E : Padic.FiniteCoefficientFields l Ω)
    {C D : (pointFiniteDimensional E.val).FullSubcategory} (f : C ⟶ D) :
    (coefficientQbarCohomology l Ω i).map ((pointFdQbarStage l Ω E).map f) =
      (ModuleCat.extendScalars (R := E.val) (S := Ω) E.val.subtype).map
        ((homologyFunctor (ModuleCat.{u} E.val) i).map f.hom) := by
  have := (inferInstance : IsAlgClosure (Padic l) Ω)
  change (fieldDerivedHomologyIso (K := E.val) (L := Ω) E.val.subtype i).inv.app C.obj ≫
      (homologyFunctor (ModuleCat.{u} Ω) i).map
        ((fieldDerivedScalarExtension (K := E.val) (L := Ω) E.val.subtype).map f.hom) ≫
      (fieldDerivedHomologyIso (K := E.val) (L := Ω) E.val.subtype i).hom.app D.obj = _
  have h := (fieldDerivedHomologyIso (K := E.val) (L := Ω) E.val.subtype i).hom.naturality
    f.hom
  dsimp only [Functor.comp_map] at h
  rw [h]
  simp

/-- The canonical identification after enlarging the finite coefficient stage:
first commute cohomology with exact scalar extension, then apply the tensor tower map.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientCohomologyChangeStage
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (C : (pointFiniteDimensional E.val).FullSubcategory) (i : ℤ) :
    (ModuleCat.extendScalars (R := L.val) (S := Ω) L.val.subtype).obj
        ((homologyFunctor (ModuleCat.{u} L.val) i).obj
          ((fieldDerivedScalarExtension (K := E.val) (L := L.val)
            (IntermediateField.inclusion h).toRingHom).obj C.obj)) ≅
      (ModuleCat.extendScalars (R := E.val) (S := Ω) E.val.subtype).obj
        ((homologyFunctor (ModuleCat.{u} E.val) i).obj C.obj) :=
  (ModuleCat.extendScalars (R := L.val) (S := Ω) L.val.subtype).mapIso
      ((fieldDerivedHomologyIso (K := E.val) (L := L.val)
        (IntermediateField.inclusion h).toRingHom i).app C.obj) ≪≫
    ((ModuleCat.extendScalarsComp (R₁ := E.val) (R₂ := L.val) (R₃ := Ω)
      (IntermediateField.inclusion h).toRingHom
      L.val.subtype).app ((homologyFunctor (ModuleCat.{u} E.val) i).obj C.obj)).symm

/-- The change-of-stage identification is the one induced by the stagewise functor.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules).
Proof: expand the functor's conjugating comparisons; compatibility of cohomology
with tensor towers identifies the result with the displayed tensor tower map. -/
theorem coefficientQbarCohomology_changeStage
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (C : (pointFiniteDimensional E.val).FullSubcategory) (i : ℤ) :
    (coefficientQbarCohomology l Ω i).mapIso ((pointFdQbarStageComp l Ω h).app C) =
      coefficientCohomologyChangeStage l Ω h C i := by
  have := (inferInstance : IsAlgClosure (Padic l) Ω)
  apply Iso.ext
  change (fieldDerivedHomologyIso (K := L.val) (L := Ω) L.val.subtype i).inv.app
      ((fieldDerivedScalarExtension (K := E.val) (L := L.val)
        (IntermediateField.inclusion h).toRingHom).obj C.obj) ≫
      (homologyFunctor (ModuleCat.{u} Ω) i).map
        (((fieldScalarTower (IntermediateField.inclusion h).toRingHom L.val.subtype).app
          C.obj).hom) ≫
      (fieldDerivedHomologyIso (K := E.val) (L := Ω) E.val.subtype i).hom.app C.obj = _
  have ht := congrArg Iso.hom
    (fieldDerivedHomologyIso_tower (IntermediateField.inclusion h).toRingHom
      L.val.subtype i C.obj)
  dsimp only [Iso.trans_hom, Functor.mapIso_hom] at ht
  erw [ht]
  simp [coefficientCohomologyChangeStage]

/-- The four cohomology functors for the exact global coefficient datum and positive
finite level of the blueprint. This tuple specializes the generic constructions,
including the derived-complete integral category for the chosen uniformizer ideal.
Source: blueprint orders 1509–1510 (blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientCohomologyModules (D : WeilConjectures.FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (n : ℕ) (_hn : 1 ≤ n) (i : ℤ) :
    ((pointFiniteCohomology (Padic.coefficientExtensionRing c.l E.val n)).FullSubcategory ⥤
      ModuleCat.{u} (Padic.coefficientExtensionRing c.l E.val n)) ×
    ((pointFgComplete (Padic.coefficientExtensionIntegers c.l E.val)
      (Padic.coefficientExtensionIdeal c.l E.val 1)).FullSubcategory ⥤
      ModuleCat.{u} (Padic.coefficientExtensionIntegers c.l E.val)) ×
    ((pointFiniteDimensional E.val).FullSubcategory ⥤ ModuleCat.{u} E.val) ×
    (PointFdQbar c.l c.Qbar ⥤ ModuleCat.{u} c.Qbar) :=
  ⟨coefficientFiniteCohomology _ i,
    coefficientFgCohomology _ (Padic.coefficientExtensionIdeal c.l E.val 1) i,
    coefficientFdCohomology E.val i, coefficientQbarCohomology c.l c.Qbar i⟩

end DerivedCategory
