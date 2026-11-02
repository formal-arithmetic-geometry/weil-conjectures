/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfect
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModelData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FlatCondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.RingTheory.RingHom.Flat
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
import WeilConjectures.WeilObject.Sheaf.Stalk
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Direct condensed coefficient fibres at a geometric point

Source: current blueprint, def-weil-finite-coefficient-point; Bhatt--Scholze,
Example 4.1.10; Hemo--Richarz--Scholbach, Lemma 4.1
(blueprint: def-weil-finite-coefficient-point).

The four coefficient rings are used themselves. No category of coefficient-stage
representatives occurs in these constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint.Z8

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

private def continuous_scalar_coordinates
    (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    condensedScalarRing (Profinite.continuousMapRingObj.{u} T) ≃+* T :=
  (section_coordinates (Profinite.continuousMapRingSheaf T) (⊤_ Profinite.{u})).trans
    (ULift.ringEquiv.trans
      { toFun := fun f ↦ f default
        invFun := ContinuousMap.const _
        left_inv := fun f ↦ ContinuousMap.ext fun _x ↦
          congrArg f (Subsingleton.elim _ _)
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl })

private def algClosure_scalar_coordinates (ℓ : ℕ) [Fact ℓ.Prime] :
    condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ) ≃+* PadicAlgCl ℓ :=
  (section_coordinates (Profinite.padicAlgClCondensedRing ℓ) (⊤_ Profinite.{u})).trans
    { toFun := fun f ↦ f.down.val default
      invFun := Profinite.PadicAlgCl.constSectionRingHom ℓ (op (⊤_ Profinite.{u}))
      left_inv := fun f ↦ by
        apply ULift.ext
        apply Subtype.ext
        apply ContinuousMap.ext
        intro x
        exact congrArg f.down.val (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }

private theorem algClosure_scalar_properties (ℓ : ℕ) [Fact ℓ.Prime] :
    scalar_properties (Profinite.padicAlgClRingObj.{u} ℓ) := by
  let e := algClosure_scalar_coordinates.{u} ℓ
  have hf : IsField (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ)) :=
    MulEquiv.isField (Field.toIsField (PadicAlgCl ℓ)) e.toMulEquiv
  let := hf.toField
  exact ⟨inferInstance, fun S _ ↦ RingHom.Flat.of_isField hf _⟩

/-- Z8 direct coefficient evaluation at any algebraically closed point for a topological field.
The scalar ring is the field itself, via evaluation of continuous maps on the singleton.
Source: def-weil-finite-coefficient-point, field clause and geometric point calculation
(blueprint: lem-z8-geometric-field-point-api-continuous).

Proof: singleton evaluation gives the scalar ring equivalence. Every section ring is flat
over the field, so exact scalar realization and the split-cover classification give the
recorded direct point statement, independently of a finite-field base datum. -/
theorem continuousField_direct_coefficient_point
    (T : Type) [TopologicalSpace T] [Field T] [IsTopologicalRing T]
    (k : Type u) [Field k] [IsAlgClosed k] :
    IsField (condensedScalarRing (Profinite.continuousMapRingObj.{u} T)) ∧
      DirectPointStatement (Profinite.continuousMapRingObj.{u} T) k := by
  exact ⟨(continuous_scalar_coordinates T).toMulEquiv.isField (Field.toIsField T),
    direct_of_scalar_properties _ k (field_scalar_properties T)⟩

/-- Z8 direct coefficient evaluation at any algebraically closed point for the specified
finite-subextension-valued algebraic-closure coefficient ring.
Source: def-weil-finite-coefficient-point, algebraic-closure field clause
(blueprint: lem-z8-geometric-field-point-api-padic).

Proof: singleton sections of the specified condensed ring are the actual algebraic closure.
Its section rings are flat over that field. Apply exact scalar realization and the
split-cover classification, which require only that the geometric field is algebraically
closed and impose no finite-field base condition. -/
theorem padicAlgCl_direct_coefficient_point (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] :
    IsField (condensedScalarRing (Profinite.padicAlgClRingObj.{u} ℓ)) ∧
      DirectPointStatement (Profinite.padicAlgClRingObj.{u} ℓ) k := by
  exact ⟨(algClosure_scalar_coordinates ℓ).toMulEquiv.isField
      (Field.toIsField (PadicAlgCl ℓ)),
    direct_of_scalar_properties _ k (algClosure_scalar_properties ℓ)⟩

end AlgebraicGeometry.ProEtale.CondensedGeometricPoint.Z8
