/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FlatCondensedScalarRealization
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing

/-! # The ordinary coefficient categories at a geometric point

Source: current blueprint, `def-weil-finite-coefficient-point`, all paragraphs
(blueprint: def-weil-finite-coefficient-point).

The source category is the recorded internal-module bounded constructible category.
The target categories are full subcategories of ordinary derived module categories.
Universe lifts implement the size convention and do not alter the coefficient rings.
The final descent assertion is a consequence, separate from their definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedGeometricPoint

/-- The single point of the terminal profinite set, specified without an arbitrary choice.
Source: blueprint, evaluation at the point (blueprint: def-weil-finite-coefficient-point). -/
def coefficientPoint : (⊤_ Profinite.{u}) :=
  (terminalIsTerminal.from (Profinite.of PUnit.{u + 1})) PUnit.unit

/-- Singleton evaluation identifies discrete finite coefficient scalars with A itself.
This is the existing section-coordinate map followed by evaluation at the specified point.
Source: latest blueprint def-weil-finite-coefficient-point, finite-coefficient display
(blueprint: def-weil-finite-coefficient-point). -/
def finiteDiscreteScalarCoordinates (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    condensedScalarRing (Profinite.continuousCoefficientRingObj A) ≃+*
      ULift.{u + 1, u} A :=
  by
    have : Subsingleton (⊤_ Profinite.{u}) := by
      constructor
      intro x y
      let c : (⊤_ Profinite.{u}) ⟶ (⊤_ Profinite.{u}) :=
        ConcreteCategory.ofHom ⟨fun _ ↦ x, continuous_const⟩
      exact ConcreteCategory.congr_hom (terminalIsTerminal.hom_ext c (𝟙 _)) y
    let ev : C((⊤_ Profinite.{u}), A) ≃+* A :=
      { toFun := fun f ↦ f coefficientPoint
        invFun := ContinuousMap.const _
        left_inv := fun f ↦ ContinuousMap.ext fun _x ↦
          congrArg f (Subsingleton.elim _ _)
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl }
    exact ((ringSheafSectionCoordinates (Profinite.continuousCoefficientRingSheaf A)
      (⊤_ Profinite.{u})).trans (ULift.ringEquiv.trans ev)).trans ULift.ringEquiv.symm

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

omit Λ k in
omit Λ k in
end AlgebraicGeometry.ProEtale.CondensedGeometricPoint
