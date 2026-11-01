/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorExistsUnique
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarUnitConstraints
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionExistence
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransport
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransport
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientGeometricNormalization

/-! # Normalized quotient tensors under the section equivalence

Source: blueprint latest, integral proper-base-change proof, paragraph (3);
Stacks 03EL, 06YY, 07A4 and 07A6
(blueprint: lem-sfb-quotient-section-tensor-normalization).

The fixed normalization data is reexported from QuotientSectionTensorData.
The proof assembles scalar tensor uniqueness, the regular unit and the section
and geometric realizations, always using the same scalar section models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The full normalized comparison assertion, for use at the actual quotient map.
All section tensors, units and counits are fixed by the recorded constructions.
In particular the scalar model has its actual sectionwise object and map functions
and its universal counit, not an arbitrary functor with isomorphic objects.
Source: Stacks 03EK, 03EL, 06YY, 07A4 and 07A6
(blueprint: lem-sfb-quotient-section-tensor-normalization). -/
def ComparisonSpec : Prop :=
  (∃! b : ∀ T : Scheme.{u}, TensorIso a T, ∀ T : Scheme.{u}, TensorNormalized a T (b T)) ∧
    ∀ b : ∀ T : Scheme.{u}, TensorIso a T,
      (∀ T : Scheme.{u}, TensorNormalized a T (b T)) →
      ∃ c : ∀ T : Scheme.{u}, ScalarSectionData a T,
        (∀ T : Scheme.{u}, ScalarSectionNormalized a T (c T)) ∧
        (∀ T : Scheme.{u}, UnitCondition a T (b T)) ∧
        (∀ T : Scheme.{u}, ∃ barB : tensor Λ T ⋙ (c T).model.T ≅
            ((c T).model.T.prod (c T).model.T) ⋙ tensor Λ' T,
          TensorSectionCondition a T (c T) (b T) barB ∧
            SectionTensorNormalized a T (c T) barB) ∧
        (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
          GeometricCondition Λ f ∧ GeometricCondition Λ' f) ∧
        ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
          (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X),
          PullNormalized a f lam →
          ∃ barLam : (c Y).model.T ⋙ derivedPullback Λ' f ≅
              derivedPullback Λ f ⋙ (c X).model.T,
            PullSectionCondition a f (c X) (c Y) lam barLam ∧
              SectionPullNormalized a f (c X) (c Y) barLam

/-- Unique normalized quotient scalar tensor and its simultaneous section realization.
Source: blueprint main-20261015, integral proper-base-change proof, paragraph (3);
Stacks Tags 03EK, 03EL, 06YY, 07A4 and 07A6
(blueprint: lem-sfb-quotient-section-tensor-normalization).

Proof:
1. Derive the strong monoidal internal scalar-extension functor. Its generic
counit square gives TensorNormalized. Flat-term K-flat resolutions and cancellation
of the computation isomorphisms prove uniqueness on each scheme, hence uniqueness
of the whole family. The generic derived oplax unit and its constraint laws give
UnitCondition for every normalized family.
2. Choose a normalized scalar section model on every scheme, once and for all.
The section tensor transport theorem gives the tensor comparison for those same
models and every normalized internal tensorator. The section pullback transport
theorem gives the scalar/pullback comparison for those same models and every
counit-normalized internal pullback comparison.
3. Identify the native geometric tensorator with the generic derived tensorator.
The existing section-derived tensor and pushpull normalization theorem supplies
the tensor, unit and counit comparison equations for both coefficient rings.
Assemble these independent assertions into ComparisonSpec. No flatness of the
coefficient map, boundedness, or exactness of quotient scalar extension is used. -/
theorem quotient_section_tensor_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules (integral l E) T)]
    [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules (finite l E n) T)] :
    ComparisonSpec (reduction l E n) := by
  classical
  let a := reduction l E n
  have ht (T : Scheme.{u}) := scalar_tensor_exists_unique a T
  refine ⟨?_, ?_⟩
  · refine ⟨fun T ↦ (ht T).choose, fun T ↦ (ht T).choose_spec.1, ?_⟩
    intro b hb
    funext T
    exact (ht T).choose_spec.2 (b T) (hb T)
  · intro b hb
    choose c hc using (fun T : Scheme.{u} ↦ scalar_section_exists a T)
    refine ⟨c, hc, ?_, ?_, ?_, ?_⟩
    · intro T
      exact scalar_unit_constraints a T (b T) (hb T)
    · intro T
      exact section_tensor_transport a T (c T) (hc T) (b T) (hb T)
    · intro X Y f
      exact ⟨geometric_normalization (Λ := integral l E) f,
        geometric_normalization (Λ := finite l E n) f⟩
    · intro X Y f lam hlam
      exact section_pull_transport a f (c X) (c Y) (hc X) (hc Y) lam hlam

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
