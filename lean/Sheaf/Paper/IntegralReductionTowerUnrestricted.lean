/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Integral reduction towers without a finite-field datum

Source: Bhatt--Scholze, Definition 3.5.2; Stacks Project, Tags 03EK and 06YY
(blueprint: def-weil-integral-reduction-tower).

The completion and its projections already have unrestricted versions. This supplies
the same reduction tower without the irrelevant global finite-field datum. The completed
coefficient sheaf is shared with the finite-field interface.
Index n means exponent n+1.
-/

@[expose] public section

set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- Modules over the actual completed coefficient sheaf, with no finite-field datum.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable abbrev integralTowerModules :=
  SheafOfModules.{max u (t + 1)} (completedIntegralCoefficientSheafUnrestricted l E Y)

/-- The standard localization for unrestricted completed coefficients.
Source: Stacks Tag 05RU (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance integralTowerHasDerivedCategory :
    HasDerivedCategory (integralTowerModules l E Y) :=
  HasDerivedCategory.standard _

set_option linter.defProp false in
/-- The canonical scalar-extension witness, with explicit standard localizations.
Source: Stacks Tag 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralReductionExistence (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l E Y n)
    (completedIntegralCommRingProjectionUnrestricted l E Y n)

/-- Ordinary scalar extension along the actual coefficient projection, fixed on
objects and maps by sectionwise tensor product followed by sheafification.
Source: Stacks Tag 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralReductionFunctor (n : ℕ) :
    integralTowerModules l E Y ⥤
      SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) :=
  (unrestrictedIntegralReductionExistence l E Y n).choose

/-- Additivity of ordinary reduction, from the scalar-extension witness.
Source: Stacks Tag 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable instance unrestrictedIntegralReductionFunctor_additive (n : ℕ) :
    (unrestrictedIntegralReductionFunctor l E Y n).Additive :=
  (unrestrictedIntegralReductionExistence l E Y n).choose_spec.choose_spec.choose_spec.choose

/-- Termwise finite reduction, before restricting the coefficient action.
Source: Stacks Tag 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable abbrev unrestrictedIntegralFiniteComplex (n : ℕ) :=
  (unrestrictedIntegralReductionFunctor l E Y n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Finite reduction, read over the completion via its limit projection.
Source: Stacks Tags 03DA and 06YY (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralComplexFunctor (n : ℕ) :=
  unrestrictedIntegralFiniteComplex l E Y n ⋙
    (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E Y n))).mapHomologicalComplex
          (ComplexShape.up ℤ)

/-- The sheafified pure tensor s⊗x in ordinary reduction. The transport is the
object equality of the scalar-extension witness, exactly as in integralTowerTensorSection.
Source: Stacks Tag 03EK (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralTensorSection (n : ℕ)
    (M : integralTowerModules l E Y)
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E Y n).obj M).val.obj U :=
  (eqToHom ((unrestrictedIntegralReductionExistence l E Y n).choose_spec.choose M).symm).val.app U
    ((CategoryTheory.toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U).hom] x))

/-- There is a unique natural transformation between consecutive reductions sending
s⊗x to ρ(s)⊗x in every degree. Thus it is the canonical transition, on all complexes.
Source: Stacks Tag 03EK; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower).
Proof: define the map on presheaf tensors by this formula. The identity π_n=ρ_nπ_(n+1)
makes it balanced and linear over the completed sheaf. Restrictions and differentials
commute with it, so sheafification gives chain maps. Applying a chain map before or
after reduction agrees on pure tensors, proving naturality. Tensor generation and
the universal property of sheafification give uniqueness in every degree, hence
uniqueness of the natural transformation. -/
theorem unrestrictedIntegralTransition_existsUnique (n : ℕ) :
    ∃! τ : unrestrictedIntegralComplexFunctor l E Y (n + 1) ⟶
      unrestrictedIntegralComplexFunctor l E Y n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ)
        (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l E Y (n + 1)).obj.obj U)
        (x : (P.X i).val.obj U),
        ((τ.app P).f i).val.app U
          (unrestrictedIntegralTensorSection l E Y (n + 1) (P.X i) U s x) =
        unrestrictedIntegralTensorSection l E Y n (P.X i) U
          ((integralCoefficientSheafTransition l E Y n).hom.app U s) x := by
  sorry

/-- The canonical natural transition, uniquely determined on sheafified pure tensors.
Source: Stacks Tag 03EK (blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralTransition (n : ℕ) :
    unrestrictedIntegralComplexFunctor l E Y (n + 1) ⟶
      unrestrictedIntegralComplexFunctor l E Y n :=
  (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose

/-- The strict reduction tower before localization, retaining its canonical transitions.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-integral-reduction-tower). -/
noncomputable def unrestrictedIntegralComplexTower
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E Y) ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ (unrestrictedIntegralComplexFunctor l E Y n).obj P)
    (fun n ↦ (unrestrictedIntegralTransition l E Y n).app P)

end WeilConjectures
