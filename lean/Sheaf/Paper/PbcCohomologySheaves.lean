/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.Paper.PbcRationalTransport
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Cohomology sheaves and geometric fibres at a PBC coefficient stage

Source: blueprint def-weil-derived-cohomology-sheaves; Bhatt--Scholze, Section 6.8.
(blueprint: def-weil-derived-cohomology-sheaves).
The cohomology is the recorded Mathlib homology functor. Rationalization changes
its Hom groups, not its integral representative. Fibres use completed geometric
pullback and exact point sections before extension to the algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (X : Scheme.{u})

/-- The ordinary completed-module category at a finite coefficient stage.
Source: blueprint cohomology-sheaf convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
abbrev pbcStageModules (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcModules X (pbcAdicCompletion X (pbcStageDatum.{u} l Ω E))

/-- The ordinary cohomology sheaf of the actual integral representative.
Source: blueprint cohomology-sheaf convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcStageCohomology (E : Padic.FiniteCoefficientFields l Ω) (a : ℤ) :
    pbcIntegralStage l Ω X E ⥤ pbcStageModules l Ω X E :=
  pbcStageInclusion l Ω X E ⋙ DerivedCategory.homologyFunctor _ a

/-- Cohomology is additive and linear for the constant completed-coefficient action.
Source: blueprint cohomology-sheaf convention
(blueprint: def-weil-derived-cohomology-sheaves).
Proof: multiplication by a constant section is a chain endomorphism. Kernels and
images inherit that scalar action, so the induced homology map commutes with it.
The same identity holds on roofs after inverting quasi-isomorphisms. Restriction
to the full integral subcategory does not change any map or scalar action. -/
theorem pbcStageCohomology_linear (E : Padic.FiniteCoefficientFields l Ω) (a : ℤ) :
    (pbcStageCohomology l Ω X E a).Additive ∧
      (pbcStageCohomology l Ω X E a).Linear
        (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) := by
  sorry

/-- Additivity of the recorded cohomology functor.
Source: blueprint cohomology-sheaf convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
instance pbcStageCohomology_additive (E : Padic.FiniteCoefficientFields l Ω) (a : ℤ) :
    (pbcStageCohomology l Ω X E a).Additive :=
  (pbcStageCohomology_linear l Ω X E a).1

/-- Linearity of the recorded cohomology functor.
Source: blueprint cohomology-sheaf convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
instance pbcStageCohomology_linearInstance
    (E : Padic.FiniteCoefficientFields l Ω) (a : ℤ) :
    (pbcStageCohomology l Ω X E a).Linear
      (PbcIntegralRing l (pbcFiniteField.{u} l Ω E)) :=
  (pbcStageCohomology_linear l Ω X E a).2

/-- Rational module sheaves at the same coefficient stage; objects retain their lattice.
Source: blueprint cohomology-sheaf convention and Section 6.8 rationalization
(blueprint: def-weil-derived-cohomology-sheaves). -/
abbrev pbcStageRationalSheaves (E : Padic.FiniteCoefficientFields l Ω) :=
  ScalarLocalization (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcStageModules l Ω X E) (pbcStageUniformizer.{u} l Ω E)

/-- Cohomology on the rational finite stage, with the actual tensor-Hom map.
Source: blueprint cohomology-sheaf convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcRationalCohomology (E : Padic.FiniteCoefficientFields l Ω) (a : ℤ) :
    pbcStageCategory l Ω X E ⥤ pbcStageRationalSheaves l Ω X E :=
  ScalarLocalization.transport (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (pbcStageUniformizer.{u} l Ω E) (pbcStageCohomology l Ω X E a)

/-- The integral coefficient embedding into the chosen algebraic closure.
Source: blueprint finite-stage cohomology convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcFibreCoefficient (E : Padic.FiniteCoefficientFields l Ω) :
    Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E) →+* Ω :=
  (E.val.subtype.comp (Shrink.algEquiv ℚ_[l] E.val).toRingHom).comp
    (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)).subtype

/-- Geometric cohomology fibres: completed pullback, coefficient transport, point
sections, ordinary cohomology, then scalar extension to Qbar. In particular this is
not the ordinary stalk of a discrete non-torsion sheaf on the small etale site.
Source: Bhatt--Scholze 6.8; blueprint cohomology convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcStageCohomologyFibre (E : Padic.FiniteCoefficientFields l Ω)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X) (a : ℤ) :=
  pbcActualCompletedPull x (pbcStageDatum.{u} l Ω E) ⋙
    (purCoefficientModel l (pbcFiniteField.{u} l Ω E) (Spec (.of κ))).functor ⋙
    pointCompletedDerivedSections κ l (pbcFiniteField.{u} l Ω E) ⋙
    DerivedCategory.homologyFunctor _ a ⋙
    ModuleCat.extendScalars (pbcFibreCoefficient.{u} l Ω E)

/-- The scalar in Qbar associated to a localized finite-stage coefficient.
Source: blueprint rational cohomology convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcFibreFraction (E : Padic.FiniteCoefficientFields l Ω)
    (a : Localization.Away (pbcStageUniformizer.{u} l Ω E)) : Ω :=
  E.val.subtype (qbarStageFieldEquiv.{w, u} l Ω E a)

/-- The rational fibre functor is uniquely determined on unchanged objects and all
pure-tensor arrows. No choice of a fibre basis or of an unspecified functor occurs.
Source: blueprint cohomology convention and Bhatt--Scholze Section 6.8
(blueprint: def-weil-derived-cohomology-sheaves).
Proof: the completed point pullback and exact point sections are coefficient-linear.
After extension to Qbar the uniformizer is invertible. Send a tensor c tensor f to
c times the actual fibre map of f. Tensor balancing follows from coefficient
linearity. Additivity extends the formula to all arrows; bilinearity proves the
identity and composition laws. The normalization of the fraction-field equivalence
identifies its integral coefficients with the specified embedding into Qbar.
Every object is an integral representative and pure tensors generate each Hom,
so these equations also prove uniqueness. -/
theorem pbcRationalCohomologyFibre_exists
    (E : Padic.FiniteCoefficientFields l Ω) (κ : Type u)
    [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X) (a : ℤ) :
    ∃! F : pbcStageCategory l Ω X E ⥤ ModuleCat.{max (u + 1) w} Ω,
      F.Additive ∧
      (∀ K : pbcStageCategory l Ω X E,
        F.obj K = (pbcStageCohomologyFibre l Ω X E κ x a).obj K.obj.obj) ∧
      (∀ (K L : pbcIntegralStage l Ω X E)
        (c : Localization.Away (pbcStageUniformizer.{u} l Ω E)) (f : K ⟶ L),
        HEq (F.map (c • (pbcStageLocalization l Ω X E).map f))
          (pbcFibreFraction.{u} l Ω E c •
            (pbcStageCohomologyFibre l Ω X E κ x a).map
              ((pbcStageInclusion l Ω X E).map f))) := by
  sorry

/-- The uniquely fraction-normalized fibre functor at a rational coefficient stage.
Source: blueprint cohomology convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcRationalCohomologyFibre (E : Padic.FiniteCoefficientFields l Ω)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X) (a : ℤ) :
    pbcStageCategory l Ω X E ⥤ ModuleCat.{max (u + 1) w} Ω :=
  (pbcRationalCohomologyFibre_exists l Ω X E κ x a).exists.choose

variable [IsNoetherian X]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The fibre of a Qbar complex is evaluated on its displayed finite-stage lattice.
Source: blueprint cohomology convention, with the adic common-stage convention
(blueprint: def-weil-derived-cohomology-sheaves). -/
def pbcQbarCohomologyFibre (M : pbcQbarCategory l Ω X)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X) (a : ℤ) :=
  (pbcStageCohomologyFibre l Ω X M.stage κ x a).obj M.obj.obj.obj

end AlgebraicGeometry.Scheme
