/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.LocalizingClosure
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Ring.NegOnePow
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.CompletedConstantSheafReduction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent
import Sheaf.Paper.CartesianCoefficients

/-!
# Scalar cohomology models for locally perfect complexes and their duals

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-internal-hom.proof.md,
paragraphs 2--3; Stacks Tags 093J, 093M, 08JB, 08JH, 08JJ
(blueprint: lem-sfb-internal-hom-dual-constructible-models).

The result is expressed for each of the six admissible coefficients. The auxiliary
predicate expands the same assertion for each coefficient without replacing the
specified scalar-extension functor by an arbitrary functor hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.InternalHomDualModels

variable {R : Type u} [CommRing R]

/-- The signed scalar dual differential: phi maps to -(-1)^i phi d_F.
Source: Stacks Tag 08JJ, ordinary dual complex
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def scalarDualDifferential (F : CochainComplex (ModuleCat.{u + 1} R) ℤ) (i j : ℤ) :
    ModuleCat.of R (Module.Dual R (F.X (-i))) ⟶
      ModuleCat.of R (Module.Dual R (F.X (-j))) :=
  ModuleCat.ofHom (-i.negOnePow • (F.d (-j) (-i)).hom.dualMap)

/-- The explicit dual differentials satisfy the complex axioms.
Source: Stacks Tag 08JJ (blueprint: lem-sfb-internal-hom-dual-constructible-models).
Proof: if i+1 is not j then -j+1 is not -i, so the original differential vanishes.
A composite is the product of two signs times precomposition with d_F d_F, hence zero.
These are the two well-definedness checks of the ordinary scalar Hom complex. -/
theorem scalarDualDifferential_laws (F : CochainComplex (ModuleCat.{u + 1} R) ℤ) :
    (∀ i j : ℤ, ¬ (ComplexShape.up ℤ).Rel i j → scalarDualDifferential F i j = 0) ∧
    (∀ i j k : ℤ, scalarDualDifferential F i j ≫ scalarDualDifferential F j k = 0) := by
  sorry

/-- The actual scalar complex Hom_R(F,R[0]), with reversed degrees and its Hom sign.
Source: Stacks Tag 08JJ (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def scalarDual (F : CochainComplex (ModuleCat.{u + 1} R) ℤ) :
    CochainComplex (ModuleCat.{u + 1} R) ℤ where
  X i := ModuleCat.of R (Module.Dual R (F.X (-i)))
  d := scalarDualDifferential F
  shape := (scalarDualDifferential_laws F).1
  d_comp_d' i j k _ _ := (scalarDualDifferential_laws F).2 i j k

/-- Additivity of the already defined scalar module functor.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models).
Proof: its map is the original additive linear map; addition is unchanged in internal
abelian-group modules. Sheafification, extension of scalars and point pullback are additive. -/
theorem scalarModules_additive (A : Type u) [CommRing A] :
    (FiniteConstantModel.scalarModules A).Additive := by
  sorry

attribute [instance] scalarModules_additive

/-- The finite-discrete coefficient model, with the discrete topology fixed in the data.
Source: blueprint admissible coefficients; Stacks Tag 093J
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def finiteModel (A : Type u) [CommRing A] (T : Scheme.{u}) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  FiniteConstantModel.modelFunctor A T

/-- Finite-discrete coefficients, with their actual continuous-function ring structure.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev finiteCoefficients (A : Type u) [CommRing A] :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  Profinite.continuousCoefficientRingObj A

/-- The integral base coefficient, lifted only to the scheme universe.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev baseIntegralCoefficients (l : ℕ) [Fact l.Prime] :=
  Profinite.continuousCoefficientRingObj (ULift.{u} ℤ_[l])

/-- Its canonical ordinary scalar model.
Source: Stacks Tags 093J, 093M
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def baseIntegralModel (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  FiniteConstantModel.modelFunctor (ULift.{u} ℤ_[l]) T

/-- The rational base coefficient, lifted only to the scheme universe.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev baseRationalCoefficients (l : ℕ) [Fact l.Prime] :=
  Profinite.continuousCoefficientRingObj (ULift.{u} ℚ_[l])

/-- Its canonical ordinary scalar model.
Source: Stacks Tag 093J
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def baseRationalModel (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  FiniteConstantModel.modelFunctor (ULift.{u} ℚ_[l]) T

/-- The algebraic-closure coefficient: all continuous functions into Qbar_l with the
topology of its l-adic absolute value, lifted only to the scheme universe. This is the
condensed ring of the topological ring Qbar_l (sk-def-sfb-condensed-ring), as fixed by the
coefficient convention of sk-def-localizing-closure; it is not the finite-subextension
colimit object.
Source: blueprint admissible coefficients
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
abbrev algebraicCoefficients (l : ℕ) [Fact l.Prime] :=
  Profinite.continuousCoefficientRingObj (ULift.{u} (PadicAlgCl l))

/-- Its canonical ordinary scalar model.
Source: Stacks Tag 093J
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def algebraicModel (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  FiniteConstantModel.modelFunctor (ULift.{u} (PadicAlgCl l)) T

/-- Commutativity of the already constructed discrete constant scalar ring.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance constantScalarsComm (A : Type u) [CommRing A] :
    IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A))) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  FiniteConstantModel.constantScalars_commutative A

/-- Termwise realization of scalar complexes preserves zero maps.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models).
Proof: the scalar module functor, sheafification and point inverse image are additive.
Relative scalar extension is a left adjoint between abelian categories, so is additive.
The resulting composite therefore preserves zero and addition. -/
theorem realization_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] (A : Type u) [CommRing A]
    (ρ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Λ) [IsMonHom ρ] (T : Scheme.{u}) :
    (FiniteConstantModel.scalarModules A ⋙
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⋙ Mod.extendScalars ρ ⋙
          (upperStarFromPoint T).mapMod Λ).Additive := by
  sorry

attribute [instance] realization_additive

/-- Additivity of the canonical continuous-coefficient model.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance continuousModelAdditive (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (T : Scheme.{u}) :
    (FiniteConstantModel.modelFunctor A T).Additive :=
  realization_additive _ A (FiniteConstantModel.scalarToContinuous A) T

/-- Additivity for finite discrete coefficients.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance finiteModelAdditive (A : Type u) [CommRing A] (T : Scheme.{u}) :
    (finiteModel A T).Additive :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  continuousModelAdditive A T

/-- Additivity for the integral base coefficient.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance baseIntegralModelAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (baseIntegralModel l T).Additive := continuousModelAdditive _ T

/-- Additivity for the rational base coefficient.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance baseRationalModelAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (baseRationalModel l T).Additive := continuousModelAdditive _ T

/-- Additivity for a finite extension's completed integral coefficient.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance integralModelAdditive (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (FiniteConstantModel.integralModel l E T).Additive :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  continuousModelAdditive _ T

/-- Additivity for finite extension field coefficients.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance rationalModelAdditive (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    (FiniteConstantModel.rationalModel l E T).Additive :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  continuousModelAdditive _ T

/-- Additivity for the continuous condensed algebraic closure.
Source: Stacks Tag 093J (blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
instance algebraicModelAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (algebraicModel l T).Additive := continuousModelAdditive _ T

/-- The two original-cover cohomology formulas, finite presentation, and membership
of both objects in Dbc. The model functor is a parameter here only to share the syntax:
the main theorem substitutes the explicit canonical functor in each coefficient case.
Source: blueprint internal-Hom stability proof, paragraphs 2--3
(blueprint: lem-sfb-internal-hom-dual-constructible-models). -/
def Assertion (A : Type u) [CommRing A]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (C : ∀ T : Scheme.{u}, ModuleCat.{u + 1} A ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    [∀ T : Scheme.{u}, (C T).Additive] (S : Scheme.{u}) : Prop :=
  ∀ (P : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)))
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S)
    (F : 𝒰.I₀ → CochainComplex (ModuleCat.{u + 1} A) ℤ),
    (∀ i : 𝒰.I₀, ∃ a b : ℤ, (F i).IsStrictlyGE a ∧ (F i).IsStrictlyLE b) →
    (∀ (i : 𝒰.I₀) (q : ℤ), Module.Finite A ((F i).X q) ∧
      Module.Projective A ((F i).X q)) →
    (∀ i : 𝒰.I₀, Nonempty
      (((CondensedRing.upperStar Λ (𝒰.f i)).mapDerivedCategory).obj P ≅
        DerivedCategory.Q.obj (((C (𝒰.X i)).mapHomologicalComplex (.up ℤ)).obj (F i)))) →
    (∀ (i : 𝒰.I₀) (q : ℤ),
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj P) ≅
          (C (𝒰.X i)).obj
            ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj (F i))) ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj
        ((DerivedCategory.homologyFunctor _ q).obj
          (((CondensedRing.derivedHom Λ S).obj (op P)).obj (𝟙_ _))) ≅
            (C (𝒰.X i)).obj
              ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj
                (scalarDual (F i)))) ∧
      Module.FinitePresentation A
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj (F i)) ∧
      Module.FinitePresentation A
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A) (.up ℤ) q).obj
          (scalarDual (F i)))) ∧
    constantModelBoundedConstructible Λ S P ∧
    constantModelBoundedConstructible Λ S
      (((CondensedRing.derivedHom Λ S).obj (op P)).obj (𝟙_ _))

/-- Constructible scalar cohomology models for all six admissible coefficient rings.
The integral sheaves are the pulled-back continuous condensed rings, including their
completed inverse-limit realization; no discrete replacement or derived completeness
condition is imposed. Bounds on each scalar complex may vary with the cover member.

Source: blueprint main-20261015, internal-Hom stability proof, paragraphs 2--3;
Stacks Tags 00FP, 093J, 093M, 08JB, 08JH, 08JJ
(blueprint: lem-sfb-internal-hom-dual-constructible-models).

Proof (the ten node steps):
1. Every admissible scalar ring is Noetherian: finite rings and fields by the ideal
criterion; integral rings by lem-weil-l-adic-extension-integers-dvr, with Z_l the base case.
2. Finite-projective duality makes the scalar dual bounded and finite projective.
Noetherian finite kernels and cokernels and finite-module finite presentation show
that both scalar cohomology modules are finitely presented; they need not be projective.
3. For finite coefficients scalar realization is the exact constant module functor
(def-sfb-site-derived-constant-module-functor and finite-discrete condensed comparison).
For field coefficients scalar exact sequences split by a basis, and realization preserves
that splitting, including for the continuous condensed algebraic closure.
4. For integral coefficients det-prop-sfb-qlbar-colimit-x-integral-limit identifies the
coefficient sheaf with the limit of constant finite quotients. Completion-flatness
(lem-weil-pbc-completed-constant-sheaf-reduction) gives exact scalar realization.
5. The strict-perfect package splits every realized term from a finite free sheaf.
Internal Hom out of a finite free sheaf is exact; its direct summand is exact as well.
6. Exact restriction commutes with derived internal Hom. On the chart, bounded
exact-term Hom takes the K-injective resolution B[0] to a quasi-isomorphic Hom complex.
Thus the dual is represented by the ordinary finite-projective dual complex.
7. The map b tensor phi to (b' tensor v to bb'phi(v)) is an isomorphism for finite free
modules and hence their retracts. Naturality respects the differential -(-1)^q phi d_F,
identifying that ordinary dual with the realization of the stated scalarDual.
8. Exact functors commute with homology, and exact restriction commutes with it too.
Apply this to F and scalarDual F to obtain both formulas on EVERY ORIGINAL chart.
9. Finite type over a field makes S Noetherian, hence qcqs. The finite affine proetale
refinement lemma gives a finite refinement of the given cover. Cartesian coefficients
restrict both models to that refinement. If S is empty use zero complexes and [0,0].
10. Take the minimum and maximum of the finitely many bounds. The dual bounds are
[-b,-a]. Local-model cohomology descent gives global bounds and constructibility on the
single stratum S, proving both Dbc memberships without changing the coefficient sheaf. -/
theorem internalHomDual_constructible_models
    (l p : ℕ) [Fact l.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hpl : p ≠ l) (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))] :
    (∀ (A : Type u) [CommRing A] [Finite A],
      (∃ n : ℕ, (l : A) ^ n = 0) →
      Assertion A (finiteCoefficients A) (finiteModel A) S) ∧
    Assertion (ULift.{u} ℤ_[l]) (baseIntegralCoefficients l) (baseIntegralModel l) S ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      Assertion (Padic.coefficientExtensionIntegers l E)
        (FiniteConstantModel.integralCoefficients l E)
        (FiniteConstantModel.integralModel l E) S) ∧
    Assertion (ULift.{u} ℚ_[l]) (baseRationalCoefficients l) (baseRationalModel l) S ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      Assertion E (FiniteConstantModel.rationalCoefficients l E)
        (FiniteConstantModel.rationalModel l E) S) ∧
    Assertion (ULift.{u} (PadicAlgCl l)) (algebraicCoefficients l)
      (algebraicModel l) S := by
  sorry

end AlgebraicGeometry.ProEtale.InternalHomDualModels
