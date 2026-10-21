/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.Paper.FiniteConstantModelResolution
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Module.Projective

/-!
# Exact scalar realization for admissible continuous coefficients

Source: Stacks Project, Modules on Sites, Tags 093J and 093M; blueprint main-20261015,
internal-Hom stability proof, paragraphs 2--3
(blueprint: lem-sfb-admissible-scalar-realization-exact).

The scalar realization is the existing `FiniteConstantModel.modelFunctor`. The algebraic
closure below uses all continuous functions. Universe lifts of the three standard scalar
rings carry their induced topologies and do not change their rings or sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdmissibleScalarRealization

open FiniteConstantModel

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Restrict the actual realized module sheaf to the localized site over `U`.
Source: Stacks 00Y0, localization, and 093J, constant modules
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def localizedModel (T : Scheme.{u}) (U : T.ProEt) :=
  modelFunctor A T ⋙
    InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ⋙
    SheafOfModules.overFunctor _ U

/-- Noetherian scalars, additive exact realization on all scalar modules, and the same
assertion for the actual restricted coefficient sheaf on every localized site.
Source: Stacks 093J and 093M and the field split-sequence argument
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def ScalarAssertions (T : Scheme.{u}) : Prop :=
  IsNoetherianRing A ∧ (modelFunctor A T).Additive ∧
    PreservesFiniteLimits (modelFunctor A T) ∧
    PreservesFiniteColimits (modelFunctor A T) ∧
    ∀ U : T.ProEt, (localizedModel A T U).Additive ∧
      PreservesFiniteLimits (localizedModel A T U) ∧
      PreservesFiniteColimits (localizedModel A T U)

/-- The pulled-back canonical scalar map, with domain `p_T^*` of the constant scalar ring.
The canonical `constantSchemeIso` identifies its domain with the constant ring on `T`.
Source: Stacks 093J, constant functions
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
abbrev scalarMap (T : Scheme.{u}) :
    (upperStarFromPoint T).obj
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))) ⟶
      condensedRingObj (Profinite.continuousCoefficientRingObj A) T :=
  (upperStarFromPoint T).map (scalarToContinuous A)

/-- The actual completed coefficient assertion: an isomorphism of ring sheaves with the
positive constant quotient tower, and flatness over constant scalars on all sheaf modules,
also on every localized site. Here `p` is the specified uniformizer.
Source: Stacks 093M and the integral coefficient limit comparison
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def CompletedIdentification (T : Scheme.{u}) (p : A) : Prop :=
  (∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
    Scheme.adicLisseCompletedRing T
      (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    ∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))))).app U
          (Ideal.Quotient.mk
            ((Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ^ (n + 1))
            (ULift.up a)))

/-- Flatness of the actual restricted coefficient module on every localized site.
Source: Stacks 093M and 00Y0
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def LocalizedFlatness (T : Scheme.{u}) : Prop :=
  ∀ U : T.ProEt, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    (R := (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      ((upperStarFromPoint T).obj
        ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
          (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))))).over U)
    (((InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology T)
      ((upperStarFromPoint T).obj
        ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
          (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))))).obj
      ((Mod.comap (scalarMap A T)).obj
        (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A) T)))).over U)

/-- The completed identification and exact tensor extension on all sheaf modules.
Source: Stacks 093M
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def CompletedAssertions (T : Scheme.{u}) (p : A) : Prop :=
  CompletedIdentification A T p ∧
    PreservesFiniteLimits (Mod.extendScalars (scalarMap A T)) ∧
    PreservesFiniteColimits (Mod.extendScalars (scalarMap A T)) ∧
    LocalizedFlatness A T

/-- Integral extension scalars have their spectral absolute value topology.
Source: blueprint internal-Hom proof paragraphs 2--3 and Stacks 093M
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def IntegralAssertions (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (T : Scheme.{u}) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  ScalarAssertions (Padic.coefficientExtensionIntegers ℓ E) T ∧
    ∀ π : Padic.coefficientExtensionIntegers ℓ E,
      Ideal.span ({π} : Set (Padic.coefficientExtensionIntegers ℓ E)) =
        Padic.coefficientExtensionMaximalIdeal ℓ E →
      CompletedAssertions (Padic.coefficientExtensionIntegers ℓ E) T π

/-- Rational extension scalars retain the topology of their spectral absolute value.
Source: blueprint internal-Hom proof paragraphs 2--3, field case
(blueprint: lem-sfb-admissible-scalar-realization-exact). -/
def RationalAssertions (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] (T : Scheme.{u}) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  ScalarAssertions E T

/-- All six admissible scalar realizations are additive and exact, including the continuous
algebraic closure without a finite-subextension condition. Integral coefficients are the
actual completed constant sheaf and are flat on all constant-ring module sheaves.

Source: Stacks 093J, 093M; blueprint main-20261015, internal-Hom stability proof paragraphs
2--3 (blueprint: lem-sfb-admissible-scalar-realization-exact).

Proof:
1. Evaluation on a point identifies each scalar ring with the underlying ordinary ring.
Finite rings (including zero) and fields are Noetherian; integral extension rings are DVRs,
hence PIDs and Noetherian (lem-weil-l-adic-extension-integers-dvr and
lem-weil-pbc-pid-noetherian-normal). The degree-one extension gives the integer case.
2. Constant sheafification and ordinary balanced tensor are additive, on pure tensors.
3. Apply lem-weil-pbc-finite-type-constant-exact (Stacks 093J) to an arbitrary scalar short
exact sequence. No finite-generation hypothesis on any module is used.
4. For finite discrete rings the canonical constant function map is an isomorphism, by
lem-sf-finite-discrete-normalized-encoding and
lem-sf-module-object-ordinary-coefficient-equivalence. Scalar realization is constants.
5. det-prop-sfb-qlbar-colimit-x-integral-limit identifies the actual integral coefficient
ring with the positive tower of constant uniformizer quotients. Every projection carries
a constant scalar to its residue, so the comparison respects the constant scalar map.
Any other uniformizer generates the same ideal, so the assertion covers every choice.
The same argument applies to the standard integer ring with uniformizer ell.
6. lem-weil-pbc-completed-constant-sheaf-reduction (Stacks 093M) gives flatness on all
constant-ring sheaf modules. Apply it to the constant exact sequence in step 3.
7. Every scalar sequence over each of the three fields splits by vector-space projectivity
(lem-weil-pbc-vector-space-projective). Additivity preserves its splitting, hence exactness.
This uses the actual continuous algebraic-closure coefficient ring throughout.
8. lem-sfb-coefficient-sections-localization identifies the localized site and its actual
coefficients with those of the pro-etale object scheme. Repeat steps 2--7 there; restriction
of the scalar map is still constant functions. Ring identifications restrict as well. -/
theorem admissible_scalar_realization_exact (ℓ : ℕ) [Fact ℓ.Prime] (T : Scheme.{u}) :
    (∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [Finite A] [DiscreteTopology A],
      (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) →
      ScalarAssertions A T ∧ IsIso (FiniteDiscreteOrdinary.canonicalAbelianMap A T)) ∧
    (ScalarAssertions (ULift.{u} ℤ_[ℓ]) T ∧
      CompletedAssertions (ULift.{u} ℤ_[ℓ]) T (ℓ : ULift.{u} ℤ_[ℓ])) ∧
    (∀ (E : Type u) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E],
      IntegralAssertions ℓ E T ∧ RationalAssertions ℓ E T) ∧
    ScalarAssertions (ULift.{u} ℚ_[ℓ]) T ∧
    ScalarAssertions (ULift.{u} (PadicAlgCl ℓ)) T := by
  sorry

end AlgebraicGeometry.ProEtale.AdmissibleScalarRealization
