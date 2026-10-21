/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SfConstructibleHeart
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.TraceFormulaAdicSystem
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.Paper.PointSectionsDerivedReduction
public import Sheaf.Paper.IntegralScalarExtensionWellDefined
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.ConstructibleTruncations
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.CompactSupportRepresentativeIndependence

/-! # Integral lattice on a curve

Source: blueprint main-20261015, `thm-trf-l-function-euler-product.proof.md`, Step 5
(blueprint: lem-trf-curve-integral-lattice).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

namespace TraceFormulaCoefficientConventions

/-- Multiplication by a uniformizer power on an actual completed-coefficient sheaf.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeScalar (T : TraceFormulaCoefficientConventions.{u})
    (C : scalarReductionSource T.coefficients.l T.coefficientField T.geometricBaseChange)
    (n : ℕ) : C ⟶ C :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 C).inv ≫
    ((integralScalarChainAction T.coefficients.l T.coefficientField T.geometricBaseChange
      (Padic.coefficientExtensionUniformizer T.coefficients.l T.coefficientField ^ n)).app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj C)).f 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 C).hom

/-- The degree-zero cohomology of the supplied integral representative.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeCohomology (T : TraceFormulaCoefficientConventions.{u})
    (K : sfIntegralConstructibleCategory T.coefficients.l T.coefficientField
      T.geometricBaseChange) :
    scalarReductionSource T.coefficients.l T.coefficientField T.geometricBaseChange :=
  (DerivedCategory.homologyFunctor _ 0).obj K.obj

/-- The quotient by the kernel at exponent e+1. The theorem asserts that this kernel
contains every power kernel, so it is exactly the union D in the source.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeQuotient (T : TraceFormulaCoefficientConventions.{u})
    (K : sfIntegralConstructibleCategory T.coefficients.l T.coefficientField
      T.geometricBaseChange) (e : ℕ) :
    scalarReductionSource T.coefficients.l T.coefficientField T.geometricBaseChange :=
  cokernel (kernelSubobject (T.latticeScalar (T.latticeCohomology K) (e + 1))).arrow

/-- Compact sections with the geometric structure morphism installed, using the recorded
integral construction, including its coefficient-universe lift.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeCompactSections (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap)
    (K : sfIntegralConstructibleCategory T.coefficients.l T.coefficientField
      T.geometricBaseChange) :
    (DerivedCategory.pointFgComplete
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField))
      (Ideal.span {ULift.up
        (Padic.coefficientExtensionUniformizer T.coefficients.l
          T.coefficientField)})).FullSubcategory := by
  letI : T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩
  letI : LocallyOfFiniteType (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricFiniteType
  letI : QuasiCompact (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricQuasiCompact
  letI : IsSeparated (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricSeparated
  exact integralCompactSections T.datum T.coefficients.l T.coefficients.different
    T.coefficientField T.geometricBaseChange c K

/-- Rational compact cohomology with the same geometric structure map and compactification.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeRationalCohomology (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap)
    (K : sfRationalConstructibleCategory T.coefficients.l T.coefficientField
      T.geometricBaseChange) (i : ℤ) : ModuleCat.{u} T.coefficientField := by
  letI : T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩
  letI : LocallyOfFiniteType (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricFiniteType
  letI : QuasiCompact (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricQuasiCompact
  letI : IsSeparated (T.geometricBaseChange ↘ Spec (.of T.datum.k)) :=
    T.geometricSeparated
  exact rationalCompactCohomology T.datum T.coefficients.l T.coefficients.different
    T.coefficientField T.geometricBaseChange c K i

/-- Finiteness of every positive coefficient level, with the index shift explicit.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
instance latticeFiniteLevel (T : TraceFormulaCoefficientConventions.{u}) (n : ℕ) :
    Finite (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1)) :=
  Padic.finite_coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))

end TraceFormulaCoefficientConventions

namespace TraceFormulaCoefficientConventions

/-- The localization of a coefficient model in the small derived category used by
integral compact sections. Source: blueprint Step 5
(blueprint: lem-trf-curve-integral-lattice). -/
def latticeModel (T : TraceFormulaCoefficientConventions.{u})
    (P : CochainComplex (ModuleCat.{u + 1}
      (ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField))) ℤ) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField)))
  DerivedCategory.Q.obj P

/-- A finite-level reduction of a chosen compact-support model.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeModelReduction (T : TraceFormulaCoefficientConventions.{u})
    (P : CochainComplex (ModuleCat.{u + 1}
      (ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField))) ℤ)
    (n : ℕ) :=
  let f := pointReductionQuotient T.coefficients.l T.coefficientField n
  letI : (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} f).isLeftAdjoint
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1}
    (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField (n + 1))))
  DerivedCategory.Q.obj
    (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} f).mapHomologicalComplex
      (.up ℤ)).obj P)

/-- Finite compact sections with the geometric structure map installed.
Source: blueprint Step 5 (blueprint: lem-trf-curve-integral-lattice). -/
def latticeFiniteCompactSections (T : TraceFormulaCoefficientConventions.{u})
    (c : Compactification T.structureMap) (n : ℕ)
    (K : adicLevel T n) :=
  letI : T.geometricBaseChange.Over (Spec (.of T.datum.k)) := ⟨T.structureMap⟩
  finiteCompactSections T.datum T.coefficients.l T.coefficientField
    T.geometricBaseChange c (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) K

end TraceFormulaCoefficientConventions

/-- The degree-zero torsion quotient is a torsion-free integral lattice, with its ordinary
finite reductions, explicit etale origins, normalized quotient transitions and finite-free
compact-support model. Positive exponent n+1 covers every n≥1 of the source.
Source: blueprint main-20261015, thm-trf-l-function-euler-product, Step 5
(blueprint: lem-trf-curve-integral-lattice).

Proof: rational standard truncations show that all other integral cohomology is killed
by uniformizer powers. Integral stratified perfectness gives finitely presented local
models for H⁰; their torsion exponents have a common bound e+1. Thus its power-torsion
union is the kernel at e+1, and the cokernel M is integral constructible and torsion-free.
The truncation and quotient cones are power-torsion, hence invertible after localization;
compose with alpha to identify K_E with Q(M). The two-term uniformizer resolution gives
ordinary reductions M/ϖⁿM, and integral residue Tor gives finite Tor amplitude [0,0].
Finite-ring constructible derived origin supplies the specified etale antecedents.
Quotient transitions and derived tensor associativity give the normalized A-system.
Finally clauses (1) and (2) of the adic coefficient-morphism systems proposition, which
need no Weil structure, identify compact support with a bounded finite-free model and
all its finite reductions. Flat localization to E gives the cohomology comparison. -/
theorem exists_curve_integral_lattice
    (T : TraceFormulaCoefficientConventions.{u})
    (_hdim : topologicalKrullDim T.X₀.left ≤ 1)
    (K_E : sfRationalConstructibleCategory T.coefficients.l T.coefficientField
      T.geometricBaseChange)
    (K_O : sfIntegralConstructibleCategory T.coefficients.l T.coefficientField
      T.geometricBaseChange)
    (_alpha : (sfRationalConstructibleLocalization T.coefficients.l T.coefficientField
      T.geometricBaseChange).obj K_O ≅ K_E)
    (_hheart : sfRationalHeartProperty T.coefficients.l T.coefficientField
      T.geometricBaseChange K_E) :
    ∃ (e : ℕ) (M : sfIntegralConstructibleCategory T.coefficients.l T.coefficientField
        T.geometricBaseChange),
      (∀ n : ℕ,
        kernelSubobject (T.latticeScalar (T.latticeCohomology K_O) (n + 1)) ≤
          kernelSubobject (T.latticeScalar (T.latticeCohomology K_O) (e + 1))) ∧
      Nonempty (M.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (T.latticeQuotient K_O e)) ∧
      Mono (T.latticeScalar (T.latticeQuotient K_O e) 1) ∧
      Nonempty (K_E ≅ (sfRationalConstructibleLocalization T.coefficients.l
        T.coefficientField T.geometricBaseChange).obj M) ∧
      (∀ n : ℕ,
        Nonempty ((scalarReductionDerivedExtension T.coefficients.l T.coefficientField
          T.geometricBaseChange n).obj M.obj ≅
          (DerivedCategory.singleFunctor _ 0).obj
            ((scalarReductionExtension T.coefficients.l T.coefficientField
              T.geometricBaseChange n).obj (T.latticeQuotient K_O e))) ∧
        ∃ (F : DerivedCategory.Plus
            (Sheaf (ProEt.topology T.geometricBaseChange)
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField
                  (n + 1)))))),
          Nonempty (F.obj ≅ (sfIntrinsicDerivedEquivalence T.geometricBaseChange
            (Padic.coefficientExtensionRing T.coefficients.l T.coefficientField
              (n + 1))).inverse.obj
                ((scalarReductionDerivedExtension T.coefficients.l T.coefficientField
                  T.geometricBaseChange n).obj M.obj)) ∧
          Nonempty (FixedEtaleOriginWitness T.geometricBaseChange
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing T.coefficients.l
              T.coefficientField (n + 1))) F)) ∧
      (∃ S : TraceFormulaASystem T, S.IsNormalized ∧
        (∀ n : ℕ, Nonempty ((S.K n).obj ≅
          (scalarReductionDerivedExtension T.coefficients.l T.coefficientField
            T.geometricBaseChange n).obj M.obj)) ∧
        ∃ eta : ∀ n : ℕ, S.restrictedObjects n ≅
            (sfDerivedReductionRestricted T.coefficients.l T.coefficientField
              T.geometricBaseChange n).obj M.obj,
          ∀ n : ℕ, S.restrictedStep n ≫ (eta n).hom =
            (eta (n + 1)).hom ≫
              (sfDerivedReductionTransition T.coefficients.l T.coefficientField
                T.geometricBaseChange n).app M.obj) ∧
      ∀ c : Compactification T.structureMap,
        ∃ P : CochainComplex (ModuleCat.{u + 1}
            (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField))) ℤ,
          (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
          (∀ i : ℤ,
            Module.Free (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField))
                (P.X i) ∧
            Module.Finite (ULift.{u + 1, u}
              (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField))
                (P.X i)) ∧
          Nonempty (T.latticeModel P ≅ (T.latticeCompactSections c M).obj) ∧
          (∀ n : ℕ, Nonempty (T.latticeModelReduction P n ≅
            T.latticeFiniteCompactSections c n
              ((scalarReductionDerivedExtension T.coefficients.l T.coefficientField
                T.geometricBaseChange n).obj M.obj))) ∧
          (∀ i : ℤ, Nonempty
            ((ModuleCat.uliftFunctor.{u + 1} T.coefficientField).obj
                (T.latticeRationalCohomology c K_E i) ≅
              (ModuleCat.extendScalars.{u + 1, u, u + 1}
                ((algebraMap
                  (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField)
                  T.coefficientField).comp
                  (ULift.ringEquiv : ULift.{u + 1, u}
                    (Padic.coefficientExtensionIntegers T.coefficients.l T.coefficientField)
                      ≃+* _).toRingHom)).obj (P.homology i))) := by
  sorry

end WeilConjectures
