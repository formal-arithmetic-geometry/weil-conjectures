/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.ClopenStrictSystemComparison
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.Paper.CompactSupportCoefficientAction

import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.CoefficientSystemDerivedComparison
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.Paper.EtaleCoefficientSystemAdjoint
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients

/-! # Exceptional inverse image on finite clopen components

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/def-pur-section-invariant.md, finite-clopen compactification
and adjunction argument (blueprint: lem-pur-finite-clopen-exceptional-restriction).

The finite-level, strict-system, inverse-limit, rational, and common-stage
comparisons are specified together. Every comparison is tied to its canonical
construction; the coefficient-unit comparisons evaluate those same maps.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w c ci d v vi vd

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace WeilConjectures.PurityFiniteSetting

/-- The bounded constructible finite category, with the recorded cohomological predicate.
Source: blueprint finite coefficient clause
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
noncomputable abbrev clopenFiniteCategory (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (n : ℕ) :=
  (Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W).FullSubcategory

/-- The finite comparison is the counit-normalized right-adjoint comparison for
component insertion and the actual compact-support functors. The four formula
isomorphisms identify full-subcategory lifts of the already defined functors;
the last equation identifies the displayed finite map with that comparison.
Source: blueprint finite-clopen proof steps 2--4
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
structure ClopenFiniteAdjointComparisonData
    (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] (n : ℕ)
    (rho : clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E X Y g n ⋙
        finiteDerivedPullback P.coefficients.l E n j.left ≅
      clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E Xi Y (j.left ≫ g) n) where
  restriction : clopenFiniteCategory P.coefficients.l E X.left n ⥤
    clopenFiniteCategory P.coefficients.l E Xi.left n
  restrictionFormula : restriction ⋙ clopenFiniteInclusion P.coefficients.l E Xi.left n ≅
    clopenFiniteInclusion P.coefficients.l E X.left n ⋙
      finiteDerivedPullback P.coefficients.l E n j.left
  insertion : clopenFiniteCategory P.coefficients.l E Xi.left n ⥤
    clopenFiniteCategory P.coefficients.l E X.left n
  componentAdjunction : insertion ⊣ restriction
  reverseAdjunction : restriction ⊣ insertion
  reverseCounit : IsIso reverseAdjunction.counit
  support : clopenFiniteCategory P.coefficients.l E X.left n ⥤
    clopenFiniteCategory P.coefficients.l E Y.left n
  supportI : clopenFiniteCategory P.coefficients.l E Xi.left n ⥤
    clopenFiniteCategory P.coefficients.l E Y.left n
  supportFormula : support ⋙ clopenFiniteInclusion P.coefficients.l E Y.left n ≅
    clopenFiniteInclusion P.coefficients.l E X.left n ⋙
      Scheme.sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))
  supportFormulaI : supportI ⋙ clopenFiniteInclusion P.coefficients.l E Y.left n ≅
    clopenFiniteInclusion P.coefficients.l E Xi.left n ⋙
      Scheme.sfIntrinsicCompactSupport (c.precomp j.left)
        (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))
  exceptional : clopenFiniteCategory P.coefficients.l E Y.left n ⥤
    clopenFiniteCategory P.coefficients.l E X.left n
  exceptionalI : clopenFiniteCategory P.coefficients.l E Y.left n ⥤
    clopenFiniteCategory P.coefficients.l E Xi.left n
  exceptionalFormula : exceptional ⋙ clopenFiniteInclusion P.coefficients.l E X.left n ≅
    clopenFiniteInclusion P.coefficients.l E Y.left n ⋙ clopenFiniteExceptional P E X Y g n
  exceptionalFormulaI : exceptionalI ⋙ clopenFiniteInclusion P.coefficients.l E Xi.left n ≅
    clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
      clopenFiniteExceptional P E Xi Y (j.left ≫ g) n
  adjunction : support ⊣ exceptional
  adjunctionI : supportI ⊣ exceptionalI
  mate : ClopenCounitComparison insertion restriction support exceptional supportI exceptionalI
    componentAdjunction adjunction adjunctionI

/-- The normalization equations for `ClopenFiniteAdjointComparisonData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
def ClopenFiniteAdjointComparisonCoherence
    (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] (n : ℕ)
    (rho : clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E X Y g n ⋙
        finiteDerivedPullback P.coefficients.l E n j.left ≅
      clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E Xi Y (j.left ≫ g) n)
    (record : ClopenFiniteAdjointComparisonData P E X Y Xi g c j n rho) : Prop :=
  -- componentUnit
  (record.componentAdjunction.unit = @inv _ _ _ _ record.reverseAdjunction.counit
      record.reverseCounit) ∧
  -- comparisonMap
  (∀ L : clopenFiniteCategory P.coefficients.l E Y.left n,
    (clopenFiniteInclusion P.coefficients.l E Xi.left n).map (record.mate.comparison.hom.app L) ≫
        record.exceptionalFormulaI.hom.app L =
      record.restrictionFormula.hom.app (record.exceptional.obj L) ≫
        (finiteDerivedPullback P.coefficients.l E n j.left).map
          (record.exceptionalFormula.hom.app L) ≫ rho.hom.app L)

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
structure ClopenFiniteAdjointComparison
    (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] (n : ℕ)
    (rho : clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E X Y g n ⋙
        finiteDerivedPullback P.coefficients.l E n j.left ≅
      clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E Xi Y (j.left ≫ g) n)
    extends ClopenFiniteAdjointComparisonData P E X Y Xi g c j n rho where
  coherence : ClopenFiniteAdjointComparisonCoherence P E X Y Xi g c j n rho
      toClopenFiniteAdjointComparisonData

/-- All coefficient comparisons at one finite coefficient field. The exceptional
functors are fixed by the actual strict-system formula and, independently, their
adjunctions to the recorded compact-support functors. Rational maps are fixed on
all pure tensors. The integral comparison is the image of the specified system
map under the actual restriction-of-scalars/total-limit functor.
Source: blueprint proof steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
structure ClopenExceptionalCoefficientComparisonData
    (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] where
  baseUnit : IsUnit (P.coefficients.l : P.field.k)
  S : StrictEtaleCompactSupport
    (clopenSystemRing P.coefficients.l E) (clopenSystemUniformizer P.coefficients.l E) c
  G : StrictEtaleExceptionalAdjoint _ _ c S
  Si : StrictEtaleCompactSupport
    (clopenSystemRing P.coefficients.l E) (clopenSystemUniformizer P.coefficients.l E)
    (c.precomp j.left)
  Gi : StrictEtaleExceptionalAdjoint _ _ (c.precomp j.left) Si
  strict : StrictClopenExceptionalComparison _ _ c j.left S G Si Gi
  supportNormalization : StrictClopenCompactSupportNormalization _ _ c j.left S G Si Gi strict
  CX : ClopenSystemComparison P.coefficients.l E X.left S.PX
  CY : ClopenSystemComparison P.coefficients.l E Y.left S.PY
  Ci : ClopenSystemComparison P.coefficients.l E Xi.left Si.PX
  CYi : ClopenSystemComparison P.coefficients.l E Y.left Si.PY
  sameInput : clopenExceptionalInput P.coefficients.l E Y.left Si.PY CYi =
    clopenExceptionalInput P.coefficients.l E Y.left S.PY CY
  site : ClopenSystemSquare P.coefficients.l E strict CX Ci
  system : clopenExceptionalSystem P.coefficients.l E S G CX CY ⋙
      site.sequenceRestriction ≅
    clopenExceptionalSystem P.coefficients.l E Si Gi Ci CYi
  finiteEtaleAdjoint : ∀ n : ℕ,
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1}
        (Padic.coefficientExtensionRing P.coefficients.l E (n + 1)))) c).IsLeftAdjoint
  fixedFiniteFormula : ∀ n : ℕ,
    (Scheme.sfIntrinsicDerivedEquivalence Y.left
        (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))).inverse ⋙
      (@ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1} (Padic.coefficientExtensionRing P.coefficients.l E (n + 1)))
        _ _ X.left Y.left g c (finiteEtaleAdjoint n)) ⋙
      (Scheme.sfIntrinsicDerivedEquivalence X.left
        (Padic.coefficientExtensionRing P.coefficients.l E (n + 1))).functor ≅
      clopenFiniteExceptional P E X Y g n
  finite : ∀ n : ℕ,
    clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E X Y g n ⋙
        finiteDerivedPullback P.coefficients.l E n j.left ≅
      clopenFiniteInclusion P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E Xi Y (j.left ≫ g) n
  finiteMate : ∀ n : ℕ, ClopenFiniteAdjointComparison P E X Y Xi g c j n (finite n)
  finiteEvaluation : ∀ n : ℕ,
    clopenExceptionalSystem P.coefficients.l E S G CX CY ⋙
        coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l E X.left n ≅
      (sfIntegralConstructible P.coefficients.l E Y.left).ι ⋙
        scalarReductionDerivedExtension P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E X Y g n
  finiteEvaluationI : ∀ n : ℕ,
    clopenExceptionalSystem P.coefficients.l E Si Gi Ci CYi ⋙
        coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l E Xi.left n ≅
      (sfIntegralConstructible P.coefficients.l E Y.left).ι ⋙
        scalarReductionDerivedExtension P.coefficients.l E Y.left n ⋙
        clopenFiniteExceptional P E Xi Y (j.left ≫ g) n
  restrictionEvaluation : ∀ n : ℕ,
    site.sequenceRestriction ⋙
        coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l E Xi.left n ≅
      coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l E X.left n ⋙
        finiteDerivedPullback P.coefficients.l E n j.left
  integral : sfIntegralConstructibleCategory P.coefficients.l E Y.left ⥤
    sfIntegralConstructibleCategory P.coefficients.l E X.left
  integralI : sfIntegralConstructibleCategory P.coefficients.l E Y.left ⥤
    sfIntegralConstructibleCategory P.coefficients.l E Xi.left
  integralAdjunction :
    sfCompactSupportFiniteIntegralFunctor P.coefficients.l P.field.k baseUnit c E ⊣ integral
  integralAdjunctionI :
    sfCompactSupportFiniteIntegralFunctor P.coefficients.l P.field.k baseUnit
      (c.precomp j.left) E ⊣ integralI
  integralFormula : integral ⋙ (sfIntegralConstructible P.coefficients.l E X.left).ι ≅
    clopenExceptionalSystem P.coefficients.l E S G CX CY ⋙
      coefficientSequenceLimit.{u, u} P.coefficients.l E X.left
  integralFormulaI : integralI ⋙ (sfIntegralConstructible P.coefficients.l E Xi.left).ι ≅
    clopenExceptionalSystem P.coefficients.l E Si Gi Ci CYi ⋙
      coefficientSequenceLimit.{u, u} P.coefficients.l E Xi.left
  limitRestriction :
    integral ⋙ clopenIntegralRestriction P E j ⋙
        (sfIntegralConstructible P.coefficients.l E Xi.left).ι ≅
      clopenExceptionalSystem P.coefficients.l E S G CX CY ⋙ site.sequenceRestriction ⋙
        coefficientSequenceLimit.{u, u} P.coefficients.l E Xi.left
  integralComparison : integral ⋙ clopenIntegralRestriction P E j ≅ integralI
  rational : sfRationalConstructibleCategory P.coefficients.l E Y.left ⥤
    sfRationalConstructibleCategory P.coefficients.l E X.left
  rationalI : sfRationalConstructibleCategory P.coefficients.l E Y.left ⥤
    sfRationalConstructibleCategory P.coefficients.l E Xi.left
  rationalAdjunction :
    sfCompactSupportFiniteFunctor P.coefficients.l P.field.k baseUnit c E ⊣ rational
  rationalAdjunctionI :
    sfCompactSupportFiniteFunctor P.coefficients.l P.field.k baseUnit
      (c.precomp j.left) E ⊣ rationalI
  rationalComparison : rational ⋙ clopenRationalRestriction P E j ≅ rationalI

/-- The normalization equations for `ClopenExceptionalCoefficientComparisonData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
def ClopenExceptionalCoefficientComparisonCoherence
    (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalCoefficientComparisonData P E X Y Xi g c j) : Prop :=
  -- systemMap
  (∀ L : sfIntegralConstructibleCategory P.coefficients.l E Y.left,
    R.system.hom.app L = R.Ci.sequence.derived.functor.map
      (R.site.derived.system.inverse.map
          (R.CX.sequence.derived.unitIso.inv.app
            (R.CX.derived.system.inverse.obj
              (R.G.right.obj ((clopenExceptionalInput P.coefficients.l E Y.left R.S.PY
      R.CY).obj L)))) ≫
        R.site.square.hom.app
          (R.G.right.obj ((clopenExceptionalInput P.coefficients.l E Y.left R.S.PY R.CY).obj L)) ≫
        R.Ci.derived.system.inverse.map
          (R.strict.system.comparison.hom.app
            ((clopenExceptionalInput P.coefficients.l E Y.left R.S.PY R.CY).obj L)) ≫
        R.Ci.derived.system.inverse.map (R.Gi.right.map
          (eqToHom (congrArg (fun F ↦ F.obj L) R.sameInput.symm))))) ∧
  -- finiteSystemMap
  (∀ (n : ℕ)
    (L : sfIntegralConstructibleCategory P.coefficients.l E Y.left),
    (coefficientSequenceDerivedEvaluation.{u, u} P.coefficients.l E Xi.left n).map
        (R.system.hom.app L) ≫ (R.finiteEvaluationI n).hom.app L =
      (R.restrictionEvaluation n).hom.app
          ((clopenExceptionalSystem P.coefficients.l E R.S R.G R.CX R.CY).obj L) ≫
        (finiteDerivedPullback P.coefficients.l E n j.left).map
          ((R.finiteEvaluation n).hom.app L) ≫
        (R.finite n).hom.app ((clopenConstructibleReduction P.coefficients.l E Y.left n).obj L)) ∧
  -- inverseLimitMap
  (∀ L : sfIntegralConstructibleCategory P.coefficients.l E Y.left,
    (sfIntegralConstructible P.coefficients.l E Xi.left).ι.map
        (R.integralComparison.hom.app L) =
      R.limitRestriction.hom.app L ≫
        (coefficientSequenceLimit.{u, u} P.coefficients.l E Xi.left).map (R.system.hom.app L) ≫
        R.integralFormulaI.inv.app L) ∧
  -- rationalObject
  (∀ K, R.rational.obj K = ⟨R.integral.obj K.obj⟩) ∧
  -- rationalObjectI
  (∀ K, R.rationalI.obj K = ⟨R.integralI.obj K.obj⟩) ∧
  -- rationalMap
  (∀ (K L : sfIntegralConstructibleCategory P.coefficients.l E Y.left)
    (f : K ⟶ L) (a : Localization.Away (Padic.coefficientExtensionUniformizer P.coefficients.l E)),
    HEq (R.rational.map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l E] f :
        (sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj K ⟶
        (sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l E] R.integral.map f :
        (sfRationalConstructibleLocalization P.coefficients.l E X.left).obj (R.integral.obj K) ⟶
        (sfRationalConstructibleLocalization P.coefficients.l E X.left).obj (R.integral.obj L))) ∧
  -- rationalMapI
  (∀ (K L : sfIntegralConstructibleCategory P.coefficients.l E Y.left)
    (f : K ⟶ L) (a : Localization.Away (Padic.coefficientExtensionUniformizer P.coefficients.l E)),
    HEq (R.rationalI.map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l E] f :
        (sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj K ⟶
        (sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers P.coefficients.l E] R.integralI.map f :
        (sfRationalConstructibleLocalization P.coefficients.l E Xi.left).obj (R.integralI.obj K) ⟶
        (sfRationalConstructibleLocalization P.coefficients.l E Xi.left).obj (R.integralI.obj L))) ∧
  -- rationalComparisonMap
  (∀ L : sfIntegralConstructibleCategory P.coefficients.l E Y.left,
    HEq (R.rationalComparison.hom.app
      ((sfRationalConstructibleLocalization P.coefficients.l E Y.left).obj L))
      ((sfRationalConstructibleLocalization P.coefficients.l E Xi.left).map
        (R.integralComparison.hom.app L)))

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
structure ClopenExceptionalCoefficientComparison
    (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    extends ClopenExceptionalCoefficientComparisonData P E X Y Xi g c j where
  coherence : ClopenExceptionalCoefficientComparisonCoherence P E X Y Xi g c j
      toClopenExceptionalCoefficientComparisonData

section AllCoefficients
variable (P : PurityFiniteSetting.{u})
  (X Y Xi : Over (Spec (.of P.field.k)))
  [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
  [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
  [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
  (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (c : Compactification g) (j : Xi ⟶ X)
  [IsOpenImmersion j.left] [IsClosedImmersion j.left]

/-- The algebraically closed comparison is descent of the rationalized integral
comparisons at every actual common coefficient stage. The coefficient transitions
are the counit mates of the fixed compact-support coefficient action, including
identity extensions. Hence neither its functors nor its representative maps are
unconstrained existential adjoints.
Source: blueprint proof steps 10--11
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
structure ClopenExceptionalAllCoefficientsData where
  baseUnit : IsUnit (P.coefficients.l : P.field.k)
  base : ClopenExceptionalCoefficientComparison P P.extension X Y Xi g c j
  stage : ∀ B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
    ClopenExceptionalCoefficientComparison P
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
      X Y Xi g c j
  support : SfCompactSupportCoefficientAction
    P.coefficients.l P.field.k baseUnit P.coefficients.Qbar c
  supportI : SfCompactSupportCoefficientAction
    P.coefficients.l P.field.k baseUnit P.coefficients.Qbar (c.precomp j.left)
  action : (GeneralAlgebraicallyClosedCoefficients.stageSystem
      P.coefficients.l P.coefficients.Qbar Y.left).Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem
      P.coefficients.l P.coefficients.Qbar X.left)
  actionI : (GeneralAlgebraicallyClosedCoefficients.stageSystem
      P.coefficients.l P.coefficients.Qbar Y.left).Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem
      P.coefficients.l P.coefficients.Qbar Xi.left)
  adjunction : ∀ B, support.system.Φ B ⊣ action.Φ B
  adjunctionI : ∀ B, supportI.system.Φ B ⊣ actionI.Φ B
  stageComparison : ∀ B : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar,
    action.Φ B ⋙ clopenRationalRestriction P
        (AlgebraicallyClosedCoefficients.Coefficient.{u}
          P.coefficients.l P.coefficients.Qbar B) j ≅ actionI.Φ B
  commonStageComparison : action.functor ⋙ P.clopenCommonStagePullback j ≅ actionI.functor

/-- The normalization equations for `ClopenExceptionalAllCoefficientsData`.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
def ClopenExceptionalAllCoefficientsCoherence
    (R : ClopenExceptionalAllCoefficientsData P X Y Xi g c j) : Prop :=
  -- stage_eq
  (∀ B, R.action.Φ B = (R.stage B).rational) ∧
  -- stage_eqI
  (∀ B, R.actionI.Φ B = (R.stage B).rationalI) ∧
  -- adjunction_normalized
  (∀ B, HEq (R.adjunction B) (R.stage B).rationalAdjunction) ∧
  -- adjunction_normalizedI
  (∀ B, HEq (R.adjunctionI B) (R.stage B).rationalAdjunctionI) ∧
  -- scalarMate
  (∀ {B C : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar} (h : B ≤ C),
    (R.action.β h).hom =
      (mateEquiv (R.adjunction B) (R.adjunction C)
        (.mk _ _ _ _ (R.support.system.β h).inv)).natTrans) ∧
  -- scalarMateI
  (∀ {B C : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar} (h : B ≤ C),
    (R.actionI.β h).hom =
      (mateEquiv (R.adjunctionI B) (R.adjunctionI C)
        (.mk _ _ _ _ (R.supportI.system.β h).inv)).natTrans) ∧
  -- stageComparisonMap
  (∀ B, HEq (R.stageComparison B).hom (R.stage B).rationalComparison.hom) ∧
  -- commonStageMap
  (∀ (B : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar)
    (L : GeneralAlgebraicallyClosedCoefficients.Stage
      P.coefficients.l P.coefficients.Qbar Y.left B),
    HEq (R.commonStageComparison.hom.app ⟨B, L⟩)
      (StageSystem.PairCategory.mkHom
        (X := (⟨B, (clopenRationalRestriction P
          (AlgebraicallyClosedCoefficients.Coefficient.{u}
            P.coefficients.l P.coefficients.Qbar B) j).obj ((R.action.Φ B).obj L)⟩ :
              generalAlgebraicallyClosedConstructibleCategory
                P.coefficients.l P.coefficients.Qbar Xi.left))
        (Y := (⟨B, (R.actionI.Φ B).obj L⟩ :
          generalAlgebraicallyClosedConstructibleCategory
            P.coefficients.l P.coefficients.Qbar Xi.left))
        B le_rfl le_rfl
        ((GeneralAlgebraicallyClosedCoefficients.stageTransition
          P.coefficients.l P.coefficients.Qbar Xi.left B B le_rfl).map
            ((R.stageComparison B).hom.app L))))

/-- The actual comparison data together with all its normalization equations.
Source: finite-clopen compactification proof, steps 4--10
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
structure ClopenExceptionalAllCoefficients
   
    extends ClopenExceptionalAllCoefficientsData P X Y Xi g c j where
  coherence : ClopenExceptionalAllCoefficientsCoherence P X Y Xi g c j
      toClopenExceptionalAllCoefficientsData

/-- The integral dualizing-object comparison is the same comparison evaluated at
O_E,Y, not a comparison between the coefficient units on X and X_i.
Source: blueprint coefficient-unit clause
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
noncomputable def ClopenExceptionalAllCoefficients.integralUnitComparison
    (D : ClopenExceptionalAllCoefficients P X Y Xi g c j) :=
  D.base.integralComparison.app (P.clopenIntegralUnit Y.left)

/-- The rational dualizing-object comparison is evaluated at the rational coefficient unit.
Source: blueprint coefficient-unit clause
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
noncomputable def ClopenExceptionalAllCoefficients.rationalUnitComparison
    (D : ClopenExceptionalAllCoefficients P X Y Xi g c j) :=
  D.base.rationalComparison.app (P.clopenRationalUnit Y.left)

/-- The algebraically closed dualizing comparison is evaluated at the actual unit pair.
Source: blueprint coefficient-unit clause
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
noncomputable def ClopenExceptionalAllCoefficients.commonStageUnitComparison
    (D : ClopenExceptionalAllCoefficients P X Y Xi g c j)
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :=
  D.commonStageComparison.app (P.clopenCommonStageUnit Y.left B)

/-- At every positive finite level the dualizing comparison is evaluated at A_n,Y.
Source: blueprint coefficient-unit clause
(blueprint: lem-pur-finite-clopen-exceptional-restriction). -/
noncomputable def ClopenExceptionalAllCoefficients.finiteUnitComparison
    (D : ClopenExceptionalAllCoefficients P X Y Xi g c j) (n : ℕ) :=
  (D.base.finite n).app (clopenFiniteUnitAt P.coefficients.l P.extension Y.left n)

end AllCoefficients

/-- Exceptional inverse image restricts componentwise for a finite clopen cover.

Source: blueprint sec-six-functors-basics/sk-def-purity-conv,
finite-clopen compactification and adjunction argument
(blueprint: lem-pur-finite-clopen-exceptional-restriction).

Proof (postponed), following the eleven DAG steps:

1. Choose a compactification $c=(a,p)$ of $g$, with $a:X\hookrightarrow\overline X$ open and
$p:\overline X\to Y$ proper. This is legitimate by [thm-nagata-compactification]: a finite-type
scheme over a field is Noetherian by [lem-weil-pbc-finite-type-over-noetherian] (a field has
only two ideals), hence quasi-compact and quasi-separated by [lem-weil-pbc-locally-noetherian-
quasi-separated]. Put $a_i=a\circ j_i$. Composition of open immersions is open: compose their
isomorphisms with open subschemes, whose images remain open. Hence $(a_i,p)$ is a
compactification of $g_i$ by [def-weil-compactifications-refinements]. The schemes $X_i$ are
Noetherian opens by [lem-weil-pbc-noetherian-open-subscheme-noetherian]; $j_i$ is quasi-compact,
since the inverse image of an affine is closed in that affine and is therefore quasi-compact.
Thus [lem-weil-pbc-qc-open-immersion-finite-type] makes $j_i$ finite type. Its diagonal is an
isomorphism, so it is separated. Composing the closed diagonals and concatenating finite lists
of algebra generators shows that $g_i$ is separated finite type. The chosen proper part $p$ is
the SAME for every $i$. The scheme $\overline X$ is finite type over $k$, since $p$ and
$Y\to\operatorname{Spec}k$ are finite type; [lem-kun-dimension-finite-type] gives a finite bound
$d\geq0$ for its dimension when nonempty, as required by the finite adjunction theorem. If it is
empty take $d=0$.

2. Let $E_i$ be the inverse of the product equivalence [lem-pur-finite-clopen-derived-
decomposition] applied to the tuple having $M$ in position $i$ and zero elsewhere. In a finite
product of additive categories,
$$\operatorname{Hom}_X(E_iM,H)=\operatorname{Hom}_{X_i}(M,j_i^*H),\qquad
\operatorname{Hom}_X(H,E_iM)=\operatorname{Hom}_{X_i}(j_i^*H,M),$$
since all other factors are
singleton Hom sets involving zero. Thus $E_i$ is both adjoints of restriction, is exact, and
$K\cong\bigoplus_iE_iK_i$. On module sheaves $E_i$ is precisely $j_{i,!}$: [lem-weil-extension-
by-zero-adjunction] makes that functor another left adjoint of the same restriction. The
isomorphism is the one whose restriction to $X_i$ is the identity. Exact termwise descent
identifies the same functors on complexes and derived categories, as already specified in the
clopen equivalence.

3. For the chosen compactifications, $a_!E_i\cong(a_i)_!$. Indeed, on sheaves the two functors
are left adjoint to $j_i^*a^*=(a_i)^*$, using [lem-weil-extension-by-zero-adjunction] and the
composite adjunction [def-weil-pbc-composite-adjunction]. Apply [def-weil-pbc-adjunction-
conjugate] to the identity of these right adjoints, with opposite categories, to obtain the
unique unit-compatible isomorphism. Both extension functors are exact by [lem-weil-extension-by-
zero-exact], so termwise application and [lem-weil-pbc-localization-universal-property] descend
that comparison and its inverse. Consequently [def-compact-support-direct-image-detailed] gives
$Rg_!E_i\cong Rp_*(a_i)_!=R(g_i)_!$. The functor $Rp_*$ is a right adjoint by [def-weil-pbc-
proetale-operations]; it preserves a finite product since maps into that product are tuples of
maps under its adjunction bijection. Finite products are biproducts here, so it also preserves
finite direct sums. Apply $Rp_*a_!$ to the decomposition in Step 2 to obtain
$$Rg_!K\cong\bigoplus_iR(g_i)_!K_i.$$
All maps are natural in $K$. On bounded constructible
inputs the comparison with any originally chosen compactifications is [prop-compactification-
coherence-detailed]; these inputs have etale origin by [lem-sf-proetale-constructible-origin],
so this use stays in its asserted domain.

4. For $M\in D^b_c(X_i,A)$ and $L\in D^b_c(Y,A)$, use Step 2, Step 3 and [thm-sf-ambient-
adjoint-class] to obtain natural bijections
$$\operatorname{Hom}_{X_i}(M,j_i^*Rg^!L)\cong\operat
orname{Hom}_X(E_iM,Rg^!L)\cong\operatorname{Hom}_Y(Rg_!E_iM,L)\cong\operatorname{Hom}_Y(R(g_i)_!
M,L).$$
Here $E_iM$ is bounded constructible by the clopen equivalence, hence of etale origin.
The functors $Rg^!$ and $R(g_i)^!$ have bounded constructible values by the specified
constructible restriction in [def-weil-exceptional-inverse-image]. For each $L$, both objects
therefore represent the same functor of $M$ on the full category $D^b_c(X_i,A)$. The uniqueness
argument of [det-sp-unique-right-adjoint] applies: transpose the counit in each direction and
evaluate the Hom identities at the two representing objects; the two composites are identities.
Naturality of the Hom bijections gives naturality in $L$. This produces a natural isomorphism
$\rho_i$, uniquely specified by
$$\varepsilon_{g_i,L}\circ
R(g_i)_!(\rho_{i,L})=\varepsilon_{g,L}\circ Rg_!(c_{i,Rg^!L})\circ b_{i,j_i^*Rg^!L}^{-1},$$
where $c_i:E_ij_i^*\to\mathrm{id}$ is the product adjunction counit and
$b_i:Rg_!E_i\xrightarrow{\sim}R(g_i)_!$ is Step 3. This equation identifies the comparison as
the component right-adjoint comparison of the direct-sum formula, rather than an arbitrary
isomorphism.

5. Now work with strict etale systems $\mathsf S_A$ of [lem-pur-coefficient-system-derived-
comparison]. The cover identifies $X$ with $\coprod_iX_i$: maps on the disjoint open components
glue uniquely, and gluing the component inclusions gives inverse scheme maps. The etale clopen
decomposition [lem-weil-pbc-etale-sheaf-clopen-product] extends to constant-$A_n$ modules:
transport each scalar action and each linearity equation componentwise through its fully
faithful equivalence. Apply this at every $n$; a transition is a family of component maps and
its semilinearity equation is checked on each component. This gives an exact product equivalence
for STRICT systems with inverse given by zero insertion and finite products, and with evaluation
$e_n$ commuting with restriction and insertion. Exactness and inverse identities are levelwise.
The exact functors induce derived functors by [lem-sf-exact-functor-derived-triangulated]. Their
unit and inverse identities descend by [lem-weil-pbc-localization-universal-property]. Thus on
derived systems, insertion $E_{i,A}$ and restriction $r_{i,A}$ are adjoint in both orders, with
the same zero-component Hom calculation as Step 2; the termwise units and counits descend and
retain their triangle identities. In particular this is an equivalence of actual derived system
categories, not a product decomposition of the evaluations of an unspecified diagram.

6. Write $F_{g,A}=Rp_{A,*}a_{!,A}$ and $F_{g_i,A}=Rp_{A,*}(a_i)_{!,A}$ as in [lem-pur-etale-
coefficient-system-adjoint], for the common proper part of Step 1. There is an isomorphism
$$b_{i,A}:F_{g,A}E_{i,A}\xrightarrow{\sim}F_{g_i,A}.$$
To construct it, apply [lem-cbc-
extension-zero-composition] at every coefficient level to $a\circ j_i$. The isomorphism commutes
with transitions: on the extension-by-zero presheaves both orders send a section on the
component to that same section on its image, with its coefficient action restricted along
$A_{n+1}\to A_n$, and send the other summands to zero. Sheafification preserves these equalities
by its universal property. These are therefore inverse maps of strict systems, natural in the
system, not independently chosen derived level maps. Exactness of open extension holds levelwise
by [lem-pur-site-restriction-module-adjunction-exact]; descend its comparison by [lem-weil-pbc-
localization-universal-property] and apply the actual functor $Rp_{A,*}$. No interchange of
evaluation with a chosen resolution is needed here. Evaluating $b_{i,A}$ gives the corresponding
ordinary etale finite-level comparison by [lem-pur-coefficient-system-derived-comparison].

7. Let $G_{g,A},G_{g_i,A}$ be the actual right adjoints supplied by [lem-pur-etale-coefficient-
system-adjoint]. Step 5 and Step 6 give
$$\operatorname{Hom}(M,r_{i,A}G_{g,A}N)\cong\operatornam
e{Hom}(E_{i,A}M,G_{g,A}N)\cong\operatorname{Hom}(F_{g,A}E_{i,A}M,N)\cong\operatorname{Hom}(F_{g_
i,A}M,N).$$
By [det-sp-unique-right-adjoint] this constructs a natural isomorphism
$\rho_{i,A}:r_{i,A}G_{g,A}\cong G_{g_i,A}$ IN the derived category of strict systems. Its
defining counit equation is exactly Step 4's equation with system subscripts. Evaluation
respects $b_{i,A}$, the product adjunction, and the units/counits of $F\dashv G$ by [lem-pur-
etale-coefficient-system-adjoint]. Thus evaluation of that equation is the finite etale
equation; uniqueness of its transpose identifies $e_n\rho_{i,A}$ with the finite-level right-
adjoint comparison. This also proves the transition compatibility with the prescribed adjunction
mates. It does not infer equality of system maps merely from equality at all evaluations.

8. The etale/pro-etale comparison respects this construction on actual systems. The square
$j_i^*\nu_X^*\cong\nu_{X_i}^*j_i^*$ is [lem-weil-pbc-comparison-pullback]. It extends to systems
termwise: all maps are natural in coefficient-module morphisms, so they commute with the strict
transitions; exactness permits derived descent by [lem-weil-pbc-localization-universal-
property]. The system comparison and evaluation of $R\nu_{Y,A,*}$ are those of [lem-pur-
coefficient-system-derived-comparison]. Whisker Step 7 by $R\nu_{Y,A,*}$ and $\nu_{X_i,A}^*$,
using the preceding square. This gives
$$r_{i,A}\nu_{X,A}^*G_{g,A}R\nu_{Y,A,*}\cong\nu_{X_i,A}^*G_{g_i,A}R\nu_{Y,A,*}.$$
Evaluation
gives $Lj_i^*Rg_n^!\cong R(g_i)_n^!$. The comparison is the one of Step 4: [lem-cbc-proetale-
extension-zero-comparison] identifies the extension terms, and [thm-sf-ambient-adjoint-class]
states that the transported Hom bijections respect compactification comparisons. Therefore
transporting the counit equation of Step 7 gives exactly Step 4's equation. Uniqueness in [det-
sp-unique-right-adjoint] identifies the two maps. This proves the asserted site and evaluation
compatibility, within bounded-below etale-origin domains when using the finite pro-etale
adjunction.

9. For an integral $L$, compose the system isomorphism of Step 8 with the reduction functor
$\mathcal R_Y$ of [def-weil-exceptional-inverse-image]. This is an isomorphism $r_{i,A}\mathcal
T_gL\cong\mathcal T_{g_i}L$ of actual derived strict systems. Restriction of scalars $DU_X$
commutes with $r_{i,A}$: both underlying systems have the restricted component sheaves and the
same transitions and completed-ring actions. The clopen equivalence [lem-pur-finite-clopen-
derived-decomposition] says that restriction also commutes with derived inverse limits and
finite reduction. Apply the functor $R\lim\circ DU$ to this system map, with the total-limit
functor of [lem-weil-pbc-ringed-strict-tower-homotopy-limit]. The formula $Rg^!_{\mathcal
O_E}=R\lim\,DU_X\mathcal T_g$ in [def-weil-exceptional-inverse-image] now yields
$$Lj_i^*Rg^!_{\mathcal O_E}L\cong R(g_i)^!_{\mathcal O_E}L.$$
Here $\mathcal T_g$ and $\mathcal
T_{g_i}$ are formed, as the definition permits, with the compactifications $c=(a,p)$ and
$c_i=(a_i,p)$ of Step 1. The integral $Lj_i^*$ agrees with component restriction: by [def-weil-
derived-pullback-tensor-hom], $Lj_i^*K=R\lim_n\operatorname{Res}_nj_i^{-1}(K\otimes^L_{\mathcal
O_E}A_{E,n})$, since finite-level pullback along $j_i$ is termwise restriction. The clopen
equivalence commutes restriction with reduction, $\operatorname{Res}_n$ and $R\lim$, so this is
$j_i^{-1}R\lim_nK_n$; for $K=Rg^!_{\mathcal O_E}L$, derived complete by its $D^b_c$ typing,
$K\cong R\lim_nK_n$ [def-weil-derived-complete]. Invertibility follows because a functor sends
an isomorphism and its inverse to mutually inverse maps. No reconstruction of a morphism from
unrelated maps in ordinary derived categories has occurred.

10. These isomorphisms are $\mathcal O_E$-linear, since the system adjoints and all
restriction/extension maps are linear. Rationalization therefore sends the comparison and its
inverse to mutually inverse $E$-linear transformations, using exactly [def-weil-exceptional-
inverse-image]'s rationalized functors. For a finite extension $E\subset E'$, the scalar
comparison for $G$ is an isomorphism of systems, including the cofinal indexing comparison, by
[lem-pur-etale-coefficient-system-adjoint]. It commutes with the component comparison:
coefficient extension commutes with restriction and zero insertion, and the two composites of
open extension send every local section to the same extended section. Transposing these squares
gives the same right-adjoint square by the pasting identities [lem-weil-pbc-mate-pasting]; hence
the two orders of scalar comparison and $\rho_i$ coincide, including their system morphisms. The
coherent scalar comparisons pass through $DU$ and $R\lim$ by the construction in [def-weil-
exceptional-inverse-image]. Thus the $E$-comparisons agree after every common finite extension
and define the asserted natural isomorphism in the common-stage $\overline{\mathbf Q}_\ell$
category. This uses the actual systems' scalar comparisons, not just an equality of their
evaluated objects.

11. Take $L=\Lambda_Y$. By definition [def-weil-exceptional-inverse-image],
$Rg^!\Lambda_Y=\omega_g$ and $R(g_i)^!\Lambda_Y=\omega_{g_i}$, giving
$Lj_i^*\omega_g\cong\omega_{g_i}$ at all four stages. If $X_i$ is empty its module category and
system category have only the zero object, so $E_i=0$ and every displayed component isomorphism
is the unique zero-to-zero map. If $I$ is empty, the cover condition makes $X$ empty; the
product decomposition of [lem-pur-finite-clopen-derived-decomposition] makes $K=0$ and Step 3
gives $Rg_!K=0$, the empty direct sum. There are then no restriction comparisons to assert. The
argument nowhere uses smoothness, an orientation, a section, or tensor invertibility.
-/
theorem finiteClopenExceptionalRestriction
    (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (.of P.field.k)))
    [∀ i, LocallyOfFiniteType ((Xi i).left ↘ Spec (.of P.field.k))]
    [∀ i, QuasiCompact ((Xi i).left ↘ Spec (.of P.field.k))]
    (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left]
    [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : ∀ i i', i ≠ i' →
      Disjoint (Set.range (j i).left) (Set.range (j i').left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ) :
    (∀ (n : ℕ) (c : Compactification g),
      Nonempty
        (clopenFiniteInclusion P.coefficients.l P.extension X.left n ⋙
            Scheme.sfIntrinsicCompactSupport c
              (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) ≅
          clopenFiniteInclusion P.coefficients.l P.extension X.left n ⋙ finiteBiproductFunctor
            (fun i ↦ finiteDerivedPullback P.coefficients.l P.extension n (j i).left ⋙
              Scheme.sfIntrinsicCompactSupport (c.precomp (j i).left)
                (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))))) ∧
    (∀ (c : Compactification g) (i : I),
      Nonempty (ClopenExceptionalAllCoefficients P X Y (Xi i) g c (j i))) := by
  sorry

end WeilConjectures.PurityFiniteSetting
