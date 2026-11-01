/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptionalData
public import WeilConjectures.SixFunctors.Compact.CompactSupportNormalizedRealization
import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
import all WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemResolutionModels
import WeilConjectures.SixFunctors.Coef.CoefFiniteHomSiteDescent
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicVerdierBounds
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The intrinsic finite Verdier coefficient comparison

Source: current blueprint cor-coef-finite-verdier.proof.md, paragraphs 1--3, and
lem-coef-finite-exceptional.proof.md, paragraph 2.
(blueprint: lem-sf-finite-exceptional-dual-comparison).

The actual quotient tensor and the coefficient-system quotient have the same normalized
restriction right adjoint. Its adjunction determines their comparison uniquely. The
etale dualizing object is finite-Tor constructible by finite duality of the unit;
site descent and the specified dualizing origin transport this property. Finite Verdier
bounds give closure under duality, including the empty scheme. The counit-defined
dualizing quotient comparison is invertible. Compose finite Hom coefficient change
with Hom of that dualizing comparison, correcting both source and target by the unique
quotient-model comparison. Each factor is invertible on the stated domain.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteExceptional
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
  [QuasiCompact (T ↘ Spec (.of D.k))] [IsSeparated (T ↘ Spec (.of D.k))]

include hl in
include hl in

/-- The quotient tensor adjunction in normalized sequence-restriction coordinates. -/
def quotientAdjunction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    reduction l E T h ⊣ normalizedDVRRes l E T h :=
  (pbcDerivedScalarAdjunction _).ofNatIsoRight
    (coefCompactSupportRestrictionIso l E T h).symm

/-- The two derived quotient constructions have the same scalar restriction right adjoint. -/
def quotientModelIso (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    reduction l E T h ≅ coefficientFiniteQuotientDerived l E T h :=
  (quotientAdjunction l E T h).leftAdjointUniq
    ((coefficientDerivedSystemEvaluationCalculus l E T).choose.quotientCalculus.adjunction h)

/-- The prescribed intrinsic dualizing object is finite-Tor constructible. -/
theorem dualizing_mem (n : ℕ) :
    domain l E T n (integralDualizingFiniteTerm l E D T n) := by
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertible_exponent D l hl E (n + 1)
  let := (finiteDualizingCompactification D T).hasCompactification
  let ωe := finiteDualizingEtaleTerm l E D T n
  have hω : finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) T ωe := by
    apply (finiteTorConstructibleEtale_iff_source l E (n + 1) (Nat.succ_pos n) T ωe).2
    exact Etale.constructibleFiniteTor_dualizingComplex A (𝟙 _) _
      (Etale.constructibleFiniteTor_unit A)
  have hdesc := (coefFiniteHomSiteDescent D l hl E T).1 n
  have hNu := (hdesc.2.2.2.2 ωe hω).1
  let eω : (finiteHomNu l E T n).obj ωe ≅ integralDualizingFiniteTerm l E D T n :=
    (@Functor.mapDerivedCategoryCompIso.{u + 2, u + 2, u + 2,
        u + 1, u + 1, u + 1, u + 1, u + 1, u + 2}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
      (scalarReductionTarget.{u, u} l E T n)
      _ _ _ _ _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _)
      (HasDerivedCategory.standard _)
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (ProEtale.finiteCoefficientIntrinsicRealization T
        (Padic.coefficientExtensionRing l E (n + 1)))
      inferInstance
      (ProEtale.finiteCoefficientIntrinsicRealization_exact T
        (Padic.coefficientExtensionRing l E (n + 1))).2.1
      inferInstance inferInstance
      (ProEtale.finiteCoefficientIntrinsicRealization_exact T
        (Padic.coefficientExtensionRing l E (n + 1))).2.2.1
      (ProEtale.finiteCoefficientIntrinsicRealization_exact T
        (Padic.coefficientExtensionRing l E (n + 1))).2.2.2).app ωe ≪≫
      finiteDualizingOrigin l E D T n
  have : (domain l E T n).IsClosedUnderIsomorphisms :=
    (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) T).1
  exact (domain l E T n).prop_of_iso eω hNu

/-- Finite Verdier duality preserves the full finite-Tor constructible domain. -/
theorem dual_mem (n : ℕ) (K : (domain l E T n).FullSubcategory) :
    domain l E T n ((dual l E D T n).obj (op K.obj)) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (T ↘ Spec (.of D.k))
  obtain ⟨hc, a, b, ht⟩ := K.property
  have hv := IntegralVerdier.finiteIntrinsicVerdier_bounds D l hl E T n K.obj hc d hd a b ht
  exact ⟨hv.1, -b - 2 * (d : ℤ), -a, hv.2.1⟩

/-- The dualizing quotient map in the actual quotient-tensor presentation. -/
def dualizingQuotientMap {m n : ℕ} (h : n ≤ m) :
    (reduction l E T h).obj (integralDualizingFiniteTerm l E D T m) ⟶
      integralDualizingFiniteTerm l E D T n :=
  ((quotientAdjunction l E T h).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E T h))).hom.app
      (integralDualizingFiniteTerm l E D T m) ≫
    integralDualizingFiniteComparison l E D T hl h

/-- The structural dualizing coefficient comparison is invertible. -/
theorem dualizingQuotientMap_isIso {m n : ℕ} (h : n ≤ m) :
    IsIso (dualizingQuotientMap l E D hl T h) := by
  have hu : IsIso (integralDualizingFiniteComparison l E D T hl h) :=
    (finiteDualizingCoefficientComparisons l E D T hl).2.2.2.1 h
  exact (((quotientAdjunction l E T h).leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E T h))).app
      (integralDualizingFiniteTerm l E D T m) ≪≫
    @asIso _ _ _ _ (integralDualizingFiniteComparison l E D T hl h) hu).isIso_hom

/-- Verdier coefficient change, using the fixed evaluation-defined Hom comparison. -/
def dualQuotientMap {m n : ℕ} (h : n ≤ m)
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionRing l E (m + 1))) :
    (reduction l E T h).obj ((dual l E D T m).obj (op K)) ⟶
      (dual l E D T n).obj (op ((reduction l E T h).obj K)) :=
  (quotientModelIso l E T h).hom.app ((dual l E D T m).obj (op K)) ≫
    finiteIntrinsicReductionHom l E T h K (integralDualizingFiniteTerm l E D T m) ≫
    (finiteIntrinsicDerivedInternalHom l E T n).map
      (Prod.mkHom ((quotientModelIso l E T h).hom.app K).op
        ((quotientModelIso l E T h).inv.app (integralDualizingFiniteTerm l E D T m) ≫
          dualizingQuotientMap l E D hl T h))

/-- Finite Hom coefficient change and the dualizing counit make this map invertible. -/
theorem dualQuotientMap_isIso {m n : ℕ} (h : n ≤ m)
    (K : (domain l E T m).FullSubcategory) :
    IsIso (dualQuotientMap l E D hl T h K.obj) := by
  have hHom : IsIso (finiteIntrinsicReductionHom l E T h K.obj
      (integralDualizingFiniteTerm l E D T m)) :=
    ((finiteCoefficient_derivedHom_change D l hl E T m n h).2.2.2.2.2.1
    K.obj (integralDualizingFiniteTerm l E D T m) K.property
      (dualizing_mem l E D hl T m)).2.2
  let u := @asIso _ _ _ _ (dualizingQuotientMap l E D hl T h)
    (dualizingQuotientMap_isIso l E D hl T h)
  let e := quotientModelIso l E T h
  exact (e.app ((dual l E D T m).obj (op K.obj)) ≪≫
    @asIso _ _ _ _ (finiteIntrinsicReductionHom l E T h K.obj
      (integralDualizingFiniteTerm l E D T m)) hHom ≪≫
    (finiteIntrinsicDerivedInternalHom l E T n).mapIso
      ((e.app K.obj).op.prod
        (e.symm.app (integralDualizingFiniteTerm l E D T m) ≪≫ u))).isIso_hom

set_option maxHeartbeats 1000000 in
-- The scalar adjunctions involve independently chosen derived presentations.
end WeilConjectures.FiniteExceptional
