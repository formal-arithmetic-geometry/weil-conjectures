/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ComparisonPullbackExact
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Evaluation comparison for a bounded finite free etale complex

Source: Weil blueprint, sec-six-functors, sk-prop-sf-rf-shriek-preservation,
node lem-sf-hom-comparison-finite-free; Stacks Project, Tags 08JI, 03EO and 03EL
(blueprint: lem-sf-hom-comparison-finite-free).

Fixed-coefficient module sheaves use the recorded ModuleCat-valued encoding.
The canonical comparison below is the curry of pulled-back evaluation, using the
canonical derived tensor comparison and the exact-functor identification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale

/-- Positive coefficient levels are finite, using the recorded coefficient theorem.
Source: blueprint coefficient convention and Serre, Local Fields, II §2
(blueprint: lem-sf-hom-comparison-finite-free). -/
noncomputable instance finiteFreeHomComparison_coefficientFinite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n n.property

/-- The specified evaluation comparison is invertible for a bounded finite free first
complex and a bounded complex with constructible cohomology in the second variable.
Source: blueprint lem-sf-hom-comparison-finite-free, order 2083; Stacks Tags 08JI and 099R
(blueprint: lem-sf-hom-comparison-finite-free).

Proof:
1. The comparison pullback is additive and exact, identifies the two coefficient units,
   preserves finite sums and zero objects, and preserves the support bounds of P and N
   (lem-sf-comparison-pullback-exact). Its derived action is therefore termwise.
2. For a finite free term R^r and any sheaf B, internal Hom is B^r by images of the
   basis. Currying pulled-back evaluation (lem-pc-sheaf-modules-tensor-closed and
   lem-weil-pbc-ringed-topoi-module-pullback-tensor) gives the identity on (FB)^r.
   Evaluation shows naturality under postcomposition and precomposition, including
   matrices of nonconstant sections. Conjugation by a basis isomorphism proves the
   same for terms that are merely isomorphic to finite free modules.
3. The degree m Hom complex has finitely many possibly nonzero factors
   Hom(P^i,N^(i+m)), since P is bounded. Apply the finite-sum pullback comparison and
   the maps of step 2. Their direct sum commutes with d_N h - (-1)^m h d_P by the
   two naturality identities, so it is a chain isomorphism. Equivalently, the dual
   has degree r term (P^(-r))^dual and differential (-1)^(r+1) times precomposition;
   the dual-tensor map on degrees r,s has sign (-1)^(r*s).
4. The canonical bounded-free RHom model (lem-weil-pbc-ringed-site-bounded-free-rhom-model,
   Stacks 08JI) applies on both sites: P is bounded above and N bounded below,
   and every free term is a summand of itself. Pullback preserves both bounds and
   freeness. Localize the chain isomorphism of step 3 and compose the canonical
   model identifications. No flatness or finite Tor condition on N is used.
5. On every summand, evaluation sends (h,x) to h(x). The defining currying equation
   of step 2 identifies evaluation after the chain comparison with pulled-back
   evaluation. The differential terms cancel, so evaluation is a chain map.
   Postcomposition into a K-injective resolution respects this equality termwise.
   Thus the localized chain isomorphism, conjugated by the canonical model maps,
   is precisely siteComparisonEvaluationHom, whose data are pulled-back evaluation.
   Every factor in that model description is invertible by steps 3 and 4. -/
theorem isIso_finiteFreeHomComparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) (T : Scheme.{u})
    (_hinv : IsUnit (l : T.presheaf.obj (op ⊤)))
    (P N : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ℤ)
    (_hP : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (_hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ ∐ fun _ : Fin r ↦
      (constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
          (ModuleCat.of (Padic.coefficientExtensionRing l E n)
            (Padic.coefficientExtensionRing l E n))))
    (_hN : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (N.X i))
    (_hc : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) T (_root_.DerivedCategory.Q.obj N)) :
    IsIso (siteComparisonEvaluationHom
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) T
      (_root_.DerivedCategory.Q.obj P) (_root_.DerivedCategory.Q.obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale
