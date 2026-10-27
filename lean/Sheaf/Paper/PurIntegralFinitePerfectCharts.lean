/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72, SHEAF group T9
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.IntegralStratifiedPerfectModels
public import Sheaf.CategoryTheory.DerivedMorphismPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Finite simultaneous integral perfect charts

Source: Bhatt--Scholze, Proposition 6.6.11, finite covering selection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open ProEtale

/-- The actual completed-ring reduction in the equivalent fixed-module presentation.
Index n denotes the positive exponent n+1. Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purIntegralReduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (K : PbcCompletedDerived T d) (n : ℕ) :=
  (pbcDerivedFunctionRealization T d n).asEquivalence.inverse.obj
    ((pbcCompletedReduction T d n).obj K)

/-- Termwise reduction of a scalar complex along the specified quotient map.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarReductionComplex {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  ((ModuleCat.extendScalars (Ideal.Quotient.mk (d.ideal ^ (n + 1))) :
    ModuleCat.{u + 1} A ⥤ ModuleCat.{u + 1} (PbcQuotient d n)).mapHomologicalComplex
      (.up ℤ)).obj P

/-- Exact restriction of a reduction to an immersed stratum.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purReductionOnStratum {T Z : Scheme.{u}} (g : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : PbcCompletedDerived T d) (n : ℕ) :=
  ((AlgebraicGeometry.ProEtale.upperStar (ModuleCat.{u + 1} (PbcQuotient d n)) g)
    |>.mapDerivedCategory).obj (purIntegralReduction T d K n)

/-- Exact slice restriction of a derived finite-coefficient complex.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purFixedChart (Z : Scheme.{u}) (B : Type (u + 1)) [CommRing B] (U : Z.ProEt)
    (K : _root_.DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} B))) :
    _root_.DerivedCategory (Sheaf ((ProEt.topology Z).over U) (ModuleCat.{u + 1} B)) :=
  (@CategoryTheory.derivedSliceRestriction.{u} Z.ProEt _
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z) B _ U).obj K

/-- A scalar quotient complex realized on the actual localized pro-etale site.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-pur-integral-reduction-uniform-tor). -/
abbrev purScalarComplexOnChart (Z : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (U : Z.ProEt)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (n : ℕ) :=
  (DerivedCategory.Q (C := Sheaf ((ProEt.topology Z).over U)
    (ModuleCat.{u + 1} (PbcQuotient d n)))).obj
      (((constantSheaf ((ProEt.topology Z).over U)
        (ModuleCat.{u + 1} (PbcQuotient d n))).mapHomologicalComplex (.up ℤ)).obj
          (purScalarReductionComplex d P n))

/-- Simultaneous finite perfect charts, chosen before any reduction index.
Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.6.10(1)
(blueprint: lem-pur-integral-finite-perfect-charts).

Proof: apply the actual-valuation-ring local perfect criterion to each family member.
Intersect their finite stratifications by scheme fibre products. Pull back each local
cover and its perfect scalar model through the refinement projections; the normalized
completed-coefficient inverse-image comparison and tensor associativity preserve these
models. Each stratum is Noetherian and quasi-compact, so choose a finite subcover by
quasi-compact pieces, retaining the original scalar model on each selected piece.
Take the minimum of all lower term bounds and the maximum of all upper term bounds,
including zero among both finite sets, to obtain one ordered interval. Restriction
preserves zero terms, so every retained representative has that interval.
The perfect-chart tensor comparison computes all actual reductions by the termwise
quotients on those same charts. For an all-zero family take zero
complexes, the identity stratification, identity charts and [0,0]. For an empty family
the charts are vacuous and the same stratification and interval apply; on the empty
scheme these choices are valid as well. No Tor or etale-origin conclusion is assumed. -/
theorem pur_integral_finite_perfect_charts
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (s : ℕ) (K : Fin s → PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (_hK : ∀ j : Fin s,
      IsPbcBoundedConstructibleComplete T l E (K j)) :
    ∃ a b : ℤ, a ≤ b ∧
      ((∀ j : Fin s, IsZero (K j)) → a = 0 ∧ b = 0) ∧
      ∃ S : Stratification T, 0 < S.n ∧
        (∀ (r : Fin S.n) (j : Fin s),
          ∃ (m : ℕ) (U : Fin m → (S.domain r).ProEt)
            (f : ∀ c : Fin m, U c ⟶ ProEt.mk (𝟙 (S.domain r)))
            (P : Fin m → CochainComplex
              (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) ℤ),
            Presieve.ofArrows U f ∈ (ProEt.precoverage (S.domain r)).coverings _ ∧
            ∀ c : Fin m,
              ((P c).IsStrictlyGE a ∧ (P c).IsStrictlyLE b) ∧
              (∀ q : ℤ, Module.Projective (Padic.coefficientExtensionIntegers l E)
                ((P c).X q) ∧ Module.Finite (Padic.coefficientExtensionIntegers l E)
                  ((P c).X q)) ∧
              Nonempty (integralLocalDerived (S.immersion r)
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)) (U c) (K j) ≅
                integralLocalDerived (S.immersion r)
                  (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)) (U c)
                  ((integralConstantDerived T (pbcPadicCoefficientDatum l E)).obj
                    ((completedConstantQ _).obj (P c)))) ∧
              ∀ n : ℕ,
                Nonempty (purFixedChart (S.domain r)
                  (PbcQuotient (pbcPadicCoefficientDatum l E) n) (U c)
                  (purReductionOnStratum (S.immersion r)
                    (pbcPadicCoefficientDatum l E) (K j) n) ≅
                  purScalarComplexOnChart (S.domain r) (pbcPadicCoefficientDatum l E)
                    (U c) (P c) n)) := by
  sorry

end AlgebraicGeometry.Scheme
