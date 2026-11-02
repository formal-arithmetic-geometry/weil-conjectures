/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation

import WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralHom.CondensedIntegralHomReductionComparisonIso
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralHom.CondensedIntegralHomReductionCompleteness

/-! # Integral internal Hom and reduction for continuous condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-hom-reduction.md and its proof, order 2975
(blueprint: lem-coef-integral-hom-reduction).

The positive coefficient level n+1 is indexed by n : ℕ, as in AdicCompletion.
The comparison is the transpose of scalar extension of the actual evaluation,
using the canonical derived tensor comparison. No completeness of the source,
constructibility, boundedness, or perfectness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedIntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The canonical K-flat scalar tensor isomorphism at positive coefficient level n+1.
It derives the ordinary balanced scalar tensorator, whose inverse multiplies the
scalar factors. Scalar extension need not be exact.
Source: blueprint proof, first paragraph, scalar extension of evaluation
(blueprint: lem-coef-integral-hom-reduction). -/
def reductionTensorIso (n : ℕ) (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E X n).obj (K ⊗ L) ≅
      (AdicCompletion.derivedReduction l E X n).obj K ⊗
        (AdicCompletion.derivedReduction l E X n).obj L :=
  letI := Mod.extendScalarsMonoidal (AdicCompletion.quotient l E X n)
  letI := Mod.extendScalars_preservesFlat (AdicCompletion.quotient l E X n)
  let τ := asIso
    (Mod.extendScalars (AdicCompletion.quotient l E X n)).leftDerivedTensorComparison
  (τ.app K).app L

/-- Scalar extension of the integral evaluation, after canonical tensor reassociation.
Source: blueprint proof, first paragraph, the evaluation defining c_n
(blueprint: lem-coef-integral-hom-reduction). -/
def reductionEvaluation (n : ℕ) (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E X n).obj K ⊗
        (AdicCompletion.derivedReduction l E X n).obj
          (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L) ⟶
      (AdicCompletion.derivedReduction l E X n).obj L :=
  (reductionTensorIso l E X n K
    (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L)).inv ≫
      (AdicCompletion.derivedReduction l E X n).map
        ((CondensedRing.derivedTensorHomAdjunction
          (DerivedNakayama.integerRing l E) K).counit.app L)

/-- The canonical A_(n+1)-linear Hom reduction arrow, defined by transposing evaluation.
Its invertibility is a conclusion, not part of its construction.
Source: blueprint statement and proof, first paragraph
(blueprint: lem-coef-integral-hom-reduction). -/
def comparison (n : ℕ) (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E X n).obj
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L) ⟶
      ((CondensedRing.derivedHom (DerivedNakayama.quotientRing l E (n + 1)) X).obj
        (op ((AdicCompletion.derivedReduction l E X n).obj K))).obj
          ((AdicCompletion.derivedReduction l E X n).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction (DerivedNakayama.quotientRing l E (n + 1))
    ((AdicCompletion.derivedReduction l E X n).obj K)).homEquiv _ _
      (reductionEvaluation l E X n K L)

end AlgebraicGeometry.ProEtale.CondensedIntegralHom

namespace AlgebraicGeometry.ProEtale.CondensedIntegralHom

/-- Arbitrary unbounded integral internal Hom commutes with every positive reduction,
preserves evaluation and every tensor--Hom transpose, and is complete whenever its
second argument is complete. The coefficients are the pulled-back continuous
condensed rings, and the reductions are the recorded derived scalar extensions.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-hom-reduction.md and its proof, order 2975
(blueprint: lem-coef-integral-hom-reduction).

Proof:
1. Completeness of `Hom(K,L)` for complete `L` is the split statement
   `derivedHom_isDerivedComplete` (blueprint: lem-coef-integral-hom-reduction-completeness):
   apply the exact right adjoint `Hom(K,-)` to the Roos triangle of `L` and identify the
   result with the Roos triangle of `Hom(K,L)` through the finite-free cone comparison.
2. Invertibility of `comparison n K L` at every level is the split statement
   `comparison_isIso` (blueprint: lem-coef-integral-hom-reduction-comparison-isIso):
   the cone `[R --pi^(n+1)--> R]` identifies `Hom(K,L) tensor A_(n+1)` with
   `Hom(K, L tensor A_(n+1))`, extension--restriction identifies the latter with the
   restriction of `Hom_(A_(n+1))(K_(n+1), L_(n+1))`, and restriction is conservative.
3. Evaluation: `comparison` is by definition the quotient tensor--Hom transpose of
   `reductionEvaluation`, so the counit identity `homEquiv_counit` gives the displayed
   evaluation equation.
4. Transposes: the transpose of `(reductionTensorIso K T).inv` followed by the reduction of
   the integral evaluation of `K ◁ f` equals, by naturality of the derived tensor comparison
   `leftDerivedTensorComparison` in its second variable (cancelling its isomorphism), the
   map `reductionEvaluation` precomposed with the reduction of `f`; naturality of
   `homEquiv` in the source then gives the displayed identity for every `f`. -/
theorem integralHomReduction (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (IsDerivedComplete l E X L → IsDerivedComplete l E X
      (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L)) ∧
    ∀ n : ℕ, IsIso (comparison l E X n K L) ∧
      ((AdicCompletion.derivedReduction l E X n).obj K ◁ comparison l E X n K L) ≫
        (CondensedRing.derivedTensorHomAdjunction (DerivedNakayama.quotientRing l E (n + 1))
          ((AdicCompletion.derivedReduction l E X n).obj K)).counit.app
            ((AdicCompletion.derivedReduction l E X n).obj L) =
        reductionEvaluation l E X n K L ∧
      ∀ (T : DerivedCategory (AdicCompletion.Modules l E X))
        (f : T ⟶
          (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L)),
        (CondensedRing.derivedTensorHomAdjunction (DerivedNakayama.quotientRing l E (n + 1))
          ((AdicCompletion.derivedReduction l E X n).obj K)).homEquiv _ _
            ((reductionTensorIso l E X n K T).inv ≫
              (AdicCompletion.derivedReduction l E X n).map
                (((CondensedRing.derivedTensorHomAdjunction
                  (DerivedNakayama.integerRing l E) K).homEquiv T L).symm f)) =
          (AdicCompletion.derivedReduction l E X n).map f ≫ comparison l E X n K L := by
  constructor
  · intro hL
    exact derivedHom_isDerivedComplete l E X K L hL
  · intro n
    constructor
    · exact comparison_isIso l E X n K L
    constructor
    · let adj := CondensedRing.derivedTensorHomAdjunction
        (DerivedNakayama.quotientRing l E (n + 1))
        ((AdicCompletion.derivedReduction l E X n).obj K)
      change ((CondensedRing.derivedTensor
          (DerivedNakayama.quotientRing l E (n + 1)) X).obj
          ((AdicCompletion.derivedReduction l E X n).obj K)).map
          (comparison l E X n K L) ≫ adj.counit.app _ = _
      rw [← adj.homEquiv_counit (g := comparison l E X n K L)]
      exact (adj.homEquiv _ _).symm_apply_apply _
    · intro T f
      let adjS := CondensedRing.derivedTensorHomAdjunction
        (DerivedNakayama.quotientRing l E (n + 1))
        ((AdicCompletion.derivedReduction l E X n).obj K)
      let adjR := CondensedRing.derivedTensorHomAdjunction
        (DerivedNakayama.integerRing l E) K
      dsimp only [comparison]
      rw [← adjS.homEquiv_naturality_left]
      change (adjS.homEquiv ((AdicCompletion.derivedReduction l E X n).obj T)
        ((AdicCompletion.derivedReduction l E X n).obj L)) _ =
        (adjS.homEquiv ((AdicCompletion.derivedReduction l E X n).obj T)
          ((AdicCompletion.derivedReduction l E X n).obj L)) _
      rw [Equiv.apply_eq_iff_eq]
      letI := Mod.extendScalarsMonoidal (AdicCompletion.quotient l E X n)
      letI := Mod.extendScalars_preservesFlat (AdicCompletion.quotient l E X n)
      let τ := (Mod.extendScalars (AdicCompletion.quotient l E X n)).leftDerivedTensorComparison
      have hc := (τ.app K).naturality f
      change (AdicCompletion.derivedReduction l E X n).map (K ◁ f) ≫
          (τ.app K).app
            (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
              (op K)).obj L) =
        (τ.app K).app T ≫
          ((AdicCompletion.derivedReduction l E X n).obj K ◁
            (AdicCompletion.derivedReduction l E X n).map f) at hc
      have hc' :
          (AdicCompletion.derivedReduction l E X n).map (K ◁ f) ≫
              (reductionTensorIso l E X n K
                (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
                  (op K)).obj L)).hom =
            (reductionTensorIso l E X n K T).hom ≫
              ((AdicCompletion.derivedReduction l E X n).obj K ◁
                (AdicCompletion.derivedReduction l E X n).map f) := by
        simpa only [reductionTensorIso, asIso_hom, Iso.app_hom] using hc
      have hci :
          (reductionTensorIso l E X n K T).inv ≫
              (AdicCompletion.derivedReduction l E X n).map
                (K ◁ f) =
            ((AdicCompletion.derivedReduction l E X n).obj K ◁
                (AdicCompletion.derivedReduction l E X n).map f) ≫
              (reductionTensorIso l E X n K
                (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
                  (op K)).obj L)).inv := by
        apply (cancel_mono (reductionTensorIso l E X n K
          (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
            (op K)).obj L)).hom).1
        change ((reductionTensorIso l E X n K T).inv ≫
            (AdicCompletion.derivedReduction l E X n).map (K ◁ f)) ≫
            (reductionTensorIso l E X n K
              (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
                (op K)).obj L)).hom =
          (((AdicCompletion.derivedReduction l E X n).obj K ◁
            (AdicCompletion.derivedReduction l E X n).map f) ≫
            (reductionTensorIso l E X n K
              (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
                (op K)).obj L)).inv) ≫
            (reductionTensorIso l E X n K
              (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
                (op K)).obj L)).hom
        calc
          _ = (reductionTensorIso l E X n K T).inv ≫
              ((AdicCompletion.derivedReduction l E X n).map (K ◁ f) ≫
                (reductionTensorIso l E X n K
                  (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
                    (op K)).obj L)).hom) := by simp only [Category.assoc]
          _ = (reductionTensorIso l E X n K T).inv ≫
              ((reductionTensorIso l E X n K T).hom ≫
                ((AdicCompletion.derivedReduction l E X n).obj K ◁
                  (AdicCompletion.derivedReduction l E X n).map f)) := by rw [hc']
          _ = (AdicCompletion.derivedReduction l E X n).obj K ◁
              (AdicCompletion.derivedReduction l E X n).map f := by
            rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
          _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [Adjunction.homEquiv_counit, Functor.map_comp]
      dsimp only [reductionEvaluation]
      change (reductionTensorIso l E X n K T).inv ≫
          (AdicCompletion.derivedReduction l E X n).map (K ◁ f) ≫
          (AdicCompletion.derivedReduction l E X n).map
            ((CondensedRing.derivedTensorHomAdjunction
              (DerivedNakayama.integerRing l E) K).counit.app L) =
        ((AdicCompletion.derivedReduction l E X n).obj K ◁
          (AdicCompletion.derivedReduction l E X n).map f) ≫
          (reductionTensorIso l E X n K
            (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
              (op K)).obj L)).inv ≫
          (AdicCompletion.derivedReduction l E X n).map
            ((CondensedRing.derivedTensorHomAdjunction
              (DerivedNakayama.integerRing l E) K).counit.app L)
      rw [← Category.assoc, hci]
      simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedIntegralHom
