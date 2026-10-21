/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.CompletedRlimFunctor
public import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
import Sheaf.Paper.IntegralCompletedLocalPerfectCriterion
import Sheaf.Paper.StratumCompletionUnitRestriction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Projective
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.CompletedKoszulQuotientComparison
import Sheaf.Paper.KoszulReconstruction

/-!
# Completed tensor in the uniform constructible coefficient category

Source: Bhatt--Scholze, Lemmas 6.5.3--6.5.5 and Proposition 6.6.11;
the common-model and compatible-origin refinement is the additional assertion of
(blueprint: lem-ag-uniform-complete-tensor).

The helpers realize the specified strict Koszul tower and its total right derived
limit, using the published Koszul factors, coefficient transport and inverse limit.
They do not substitute the reflector's product mapping-fiber object for this limit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The actual strict Koszul tensor tower, transported along the canonical completed-ring
comparison. The index m means exponent m+1. For a single generator the two terms are in
[-1,0], and the transition is the generator in degree -1 and identity in degree zero.
Source: Stacks Tags 0913, 0A0A; Bhatt--Scholze Lemma 6.5.5
(blueprint: lem-ag-uniform-complete-tensor). -/
def uniformCompleteTensorKoszulTower (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ :=
  Functor.ofOpSequence
    (X := fun m ↦ ((intrinsicPresentationModulesBack T d).mapHomologicalComplex (.up ℤ)).obj
      (completedKoszulTensor T (intrinsicPresentationDatum d) r a
        ((intrinsicPresentationComplex T d).obj C) m))
    (fun m ↦ ((intrinsicPresentationModulesBack T d).mapHomologicalComplex (.up ℤ)).map
      (completedKoszulTensorTransition T (intrinsicPresentationDatum d) r a
        ((intrinsicPresentationComplex T d).obj C) m))

/-- Koszul completion as the total right derived inverse limit of the specified strict
complex tower. A genuine representative of K is used. Each Koszul complex is bounded
finite free, so tensor with it already computes derived tensor on any representative.
Source: Stacks Tags 0941, 0A0E; Bhatt--Scholze Lemma 6.5.5
(blueprint: lem-ag-uniform-complete-tensor). -/
def uniformCompleteTensorCompletion (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (K : PbcCompletedDerived T d) : PbcCompletedDerived T d :=
  (completedRlim T (pbcAdicCompletion T d)).obj
    (DerivedCategory.Q.obj
      ((HomologicalComplex.functorEquivalence
        (pbcModules T (pbcAdicCompletion T d)) (.up ℤ) ℕᵒᵖ).inverse.obj
          (uniformCompleteTensorKoszulTower T d r a (DerivedCategory.Q.objPreimage K))))

/-- Koszul completed derived tensor preserves the full uniform constructible category,
including common local adic-lisse models and compatible etale-origin witnesses.

Source: Bhatt--Scholze, Lemma 6.5.5 with Lemmas 6.5.3--6.5.4 and Proposition 6.6.11;
the refinement to the specified uniform category is an additional lemma
(blueprint: lem-ag-uniform-complete-tensor).

Proof plan:
1. Apply lem-weil-pbc-integral-completed-local-perfect-criterion to both inputs. Refine
   their finite stratifications by scheme-theoretic intersections and their pro-etale
   covers by fiber products. Lem-weil-pbc-stratum-completion-unit-restriction identifies
   the actual restricted coefficient ring with the completed coefficient ring there.
   Lem-weil-pbc-ringed-topoi-derived-tensor-pullback preserves the realized models.
2. Choose bounded finite-projective representatives P and Q. A finite projective module
   is a retract of a finite free module, by def-weil-finitely-generated-module and
   def-weil-pbc-projective-module. Tensor the retractions to show every term of their
   signed total tensor is finite projective; its interval is [a+c,b+d]. The bounded-flat
   K-flat criterion lem-pc-bounded-above-flat-kflat-site and the representative comparison
   lem-pc-source-kflat-module-tensor-model compute the derived tensor by this totalization.
3. Derived tensor pullback identifies the restricted ordinary tensor with the scalar
   extension of P tensor Q. The multiplication map (b tensor p) tensor (c tensor q) to
   bc tensor (p tensor q), with inverse b tensor (p tensor q) to (b tensor p) tensor
   (1 tensor q), supplies the scalar-extension comparison on these representatives.
   Thus the ordinary tensor has stratified local perfect models. The reverse local
   perfect criterion supplies intrinsic completeness, uniform reductions and origins.
4. Use lem-weil-pbc-completed-koszul-quotient-comparison for r=1 and the uniformizer
   to compare the intrinsic unit with the strict quotient-completion unit. Then
   prop-weil-pbc-koszul-reconstruction compares this with the strict Koszul unit used
   here; both preserve the specified degree-zero maps. Hence that unit is invertible.
   For every n, tensoring the unit gives an isomorphism t_n from the ordinary tensor's
   reduction to the completed tensor's reduction. Keep its etale witnesses and beta maps,
   and compose alpha_n with t_n. Naturality of scalar extension preserves all normalized
   witness squares and quotient cocycles. Compose the local model comparisons with
   the inverses of restricted t_n; the same naturality proves their transition squares.
   Bounds and lisse cohomology are unchanged. Naturality of the reflector unit gives
   completeness of the output; the two unit comparisons transfer it back to intrinsic
   completeness. These are precisely the three clauses of the stated category. -/
theorem uniformCompleteTensor_mem
    (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [IsNoetherian T] (hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (hl : IsUnit (l : Γ(T, ⊤)))
    (M N : pbcBoundedConstructibleComplete T l E hdim hl) :
    IsPbcBoundedConstructibleComplete T l E
      (uniformCompleteTensorCompletion T (pbcPadicCoefficientDatum l E) 1
        (fun _ : Fin 1 ↦ Padic.coefficientExtensionUniformizer l E)
        ((SheafOfModules.siteDerivedTensorIndependentCoefficients
          (ProEt.topology T) (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))).obj
            (M.obj, N.obj))) := by
  sorry

end AlgebraicGeometry.Scheme
