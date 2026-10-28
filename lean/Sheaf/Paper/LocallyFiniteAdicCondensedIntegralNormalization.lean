/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCondensedStageData
public import Sheaf.Paper.LocallyFiniteAdicFiniteCondensedRealization

/-! # Integral tensor normalization for the finite condensed realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2).
(blueprint: lem-sf-locally-finite-adic-condensed-integral-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicRealization
attribute [local irreducible] nativeCondensedDerived nativeCondensedModules
open AlgebraicallyClosedCoefficients (Index Coefficient)
open AdicFiniteRealization

/-- The finite condensed tensor realization and a normalized native functor agree on
integral objects and their integral common-field comparisons. This assertion is made
before extending naturality to rational fractions; it contains no finite full-faithfulness
claim and no formula for a general common-stage morphism.

Source: Bhatt--Scholze, Lemma 6.8.2, Proposition 6.8.11(3), Proposition 6.8.14(2)
and Remark 6.8.15, the integral comparison in the finite realization argument.
(blueprint: lem-sf-locally-finite-adic-condensed-integral-normalization).

Proof in words: the finite coefficient encoding reconstructs the section ring of the
condensed finite field. Its finiteIso sends each continuous function to the same function
under the fixed small-field equivalence. The finite leg into the closure, followed by
globalCoefficientIso and padicAlgClSheafToAdicConstantSheaf, evaluates that function by
the embedding of the finite field into PadicAlgCl. The rationalInclusion_normalized
clause of D specifies this same map. For integral coefficients, compare every finite
quotient projection: the finite constants and integral_residues clauses, and the
quotient normalizations of the raw identity and continuous realization, send a section
to its residue. Joint monicity of the inverse-limit projections identifies the completed
integral maps. Restriction along the coefficient isomorphisms leaves underlying sections
unchanged. Transport extension through the specified internal/section scalar adjunction;
its unit equation fixes the balanced comparison. Compose the integral raw-identity
comparison, the integral formula of the continuous realization, and this balanced
comparison. The counit of finiteCondensedEncoding gives the displayed natural integral
isomorphism e. Compose its inverse with D.integral transported through native scalar
forgetting and condensedNativeMap. This is natural on every integral arrow, including
torsion objects, since every comparison is natural before localization.

For E contained in L, substitute D.common_field. The raw inverse-completion scalar
normalization identifies the completion-chain comparison with the one in A.raw. The
integral equation of A.scalar identifies its continuous rational comparison with the
same balanced tensor transposition. The coefficient_normalization of A.closure is the
commuting square of actual field inclusions. The unit normalization of
finiteSectionScalarComparison and the two tensor-composition adjunctions therefore give
finiteCondensedScalarComparison, and extending once more to the closure gives precisely
finiteCondensedClosureTransition. Both composites flatten b tensor (a tensor k) to ba
tensor k on a K-flat representative. The derived universal property makes them equal;
this is the stated integral transition equation. Identity inclusions use multiplication
by one and the actual completion unitor. Empty schemes and rank-zero modules give the
same equations with zero sections. No assertion about rational numerator inverses or
general common-stage representatives is used here.
-/
theorem finiteCondensedIntegralNormalization
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
    [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    (D : NormalizedFunctor l X) (A : AdicFiniteRealization.FiniteCondensedData l X) :
    ∃ e : ∀ E : Index l (PadicAlgCl l),
      sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion E ⋙ D.J ⋙
            nativeCondensedDerived l X ≅
        sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X ⋙
          finiteCondensedClosureFunctor l X A E,
      ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X),
        (D.J ⋙ nativeCondensedDerived l X).map
            ((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).isoToStage
              ⟨E, (sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K⟩ h).hom ≫
          (e L).hom.app
            (((GeneralAlgebraicallyClosedCoefficients.stageSystem l (PadicAlgCl l) X).T h).obj
              ((sfRationalConstructibleLocalization l
                (Coefficient.{u} l (PadicAlgCl l) E) X).obj K)).obj =
          (e E).hom.app K ≫ (finiteCondensedClosureTransition l X A h).hom.app
            ((sfRationalConstructibleLocalization l
              (Coefficient.{u} l (PadicAlgCl l) E) X).obj K) := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
