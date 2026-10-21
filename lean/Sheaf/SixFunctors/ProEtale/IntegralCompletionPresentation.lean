/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding
public import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Paper.IntegralReductionTowerCanonical
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.CategoryTheory.SheafTensorStructure
import Sheaf.CategoryTheory.SheafTensor

/-! # Canonical completeness in the completed integral presentation

Source: blueprint main-20261015, integral-criterion-reductions, final sentence;
Stacks Project, Tags 06YY, 0941, 08TC and 0145
(blueprint: lem-pe-integral-completion-presentation).

The coefficient identification is normalized by every finite restriction square.
Finite comparisons retain their finite coefficient action.
Their restriction squares are normalized on underlying abelian sheaves, and their
units fix the derived comparisons uniquely. The index n denotes exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u d

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (A : Encoding l E X)

/-- The existing finite continuous-to-constant encoding, at exponent n+1.
Source: blueprint integral-limit and finite-coefficient conventions; Stacks 00YV
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev FiniteEncoding (n : ℕ) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X

/-- The restriction square for the specified integral and finite coefficient encodings.
Source: blueprint integral-criterion comparison; Stacks 06YY
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev RestrictionSquare (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
    e.ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n

/-- Normalization fixes the restriction square on every underlying abelian sheaf.
The right side is the identity section-action map, expressed using the encoding's
recorded equality with its concrete section functor.
Source: Stacks 06YY, identity on sections under scalar relabelling
(blueprint: lem-pe-integral-completion-presentation). -/
def SquareNormalized (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (AdicCompletion.finiteRing l E X n),
    (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
        (a.hom.app M) =
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
          (eqToIso (congrArg (fun F ↦ F.obj
            ((Mod.comap (AdicCompletion.quotient l E X n)).obj M)) A.functor_eq)).hom ≫
        (SheafOfModules.toSheaf (integralCoefficientSheaf.{u, u} l E X n)).map
        (eqToIso (congrArg (fun F ↦ F.obj M) e.ordinary_functor)).inv

/-- Localize the actual restriction square; both composition comparisons are Mathlib's
canonical localization comparisons.
Source: Stacks 05RU and 06YY
(blueprint: lem-pe-integral-completion-presentation). -/
def derivedSquare (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    AdicCompletion.restrict l E X n ⋙ A.derived.functor ≅
      e.ordinaryDerived.functor ⋙ scalarReductionDerivedRestriction.{u, u} l E X n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI := scalarReductionRestrictionLimits.{u, u} l E X n
  letI := scalarReductionRestrictionColimits.{u, u} l E X n
  (Functor.mapDerivedCategoryCompIso
    (Mod.comap (AdicCompletion.quotient l E X n)) (A.modules.functor)).symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫
      Functor.mapDerivedCategoryCompIso e.ordinary.functor
        (scalarReductionRestriction.{u, u} l E X n)

/-- A comparison in D(R_n), retaining the finite coefficient action.
Source: Stacks 06YY, derived tensor under an isomorphism of coefficients
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev FiniteComparison (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  A.derived.functor ⋙
      scalarReductionDerivedExtension.{u, u} l E X n ≅
    AdicCompletion.derivedReduction l E X n ⋙ e.ordinaryDerived.functor

/-- Restrict a finite comparison to the one completed integral derived category.
Source: Stacks 06YY; blueprint integral-criterion comparison
(blueprint: lem-pe-integral-completion-presentation). -/
def restrictedComparison (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) (b : FiniteComparison l E X A n e)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) :
    (sfDerivedReductionRestricted l E X n).obj
        (A.derived.functor.obj K) ≅
      A.derived.functor.obj
        (AdicCompletion.integralLevel l E X K n) :=
  (scalarReductionDerivedRestriction.{u, u} l E X n).mapIso (b.app K) ≪≫
    ((derivedSquare l E X A n e a).app ((AdicCompletion.derivedReduction l E X n).obj K)).symm

/-- Unit normalization of a finite derived comparison. Since derived tensor is left
adjoint to restriction, this equation fixes the finite comparison uniquely.
Source: Stacks 06YY, canonical tensor unit
(blueprint: lem-pe-integral-completion-presentation). -/
def UnitCompatible (n : ℕ) (e : FiniteEncoding l E X n)
    (a : RestrictionSquare l E X A n e) (b : FiniteComparison l E X A n e) : Prop :=
  ∀ K : DerivedCategory (AdicCompletion.Modules l E X),
    (sfDerivedReductionUnit l E X n).app
        (A.derived.functor.obj K) ≫
      (restrictedComparison l E X A n e a b K).hom =
        A.derived.functor.map
          ((Mod.derivedExtendMapDerivedCategoryAdjunction
            (AdicCompletion.quotient l E X n)).unit.app K)

/-- Canonical finite reductions agree, with their actual units and quotient transitions.
There is no completeness, constructibility, boundedness or Noetherian hypothesis here.
Source: blueprint integral-criterion-reductions, final sentence; Stacks 06YY
(blueprint: lem-pe-integral-completion-presentation).

Proof:
1. Use the finite-quotient theorem to identify continuous finite coefficients with
   constant coefficients. Choose their normalized section-action encodings.
2. The normalized integral-limit map alpha has b_n = pi_n alpha. Restricting the
   finite encoding and integral encoding therefore gives the same scalar action.
   Identity on the underlying sections gives the normalized restriction squares.
3. Localize these exact squares. Uniqueness of left adjoints gives the finite
   comparison in D(R_n), uniquely fixed by the tensor-unit equation. On a K-flat
   representative it sends p tensor r to p tensor r: the balancing relations are
   identical because b_n = pi_n alpha. Thus this is the canonical derived comparison.
4. The consecutive quotient sends p tensor r to p tensor rho_n(r) on either side.
   Hence the finite comparisons respect transitions; localization and restriction
   give exactly the displayed transition equation. These formulas work at every
   positive level, for unbounded K and for the zero complex as well. -/
theorem integral_completion_reduction_comparisons :
    ∃ (A : Encoding l E X) (e : ∀ n : ℕ, FiniteEncoding l E X n)
      (a : ∀ n : ℕ, RestrictionSquare l E X A n (e n)),
      (∀ n : ℕ, SquareNormalized l E X A n (e n) (a n)) ∧
      ∃ b : ∀ n : ℕ, FiniteComparison l E X A n (e n),
        (∀ n : ℕ, UnitCompatible l E X A n (e n) (a n) (b n)) ∧
        (∀ (n : ℕ) (b' : FiniteComparison l E X A n (e n)),
          UnitCompatible l E X A n (e n) (a n) b' → b' = b n) ∧
        ∀ (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ),
          (sfDerivedReductionTransition l E X n).app
              (A.derived.functor.obj K) ≫
            (restrictedComparison l E X A n (e n) (a n) (b n) K).hom =
          (restrictedComparison l E X A (n + 1) (e (n + 1)) (a (n + 1)) (b (n + 1)) K).hom ≫
            A.derived.functor.map
              (AdicCompletion.integralStep l E X K n) := by
  sorry

/-- A canonically complete complex gives the distinguished Roos triangle with first
map the product of its completed-coefficient reductions. In the global coefficient
setting it satisfies exactly the recorded completed integral completeness predicate.
Source: blueprint integral-criterion-reductions, final sentence; Stacks 0941, 08TC, 0145
(blueprint: lem-pe-integral-completion-presentation).

Proof:
1. Write alpha for A.ringIso. Its finite restriction squares give exactly the
   normalized integral-limit comparison. Relabelling scalars by alpha inverse and the
   internal-to-sectionwise
   equivalence preserve the underlying sheaves, kernels, cokernels and cone triangles.
2. Resolve K by a flat-term K-flat complex P. The internal/sectionwise tensor comparison
   identifies the two tensor products and preserves K-flatness. The preceding finite
   comparisons identify all reductions, units and transitions on these representatives.
3. Exact countable products identify the termwise product V of the reductions with
   their derived-category product. Cone(1-s)[-1] supplies the distinguished Roos triangle.
   The strict augmentation is (gamma,0), where gamma is the product of the tensor units.
4. The strict-augmentation clause of lem-weil-strict-roos-comparison identifies this
   augmentation with the specified canonical completion map, including its zero
   nullhomotopy. Thus canonical completeness makes the map u from K to this Roos model
   invertible, and its composite with the first Roos arrow is the product of the units.
5. Transport the Roos triangle by (u,id,id); TR1 makes the resulting triangle
   distinguished, with its fixed first map. Relabel coefficients by alpha. The unit
   and transition equations above identify precisely the tower in IsSfDerivedComplete.
6. In the global setting l != D.p, the legacy reduction tower uses these same maps,
   by its K-flat resolution comparisons. Equivalently use sfDerivedComplete_iff_legacy.
   No step requires a bound on K, constructibility, or Noetherianity of X. -/
theorem integral_completion_presentation
    (e : ∀ n : ℕ, FiniteEncoding l E X n)
    (a : ∀ n : ℕ, RestrictionSquare l E X A n (e n))
    (_ha : ∀ n : ℕ, SquareNormalized l E X A n (e n) (a n))
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (_hK : AlgebraicGeometry.ProEtale.IsDerivedComplete l E X K) :
    IsSfDerivedComplete l E X (A.derived.functor.obj K) ∧
      ∀ (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p),
        WeilConjectures.IsDerivedComplete l E X D hl
          (A.derived.functor.obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralPresentation
