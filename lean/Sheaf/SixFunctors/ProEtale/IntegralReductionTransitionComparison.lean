/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding

/-! # Transition compatibility for normalized integral comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
namespace AlgebraicGeometry.ProEtale.IntegralPresentation
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Normalized finite derived comparison maps commute with the actual quotient transitions.
Source: blueprint integral-criterion-reductions, comparison proof step 4;
Stacks 06YY, compatibility of derived base change with quotient maps
(blueprint: lem-pe-integral-reduction-transition-comparison).

Proof: the inverse mate of each restriction square is the unique comparison of left
adjoints normalized by the displayed unit equation. On an internal K-flat representative,
the normalized section reconstruction and coefficient relabelling identify the tensor
balancing relations. The comparison takes s tensor x to s tensor x. Consecutive coefficient
quotients on each side take this tensor to rho(s) tensor x. These formulas agree, including
on zero modules, and tensor generation followed by sheafification gives equality of the
ordinary chain maps. The section equivalence preserves K-flatness, by the internal/section
tensor comparison and relabelling along a ring isomorphism. The universal derived counits
are invertible on these representatives. Their unit normalization identifies the inverse
mate with the localized tensor comparison. The defining representative normalization of
sfDerivedReductionTransition and the internal derived scalar adjunction identify both
localized quotient maps with the transitions in the conclusion. Naturality of all comparisons
transports the equation from the K-flat representative to every derived object. This result
concerns the transitions alone; it asserts neither existence of normalized squares nor any
completeness triangle. -/
theorem integral_completion_transition_comparison (A : Encoding l E X) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (e : ∀ n : ℕ,
      FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X)
      (a : ∀ n : ℕ,
      Mod.comap (AdicCompletion.quotient l E X n) ⋙ A.modules.functor ≅
        (e n).ordinary.functor ⋙ scalarReductionRestriction.{u, u} l E X n),
    let r (n : ℕ) :
        AdicCompletion.restrict l E X n ⋙ A.derived.functor ≅
          (e n).ordinaryDerived.functor ⋙ scalarReductionDerivedRestriction.{u, u} l E X n :=
      letI := HasDerivedCategory.standard
        (FiniteDiscreteOrdinary.Ordinary (Padic.coefficientExtensionRing l E (n + 1)) X)
      letI := scalarReductionRestrictionLimits.{u, u} l E X n
      letI := scalarReductionRestrictionColimits.{u, u} l E X n
      (Functor.mapDerivedCategoryCompIso
        (Mod.comap (AdicCompletion.quotient l E X n)) A.modules.functor).symm ≪≫
        Functor.mapDerivedCategoryNatIso (a n) ≪≫
        Functor.mapDerivedCategoryCompIso (e n).ordinary.functor
          (scalarReductionRestriction.{u, u} l E X n)
    let c (b : ∀ n : ℕ,
      A.derived.functor ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
        AdicCompletion.derivedReduction l E X n ⋙ (e n).ordinaryDerived.functor)
        (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)) :
        (sfDerivedReductionRestricted l E X n).obj (A.derived.functor.obj K) ≅
          A.derived.functor.obj (AdicCompletion.integralLevel l E X K n) :=
      (scalarReductionDerivedRestriction.{u, u} l E X n).mapIso ((b n).app K) ≪≫
        ((r n).app ((AdicCompletion.derivedReduction l E X n).obj K)).symm
    (∀ (n : ℕ) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (AdicCompletion.finiteRing l E X n)),
      (SheafOfModules.toSheaf (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
          ((a n).hom.app M) =
        (SheafOfModules.toSheaf
          (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).map
            (eqToIso (congrArg (fun F ↦ F.obj
              ((Mod.comap (AdicCompletion.quotient l E X n)).obj M)) A.functor_eq)).hom ≫
          (SheafOfModules.toSheaf (integralCoefficientSheaf.{u, u} l E X n)).map
            (eqToIso (congrArg (fun F ↦ F.obj M) (e n).ordinary_functor)).inv) →
    ∀ (b : ∀ n : ℕ,
      A.derived.functor ⋙ scalarReductionDerivedExtension.{u, u} l E X n ≅
        AdicCompletion.derivedReduction l E X n ⋙ (e n).ordinaryDerived.functor),
      (∀ (n : ℕ) (K : DerivedCategory (AdicCompletion.Modules l E X)),
        (sfDerivedReductionUnit l E X n).app (A.derived.functor.obj K) ≫
          (c b n K).hom = A.derived.functor.map
            ((Mod.derivedExtendMapDerivedCategoryAdjunction
              (AdicCompletion.quotient l E X n)).unit.app K)) →
      ∀ (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ),
        (sfDerivedReductionTransition l E X n).app (A.derived.functor.obj K) ≫
            (c b n K).hom = (c b (n + 1) K).hom ≫
          A.derived.functor.map (AdicCompletion.integralStep l E X K n) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralPresentation
