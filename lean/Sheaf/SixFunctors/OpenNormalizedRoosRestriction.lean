/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y8
-/
module

public import Sheaf.SixFunctors.AugmentedStrictIntegralCompletion

/-! # OpenNormalizedRoosRestriction

Source: Stacks Project, proetale.tex, Tag 099N (2),(5), and sites-cohomology.tex,
Tags 0G7E and 07A4 (blueprint: lem-sf-open-normalized-roos-restriction).
The index n denotes exponent n+1. Site and coefficient universes are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenQuotientCompletion
open CompletedTowerIndependent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {V W : Scheme.{t}} (e : V ⟶ W) [IsOpenImmersion e]
  (o : IntegralOpenReduction.Operations l E e)

attribute [local irreducible] restrict HasDerivedCategory.standard

/-- Exact open restriction has the signed Roos comparison, and transports the
constant-tower adjunction unit through that comparison.
Source: Stacks Project, Tags 0940, 0941 and 07KC; Tag 099N proof of (5)
(blueprint: lem-sf-open-normalized-roos-restriction).
Proof: completed-module categories have exact countable products on the pro-etale
site. Slice restriction is exact and is right adjoint to extension by zero;
transport through the coefficient equivalence preserves this adjunction. Hence
its canonical product comparison is invertible, with components fixed by product
projections. Apply exactProductFunctorStrictLimit to these two module categories,
the existing total right-derived limits, and their universal computation units.
Its shifted-cone models are the actual roosF. The signed-coordinate formulas
identify its K-injective inclusion with ordinaryRoosMap, by equality of all first
projections and vanishing of the second coordinate. Thus its theta normalization
is exactly the equations below. The same two projection identities characterize
kappa; naturality in strict chain maps gives a natural isomorphism. The descent
clause gives lambda_normalized. Finally apply its strict augmentation clause to
the identity map of a constant tower. The compatible-family Roos map has first
coordinates the identity and zero second coordinate. The normalized comparison
therefore intertwines the two actual constant-tower adjunction units through
the identity-on-diagrams constantRestriction isomorphism. This proves the final
equation on every derived object, independently of any quotient augmentation.
This construction uses no tensor comparison tau and no comparison with the
ordinary module pullback. The formulas are valid for zero complexes, the empty
open and the identity open, with no degree bound or quasi-compactness. -/
theorem openNormalizedRoosRestriction :
    ∃ (thetaW : DerivedCategory.Q ⋙ rlim l E W ≅ roosF ⋙ DerivedCategory.Q)
      (thetaV : DerivedCategory.Q ⋙ rlim l E V ≅ roosF ⋙ DerivedCategory.Q)
      (kappa : roosF (A := Modules l E W) ⋙ restrictCx l E e o ≅
      restrictTowCx l E e o ⋙ roosF (A := Modules l E V))
      (lambda : rlim l E W ⋙ restrictD l E e o ≅ restrictTowD l E e o ⋙ rlim l E V),
      (∀ I : CochainComplex (Towers l E W) ℤ, I.IsKInjective →
        (∀ p : ℤ, Injective (I.X p)) →
        (rlimUnitCx l E W).app I ≫ thetaW.hom.app I =
          DerivedCategory.Q.map (ordinaryRoosMap l E W I)) ∧
      (∀ I : CochainComplex (Towers l E V) ℤ, I.IsKInjective →
        (∀ p : ℤ, Injective (I.X p)) →
        (rlimUnitCx l E V).app I ≫ thetaV.hom.app I =
          DerivedCategory.Q.map (ordinaryRoosMap l E V I)) ∧
      (∀ (N : CochainComplex (Towers l E W) ℤ) (p : ℤ) (n : ℕ),
        (kappa.hom.app N).f (p+1) ≫
            signedCoordinates l E V ((restrictTowCx l E e o).obj N) p ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ ((restrictTowCx l E e o).obj N).asFunctor.obj (op k)) n).f
              (p+1) =
          (restrict l E e o).map (signedCoordinates l E W N p ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f (p+1))) ∧
      (∀ (N : CochainComplex (Towers l E W) ℤ) (p : ℤ) (n : ℕ),
        (kappa.hom.app N).f (p+1) ≫
            signedCoordinates l E V ((restrictTowCx l E e o).obj N) p ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ ((restrictTowCx l E e o).obj N).asFunctor.obj (op k)) n).f p =
          (restrict l E e o).map (signedCoordinates l E W N p ≫ biprod.snd ≫
            (Pi.π (fun k : ℕ ↦ N.asFunctor.obj (op k)) n).f p)) ∧
      (∀ N : CochainComplex (Towers l E W) ℤ,
        (restrictD l E e o).map (thetaW.hom.app N) ≫
            (restrict l E e o).mapDerivedCategoryFactors.hom.app (roosF.obj N) ≫
            DerivedCategory.Q.map (kappa.hom.app N) =
          lambda.hom.app (DerivedCategory.Q.obj N) ≫
            (rlim l E V).map ((restrictTow l E e o).mapDerivedCategoryFactors.hom.app N) ≫
            thetaV.hom.app ((restrictTowCx l E e o).obj N)) ∧
      (∀ H : DerivedCategory (Modules l E W),
        (constantAdjunction l E V).unit.app ((restrictD l E e o).obj H) ≫
            (rlim l E V).map ((constantRestriction l E e o).inv.app H) =
          (restrictD l E e o).map ((constantAdjunction l E W).unit.app H) ≫
            lambda.hom.app ((deltaD l E W).obj H)) := by
  sorry

end WeilConjectures.OpenQuotientCompletion
