/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
/-! # Bounded classical descent on coefficient-sized derived categories
Source: blueprint classical derived equivalence, Stacks Tag 09AL.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Cohomology vanishes outside one ordered finite integer interval.
Source: Stacks Tag 05RU (blueprint: lem-pe-coefficient-bounded-classical-descent). -/
def coefficientCohomologyBounded {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (K : ConstantCompletion.D R) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
    IsZero ((coefficientModelCohomology R q).obj K)

/-- Derived comparison is fully faithful between bounded objects, and an object
with bounded classical cohomology has an etale derived antecedent. No constructibility
or finiteness of its cohomology modules is imposed here.
Source: blueprint det-pe-classical-derived-equivalence and sk-prop-sf-comparison;
Stacks Tag 09AL (blueprint: lem-pe-coefficient-bounded-classical-descent).

Proof: use the constant-scalar equivalences, whose units extend the same discrete
scalar actions uniquely through sheafification, to identify canonical intrinsic
comparison with fixed-scalar comparison on the equivalent coefficient-sized sites.
The comparison derived unit is invertible for bounded-below etale complexes.
Consequently comparison induces bijections on all morphisms between bounded-below
objects, in particular between bounded objects. Continuous cohomology is classical;
a bounded target object is therefore also bounded below and
the classical derived equivalence supplies its antecedent as
the derived direct image, with invertible comparison counit. The site equivalences
are exact and identify ordinary derived localization and its cohomology functors.
For any D with the displayed factorization, the universal property of localization
gives a natural isomorphism to this exact derived comparison: precomposition with Q
is fully faithful on functor categories. Transport the morphism bijections and the
counit along that natural isomorphism. The antecedent in the conclusion need not
be asserted bounded here; exactness and faithfulness reflect its finite cohomological
interval in the application. This also covers the zero complex and empty scheme. -/
theorem coefficientComparison_boundedClassical (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (D : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
          ConstantCompletion.D (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
    (hD : Nonempty (ConstantCompletion.Q _ ⋙ D ≅
      constructibleComparisonComplexPullback X A ⋙ ConstantCompletion.Q _)) :
    (∀ K L : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
      coefficientCohomologyBounded _ K → coefficientCohomologyBounded _ L →
        Function.Bijective (D.map : (K ⟶ L) → (D.obj K ⟶ D.obj L))) ∧
    (∀ K : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      coefficientCohomologyBounded _ K →
      (∀ q : ℤ, ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
        (P : AffinePresentation X I),
        IsIso (continuityMap P
          ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
            ((coefficientModelFixedScalars _ A).obj
              ((coefficientModelCohomology _ q).obj K)).obj))) →
      ∃ M, Nonempty (D.obj M ≅ K)) := by sorry
end AlgebraicGeometry.ProEtale
