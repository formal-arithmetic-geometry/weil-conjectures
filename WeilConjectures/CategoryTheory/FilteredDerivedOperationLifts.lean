/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteFilteredLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.Algebra.Category.ModuleCat.AB

public import WeilConjectures.CategoryTheory.FilteredDerivedOperationStructures
import WeilConjectures.CategoryTheory.FilteredDerivedAdjunctionConstruction
import WeilConjectures.CategoryTheory.FilteredExactLocalization
import WeilConjectures.CategoryTheory.ProEtaleFilteredCanonicalConstruction

/-!
# Filtered derived operation lifts

Source: Stacks Tags 015Q–015V, 05TY; Varshavsky Lemma 5.1.4 and §§5.2.1–5.2.2.
(blueprint: lem-trf-filtered-derived-operation-lifts).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe wA vA uA wB vB uB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u

/-- Filtered right-derived operations, exact termwise operations, their canonical
adjunction maps, and the pro-etale compactification and exchange package.

Source: Stacks Tags 015Q, 015S, 05U2, 015U, 015V and 05TY; Varshavsky Lemma 5.1.4
and §§5.2.1–5.2.2 (blueprint: lem-trf-filtered-derived-operation-lifts).

Proof:
1. Apply an exact additive functor to the objects, arrows and filtration inclusions
   degreewise. It preserves the cokernel defining each grade and preserves homology,
   hence graded quasi-isomorphisms. Additivity preserves homotopies, shifts and cones.
   Localizing gives the termwise lift and its displayed localization comparison.
2. Choose filtered-injective resolutions on each finite interval. Every filtration
   on a filtered-injective term splits into a finite sum of injective graded objects.
   Applying T to its filtration inclusions gives a functorial filtration independent
   of splittings. Its graded and total complexes are the images of ordinary injective
   resolutions. Thus the two comparisons compute RT. Shifts and split-sum cones show
   triangulatedness. The same construction works without a fixed interval.
3. For exact L left adjoint to T, T preserves injectives. Compute filtered derived Hom
   with the filtered-injective representative on the right. The ordinary degreewise
   adjunction preserves each filtration condition and transposes filtered homotopies.
   Its natural Hom bijections give the filtered adjunction and triangle identities.
   Their total maps are those of the specified ordinary derived adjunction. Uniqueness
   of supported truncations gives the same equations on every grade.
4. On the small pro-etale sites the constant-coefficient module categories are
   Grothendieck abelian. The recorded realization equivalence identifies fixed-scalar
   sheaves with intrinsic constant-ring modules and transports precisely the recorded
   inverse image, direct image and extension by zero. Apply Steps 1–3 to these canonical
   sheaf functors. For every supplied c=(j,p), take the composite R^Fp_* j_!^F. It has
   the displayed total and graded candidate comparisons. No compactification existence
   or unconditional constructible-domain preservation is used.
5. Descend the canonical sheaf pullback identity/composition comparisons termwise.
   Their identities hold degreewise. Define pushforward/open comparisons by the
   specified adjunction mates. Canonical expressions use these generators, composition
   and whiskering. The comparison equations for generators imply those for expressions.
   The proper square map is exactly its unit–square–counit formula; the open square map
   is the degreewise extension-by-zero mate. The latter is invertible on Cartesian
   squares. A canonical map whose grades are invertible has a cone with zero grades,
   so is invertible in the filtered localization. This also lifts admissible inverses.
6. For a compactification, compose the proper square mate with the open square
   comparison. Refinement maps are the same proper/open mates; in a non-Cartesian
   refinement first project onto the clopen section (identity there, zero on the
   complement), an exact termwise filtration-preserving transformation. Forgetting
   and grading the resulting expressions gives the ordinary canonical expressions.
7. For compatible compactification towers expand both vertical-pasting paths into
   these maps. Proper subrectangles combine by adjunction mate pasting; open ones by
   the degreewise open comparison. Transpose the mixed proper/open cube by the proper
   adjunctions: both paths become the identical pullback/open map. Clopen projections
   commute with pullback and compose by intersection, so refinements intertwine the
   equation as well. This gives the displayed equality with the actual composition
   arrows, and inverting those arrows on the admissible domain gives the node's
   composition-isomorphism form. Every scheme map here is arbitrary over its base.
-/
theorem filteredDerivedOperationLifts
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    [HasDerivedCategory.{wB} B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] :
    (∃ lift : FilteredDerivedOperationLift T.rightDerivedFunctorPlus,
      (∀ (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H],
        Nonempty (FilteredTermwiseLift H)) ∧
      (∀ (L : B ⥤ A) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
        (adj : L ⊣ T), ∃ termwiseLeft : FilteredTermwiseLift L,
        Nonempty (FilteredDerivedAdjunction adj.derivedPlus
          termwiseLeft.toFilteredDerivedOperationLift lift))) ∧
    (∀ (R : Type u) [CommRing R] [Finite R],
      Nonempty (AlgebraicGeometry.ProEtale.ProEtaleFilteredOperationPackage R))  := by
  obtain ⟨lift, hadj⟩ := filteredDerivedAdjunctionConstruction T
  refine ⟨⟨lift, ?_, hadj⟩, ?_⟩
  · intro H _ _ _
    exact exactFilteredLocalization H
  · intro R _ _
    exact AlgebraicGeometry.ProEtale.proEtaleFilteredOperationPackage_exists R

end CategoryTheory
