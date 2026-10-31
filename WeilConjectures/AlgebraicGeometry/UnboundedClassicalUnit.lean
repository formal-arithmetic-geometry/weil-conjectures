/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonDerived
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

set_option autoImplicit false

/-!
# The unbounded unit for finite coefficients

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-proetale-coefficients/sec-pe-unbounded/
`sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`
(blueprint: det-pe-unbounded-classical-unit).

The theorem states that the canonical unbounded derived adjunction between the
finite-coefficient étale and pro-étale module categories has invertible unit on
every object. Its consequences are full faithfulness of the comparison functor and
preservation of arbitrary direct sums.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Transport the Grothendieck structure through the canonical coefficient realization.
Source: the module categories in step 1 of the unit proof
(blueprint: det-pe-unbounded-classical-unit). -/
noncomputable instance finiteCoefficientModulesGrothendieckForUnit
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] :
    IsGrothendieckAbelian.{u + 1} (FiniteCoefficientModules T A) :=
  IsGrothendieckAbelian.of_equivalence (finiteCoefficientRealization T A).asEquivalence

/-- For a finite or algebraically closed field and a finite primary coefficient ring,
the unbounded derived unit from étale to pro-étale coefficients is invertible on every
complex. Consequently the comparison is fully faithful and preserves arbitrary direct
sums. Source: blueprint, `sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`
(blueprint: det-pe-unbounded-classical-unit).

Proof (the nine steps of the node):
1. Use exactness of the comparison inverse image and the classical module
   equivalence to identify the derived comparison functor and its classical
   cohomology.
2. Construct the unbounded derived adjunction by the K-injective right derived
   direct image; its unit is the displayed canonical unit.
3. Evaluate at affine étale objects and identify the localized pro-étale site.
4. Apply the uniform finite-coefficient affine cohomological bound and bounded-below
   comparison to obtain the fixed-degree truncation bound.
5. Truncate on the étale side in a fixed degree using Tag 07K7.
6. Apply the corresponding pro-étale truncation statement to the classical image.
7. Compare the actual derived unit with the bounded-below comparison unit by
   naturality and the pullback normalization.
8. Sheafify the sectionwise cohomology comparison to conclude that the unit is an
   isomorphism.
9. Use the adjunction criterion for full faithfulness and preservation of all small
   colimits by a left adjoint.
-/
theorem unboundedClassicalUnit
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    (∀ K : FiniteCoefficientEtaleDerivedCategory X A,
      IsIso
        (((finiteCoefficientComparisonAdjunction X A).mapDerivedCategoryRightDerivedAdjunction
          |>.unit.app K))) ∧
      Nonempty (finiteCoefficientDerivedComparison X A).FullyFaithful ∧
      ∀ (I : Type v),
        Nonempty (PreservesColimitsOfShape (Discrete I)
          (finiteCoefficientDerivedComparison X A)) := by
  sorry

end AlgebraicGeometry.ProEtale
