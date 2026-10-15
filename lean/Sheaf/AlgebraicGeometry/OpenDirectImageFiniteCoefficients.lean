/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.CategoryTheory.TruncationHypercohomology

/-!
# Open direct images with finite allowable coefficients

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
cor-fin-deligne-open-finite-coefficients
(blueprint: cor-fin-deligne-open-finite-coefficients).

Bounded constructibility is the recorded finite-stratification predicate on ordinary
etale derived categories, with no condition on Tor amplitude.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An open immersion of finite-type schemes over a field preserves bounded constructible
complexes with arbitrary finite allowable commutative coefficients.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc,
cor-fin-deligne-open-finite-coefficients
(blueprint: cor-fin-deligne-open-finite-coefficients).

Proof: choose the positive annihilator N invertible in k. If N = 1 the coefficient ring
and all sheaves vanish. Otherwise split an N-torsion constructible sheaf into its finitely
many primary parts using the Chinese-remainder idempotents. Filter each primary part by
powers of its prime. The constructible Serre theorem makes all terms and quotients
constructible. A quotient killed by a prime l is canonically an F_l-sheaf. The prime-field
open-image corollary gives bounded constructible direct image, and the module/abelian
derived-direct-image comparison identifies its underlying abelian cohomology with that
computed using the original coefficients. Faithful exact forgetting detects vanishing.
On each stratum, refine additive trivializations for every pair in the finite set A times
the finite stalk; all scalar action tables then become constant, proving constructibility
with the inherited A-action. The long exact sequence of derived functors and the Serre
property reconstruct bounded constructible direct images through the finite filtrations
and primary sums. For a bounded constructible complex use a bounded below injective
representative and the truncation spectral sequence. Its E2 terms are the higher direct
images of the finitely many cohomology sheaves, so they lie in a finite rectangle. Kernels,
cokernels and extensions keep the stabilized terms and the finite abutment filtrations
constructible. The rectangle bounds the nonzero total degrees, proving boundedness. -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k)))
    {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K) :
    DerivedCategory.isBoundedConstructible A Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj K) := by
  sorry

end AlgebraicGeometry.Etale
