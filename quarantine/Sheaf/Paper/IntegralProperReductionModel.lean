/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Classical models for finite integral reductions and their proper images -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Finite reductions admit bounded classical models, compatibly with proper image.
Source: blueprint main-20261015, integral proper direct sums, proof (1), finite
reduction and discrete direct-image comparison
(blueprint: lem-sfb-integral-proper-reduction-model).

Proof: The length-one free resolution of the positive quotient identifies derived
reduction with the cone of the uniformizer power. Finite presentation on each stratum
is preserved by this two-term construction. The finite discrete coefficient comparison
identifies its constructible cohomology with classical etale sheaves. Shrink the finite
coefficient ring to a finite type in universe zero for constant coefficient realization,
then transport back along the ring equivalence. Bounded classical derived equivalence
gives L and the first isomorphism, including torsion input.
For the second comparison, use the perfect quotient projection formula to commute
reduction with proper direct image. Restriction of scalars is exact, and forgetting
the action gives the same abelian sheaf. Apply discrete direct-image comparison to
L and then forget finite coefficients. These are ordinary derived images: the
perfect quotient projection formula requires no completed-image convention.
The quotient exponent n+1 is positive; the argument includes n=0 and K=0. -/
theorem integralProperReductionModel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (n : ℕ) :
    let R := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
    let W (Z : Scheme.{u}) := sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1}) ⋙ comparisonUpperStar Ab.{u + 1} Z
    ∃ L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)),
      Nonempty ((Mod.forget (AdicCompletion.ring l E X)).mapDerivedCategory.obj
        (AdicCompletion.integralLevel l E X K n) ≅ (W X).mapDerivedCategory.obj L) ∧
      Nonempty ((Mod.forget (AdicCompletion.ring l E Y)).mapDerivedCategory.obj
        (AdicCompletion.integralLevel l E Y
          ((CondensedRing.moduleObjectDerivedPushforward
            (DerivedNakayama.integerRing l E) p).obj K) n) ≅
        (W Y).mapDerivedCategory.obj
          ((Etale.lowerStar (ModuleCat.{u + 1} R) p).rightDerivedFunctor.obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale
