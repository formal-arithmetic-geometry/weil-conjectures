/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.StalkConstructibilityCriterion
import Sheaf.Paper.ProjectiveCurveBettiCardinalities
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-!
# Constant-coefficient finiteness for projective smooth curves

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
thm-fin-projective-smooth-curve-finiteness
(blueprint: thm-fin-projective-smooth-curve-finiteness).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Higher direct images of the constant prime field sheaf under a smooth projective
relative curve over a Noetherian scheme are constructible as module sheaves.

Source: blueprint, sec-smooth-purity/sk-prop-sf-cbc,
thm-fin-projective-smooth-curve-finiteness
(blueprint: thm-fin-projective-smooth-curve-finiteness).

Proof:
1. Projectivity implies properness (lem-pc-projective-proper). The constant sheaf
with value the prime field is finite over the finite coefficient ring.
2. Proper base change (cor-weil-pbc-geometric-fiber-finite) identifies each geometric
stalk of the degree-r higher direct image with degree-r cohomology of the geometric
fibre with constant prime field coefficients. Pullback preserves constant sheaves.
3. Apply lem-fin-projective-curve-betti-cardinalities: these cohomology groups are
finite and their cardinality level sets are constructible, since the morphism is
smooth projective of relative dimension one and the prime is invertible on the base.
4. Apply fin4-lem-stalk-constructibility-criterion to obtain a finite locally closed
constructible partition on which the abelian sheaf is finite locally constant.
The additive trivializations are prime-field linear: multiplication by a residue
class modulo the prime is repeated addition. This gives module constructibility
in every degree r. -/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_constant_of_projective_smooth_curve
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S)
    [IsProjective f] [SmoothOfRelativeDimension 1 f]
    (ℓ : ℕ) [Fact ℓ.Prime] (hinv : IsUnit (ℓ : Γ(S, ⊤))) (r : ℕ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (r : ℤ)).obj
        ((Etale.rightDerivedLowerStarPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
            0).obj
            ((constantSheaf X.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ))))))) := by
  sorry

end AlgebraicGeometry
