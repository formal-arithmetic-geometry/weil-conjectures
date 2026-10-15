/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.SetTheory.Cardinal.Finite
import Sheaf.Paper.StrictlyHenselianEtaleAcyclic
import Sheaf.AlgebraicGeometry.StrictlyHenselianConstantHZero

/-!
# Constant étale cohomology of a strictly henselian local scheme

Source: blueprint, `sec-smooth-base-change/sk-rem-rest`, lemma
`sbc-lem-strict-henselian-constant-cohomology`; Stacks Project, Tag 03QO
(blueprint: sbc-lem-strict-henselian-constant-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The cohomology of a finite constant abelian étale sheaf on the spectrum of a strictly
henselian local ring, with coefficient order invertible in the ring, is its coefficient
group in degree zero and vanishes in every positive degree.
Source: blueprint, `sec-smooth-base-change/sk-rem-rest`, lemma
`sbc-lem-strict-henselian-constant-cohomology`; Stacks Project, Tag 03QO
(blueprint: sbc-lem-strict-henselian-constant-cohomology).

Proof:
1. For each positive degree `q`, apply the vanishing clause of
   `lem-weil-pbc-strictly-henselian-etale-acyclic` to `Spec R` and the constant sheaf
   with value `A`. Since `q > 0`, its integer degree is at least one.
2. In degree zero, apply `lem-sbc-strict-henselian-constant-hzero` to `R` and evaluate
   its natural isomorphism at `A`. This gives the additive identification with `A`. -/
theorem constantSheaf_cohomology_of_isStrictlyHenselianLocalRing
    (R : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R]
    (A : AddCommGrpCat.{u + 1}) [Finite A] (_hA : IsUnit (Nat.card A : R)) :
    Nonempty
        (((cohomology AddCommGrpCat.{u + 1} (Spec (CommRingCat.of R)) 0).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology
                AddCommGrpCat.{u + 1}) 0).obj
              ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology
                AddCommGrpCat.{u + 1}).obj A))) ≅ A) ∧
      ∀ (q : ℕ), 0 < q →
        IsZero
          ((cohomology AddCommGrpCat.{u + 1} (Spec (CommRingCat.of R)) (q : ℤ)).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology
                AddCommGrpCat.{u + 1}) 0).obj
              ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology
                AddCommGrpCat.{u + 1}).obj A))) := by
  sorry

end AlgebraicGeometry.Etale
