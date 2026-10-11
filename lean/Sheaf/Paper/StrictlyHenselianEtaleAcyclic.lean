/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Etale acyclicity of a strictly henselian local scheme

Source: Stacks Project, etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-etale-acyclic).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

/-- For a strictly henselian local ring, global sections on the small etale site are exact,
and all positive-degree etale cohomology objects vanish.
Source: Stacks Project, etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-etale-acyclic).
-/
theorem strictlyHenselian_etale_acyclic
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) :
    exactFunctor
        (Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology (AlgebraicGeometry.Spec (.of R)))
          AddCommGrpCat.{u + 1})
        AddCommGrpCat.{u + 1}
        (Sheaf.Γ
          (AlgebraicGeometry.Scheme.smallEtaleTopology (AlgebraicGeometry.Spec (.of R)))
          AddCommGrpCat.{u + 1}) ∧
      ∀ (F : Sheaf
          (AlgebraicGeometry.Scheme.smallEtaleTopology (AlgebraicGeometry.Spec (.of R)))
          AddCommGrpCat.{u + 1}) (p : ℤ),
        1 ≤ p →
          IsZero
            ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1}
              (AlgebraicGeometry.Spec (.of R)) p).obj
              ((DerivedCategory.singleFunctor
                (Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
                  (AlgebraicGeometry.Spec (.of R))) AddCommGrpCat.{u + 1}) 0).obj F)) := by
  sorry
