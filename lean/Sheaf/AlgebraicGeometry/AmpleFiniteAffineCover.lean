/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.AlgebraicGeometry.Ample

/-! # A finite affine cover from an ample invertible module

Source: Stacks Project, Properties, Definition 01PS and the first paragraph of
Lemma 01Q1's proof (blueprint: lem-sc-ample-finite-affine-cover).
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample invertible module admits finitely many positive tensor powers with global
sections whose affine nonvanishing loci cover the scheme.
Source: Stacks Project, Properties, Definition 01PS and Lemma 01Q1, first proof paragraph
(blueprint: lem-sc-ample-finite-affine-cover).

Proof: For each point, condition (2) of `def-weil-pbc-ample-invertible-module` supplies
an affine open nonvanishing locus of a section of a positive tensor power containing
that point. These open loci cover `X`. Condition (1) of the same definition makes `X`
quasi-compact. By `def-weil-pbc-quasi-compact-scheme`, this open cover has a finite
subcover. Enumerate that subcover by `Fin m`, retaining the powers, sections, positivity
and affineness. Every point then lies in one of the retained loci. For empty `X`, the
empty subcover (`m = 0`) is allowed. -/
theorem IsAmple.exists_finite_affine_cover (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible] (hL : IsAmple X L) :
    ∃ (m : ℕ) (n : Fin m → ℕ)
      (s : (i : Fin m) → (L.tensorPow (n i)).val.presheaf.obj (Opposite.op ⊤))
      (U : Fin m → X.Opens),
      (∀ i : Fin m, 0 < n i) ∧
      (∀ i : Fin m, IsAffineOpen (U i)) ∧
      (∀ (i : Fin m) (x : X), x ∈ U i ↔
        (TopCat.Presheaf.germ (L.tensorPow (n i)).val.presheaf ⊤ x trivial) (s i) ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              ↑(TopCat.Presheaf.stalk (L.tensorPow (n i)).val.presheaf x))) ∧
      (∀ x : X, ∃ i : Fin m, x ∈ U i) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
