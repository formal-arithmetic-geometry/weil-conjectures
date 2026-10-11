/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.Ample

/-! # Affine opens intersected with section nonvanishing loci

Source: Stacks Project, Properties, Lemma 01PV (properties-lemma-affine-cap-s-open)
(blueprint: lem-sc-affine-cap-section-open).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Intersecting an affine open with the nonvanishing locus of a section of an invertible
module, or of any positive tensor power of it, gives an affine open. The nonvanishing
condition is exactly that the germ lies outside the maximal ideal times the stalk module,
as in `def-weil-pbc-ample-invertible-module`.

Source: Stacks Project, Properties, Lemma 01PV (properties-lemma-affine-cap-s-open)
(blueprint: lem-sc-affine-cap-section-open).

Proof:
1. Restrict the invertible module to the affine scheme `U = Spec R`. The affine dictionary
   (`lem-weil-pbc-affine-tilde-gamma-adjunction` and
   `lem-sc-affine-cap-section-open-dictionary`) identifies it with the sheaf of a finite
   projective rank-one module `N`, and identifies the intersection with the primes `p`
   at which the restricted section is outside `p N`.
2. Apply `lem-sc-affine-cap-section-open-algebra`: this prime locus is affine. Its affine
   model is `Spec (Sym_R N / (s - 1))`, so the intersection is affine.
3. For `n > 0`, the tensor power is invertible
   (`def-weil-pbc-ample-invertible-module`). Apply the first clause to it and to its section.
-/
theorem affine_cap_section_open (X : Scheme.{u}) (M : X.Modules) [M.IsInvertible]
    (s : M.val.presheaf.obj (Opposite.op ⊤)) (U : X.Opens) (hU : IsAffineOpen U) :
    (∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X, x ∈ V ↔ x ∈ U ∧
      (TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial) s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x))) ∧
    (∀ n : ℕ, 0 < n → ∀ t : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤),
      ∃ V : X.Opens, IsAffineOpen V ∧ ∀ x : X, x ∈ V ↔ x ∈ U ∧
        (TopCat.Presheaf.germ (M.tensorPow n).val.presheaf ⊤ x trivial) t ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
            (⊤ : Submodule (X.presheaf.stalk x)
              ↑(TopCat.Presheaf.stalk (M.tensorPow n).val.presheaf x))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
