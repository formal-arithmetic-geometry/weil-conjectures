/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Data.List.TFAE

/-!
# Torsion sections detected at the generic point

Source: Stacks Project, Divisors, Tag 0AXR, lemma-torsion-sections
(blueprint: lem-sc-torsion-sections-generic).

The generic skyscraper realizes `j_* F_eta`: its sections are the generic stalk on any
nonempty open, and zero on the empty open. Its canonical map is `toSkyscraper` of the identity.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- The four torsion-section criteria for a quasi-coherent module on an integral scheme.
Stalks, germs and torsion are written as in `lem-sc-torsion-subsheaf-quotient`: `F_x` is
`F.presheaf.stalk x` with its `𝒪_{X,x}`-module structure (the carrier and action of
`RingedSpace.moduleStalkFunctor`, def-pc-module-stalk-functor).
Source: Stacks Project, Divisors, Tag 0AXR, lemma-torsion-sections
(blueprint: lem-sc-torsion-sections-generic).

Proof:
1. Around x choose an affine W = Spec A with F represented by an A-module M, using
`pqf-def-coherent`. Choose x ∈ D(f) ⊆ W ∩ U; this nonempty open also contains η.
By `lem-weil-pbc-spec-module-tilde-sections`, clear a power of f to represent the restriction
of s by m ∈ M. Since f has unit germs at x and η, this preserves torsion and generic
vanishing. Use `lem-weil-pbc-spec-tilde-stalk-localization` at the prime of x and at (0),
and `lem-sc-integral-scheme-stalks-in-function-field` to identify the generic localization.
2. If s_η = 0, localization gives a nonzero a ∈ A with am = 0. Its germ at x is nonzero
by the injectivity in `lem-sc-integral-scheme-stalks-in-function-field`, and annihilates s_x
by the scalar law of `def-weil-pbc-module-stalk`. Thus (3) implies (2).
3. If a nonzero b ∈ O_{X,x} kills s_x, its image in k(X) is nonzero by the same injectivity,
and is a unit by `def-sc-function-field`. Compatibility of module germs
(`def-weil-pbc-module-stalk`) gives b s_η = 0, hence s_η = 0. Thus (1) implies (3).
4. Nonemptiness of U gives (2) implies (1). Also η ∈ U and 1 kills a zero generic germ.
For j : Spec k(X) → X, the inverse image of U is the one-point source, so the generic
skyscraper has sections F_η there. The canonical `toSkyscraper` map sends s to the function
with value s_η at every membership proof; it is zero exactly when s_η = 0. Thus (3) and (4)
are equivalent, completing all four equivalences. -/
theorem torsion_sections_generic
    (X : Scheme.{u}) [IsIntegral X] (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) [Nonempty U] (s : Γ(F, U)) :
    List.TFAE [
      (∃ x : U, ∃ a : X.presheaf.stalk x, a ≠ 0 ∧ a • F.presheaf.germ U x x.property s = 0),
      (∀ x : U, ∃ a : X.presheaf.stalk x, a ≠ 0 ∧ a • F.presheaf.germ U x x.property s = 0),
      (F.presheaf.germ U (genericPoint X)
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
          (by simpa using (inferInstance : Nonempty U))) s = 0),
      ((Scheme.Modules.toSkyscraper
        (LinearMap.id : F.presheaf.stalk (genericPoint X) →ₗ[X.functionField]
          F.presheaf.stalk (genericPoint X))).app U s = 0)] := by
  sorry

end AlgebraicGeometry
