/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FiniteNormInvertibleSections
import Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine
import WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen

/-! # Existence of an ample module from the reduction in characteristic p

Source: Stacks Project, Divisors, Tag 0BD4, proposition-push-down-ample, case (3),
applied to the reduction immersion; Tags 0BDZ and 0BD0
(blueprint: lem-sfb-ample-existence-characteristic-p-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A Noetherian scheme annihilated by a prime admits an absolutely ample invertible
module if its reduction does. The resulting module is not required to lift any specified
module on the reduction.

Source: Stacks Project, Divisors, Tag 0BD4, proposition-push-down-ample, case (3),
with Tags 0BDZ (lemma-Frobenius-gives-norm-for-reduction) and 0BD0 (lemma-norm-ample)
(blueprint: lem-sfb-ample-existence-characteristic-p-reduction).

Proof:
1. Put `Y = X.nilradical.subscheme` and let `i = X.nilradical.subschemeι`.
   This closed immersion is surjective with singleton fibres and is finite by
   `lem-weil-pbc-closed-immersion-finite`. Apply `lem-sfb-reduction-frobenius-sheaf-norm`
   to obtain an exponent `e ≥ 1` and a restriction-compatible sheaf norm of degree
   `d = p^e ≥ 1`, with the scalar-power and residue-field vanishing properties.
2. Choose an ample invertible module `M` on `Y` from the hypothesis. Apply
   `lem-sfb-finite-norm-invertible-sections` to obtain a single invertible module `N`
   on `X`, whose positive powers admit norm sections for all sections of powers of `M`.
3. Fix `x : X` and an affine open neighbourhood `V`. The fibre of `i` over `x` is a
   singleton inside `i⁻¹ V`. By `lem-sc-ample-finite-principal-affine` choose `n > 0`
   and a section `s` of `M.tensorPow n` whose nonvanishing locus contains this fibre
   and lies in `i⁻¹ V`.
4. The norm-section lemma gives a section `t` of `N.tensorPow n` whose nonvanishing
   locus consists of the points whose entire fibre lies in the nonvanishing locus of `s`.
   Thus `x` lies in `X_t`. Surjectivity of `i` and `Y_s ⊆ i⁻¹ V` imply `X_t ⊆ V`.
   Now `X_t = V ∩ X_t` is affine by `lem-sc-affine-cap-section-open`.
5. Ampleness of `M` gives quasi-compactness of `Y`. Pull an open cover of `X` back to
   `Y`, take a finite subcover, and use surjectivity to obtain a finite subcover of `X`.
   Together with step 4, this is exactly `def-weil-pbc-ample-invertible-module` for `N`.
   Only existence is asserted; no identification of its restriction with `M` is needed.
-/
theorem exists_isAmple_of_reduction_charP
    (p : ℕ) (hp : p.Prime) (X : Scheme.{u}) [IsNoetherian X]
    (hchar : ∀ x : X, (p : X.presheaf.stalk x) = 0)
    (hred : ∃ (M : X.nilradical.subscheme.Modules) (_ : M.IsInvertible),
      IsAmple X.nilradical.subscheme M) :
    ∃ (L : X.Modules) (_ : L.IsInvertible), IsAmple X L := by
  sorry

end AlgebraicGeometry.Scheme.Modules
