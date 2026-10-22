/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Norm invertible modules and saturated nonvanishing loci

Source: Stacks Project, Divisors, Tags 0BCY (lemma-norm-invertible),
0BCZ (lemma-norm-map-invertible), and Section 0BCX (section-norms)
(blueprint: lem-sfb-finite-norm-invertible-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A multiplicative sheaf norm for a finite surjective morphism produces a single
invertible module whose tensor powers admit norm sections. Their nonvanishing loci
consist exactly of the points whose entire fibre lies in the original nonvanishing locus.
The norm preserves multiplication and one, with no additivity assumption.

Source: Stacks Project, Divisors, Tags 0BCY (lemma-norm-invertible),
0BCZ (lemma-norm-map-invertible), and Section 0BCX (section-norms)
(blueprint: lem-sfb-finite-norm-invertible-sections).

Proof:
1. Apply `lem-sfb-finite-trivialize-invertible-upstairs` (Tag 0BUT) at each point
   of `Z`. Choose an open cover `V_i` and generators `e_i` of `M` on `p⁻¹ V_i`.
   Fix these choices before choosing any tensor power or section.
2. Write `e_i = u_ij e_j` on overlaps. Uniqueness of coefficients gives the unit
   cocycle identities. Put `v_ij = ν(u_ij)`. Multiplicativity and preservation of
   one send inverse units to inverse units; restriction compatibility sends the
   cocycle identities to those for `v_ij` (`def-sc-invertible-module`).
3. Apply `lem-sc-glue-component-transition-cocycle` to obtain an invertible module
   `N` with frames `f_i = v_ij f_j`. This fixed `N` serves every power and section.
4. Fix `n ≥ 1` and `s`. Tensoring the frames gives transitions `u_ij^n` and `v_ij^n`;
   the powers are invertible by `lem-weil-pbc-invertible-pullback-tensor` (1).
   Write `s = b_i e_i^n`. Then `b_j = b_i u_ij^n`, hence
   `ν(b_j) = ν(b_i) v_ij^n`. The sections `ν(b_i) f_i^n` agree on overlaps
   and glue by the sheaf axiom to a global section `t` of `N.tensorPow n`.
5. If `s` vanishes at `y` over `z`, then `b_i(y) = 0`. The residue-field vanishing
   hypothesis gives `ν(b_i)(z) = 0`, hence `t(z) = 0`. Thus the nonvanishing locus
   of `t` lies in the complement of the image of the vanishing locus of `s`
   (`def-weil-pbc-ample-invertible-module`).
6. Conversely, suppose the whole fibre over `z` lies in the nonvanishing locus of `s`.
   This locus is open by `lem-weil-pbc-nonvanishing-section-trivializes`.
   The finite morphism is closed by `lem-weil-pbc-finite-closed-map-finite-fibres` (1).
   Shrink `V_i` to `W = V_i ∖ p(Y ∖ Y_s)` around `z`. On `p⁻¹ W`, the function
   `b_i` is nowhere zero, hence a unit: apply the nonvanishing trivialization lemma
   to the trivial module, and evaluate its inverse at one. Multiplicativity and
   preservation of one make `ν_W(b_i)` a unit. It is nonzero in the residue field
   at `z`; restriction compatibility identifies its value with `ν_V_i(b_i)(z)`.
   Thus `t(z) ≠ 0` in the frame `f_i^n`.
7. These inclusions give the complement-of-image equality. For any set map,
   membership in this complement is equivalent to the entire fibre lying in `Y_s`.
   This gives both displayed equalities, for every `n` and `s`, with the fixed `N`.
-/
theorem exists_invertible_norm_sections
    {Y Z : Scheme.{u}} (p : Y ⟶ Z) [IsFinite p] [Surjective p]
    (d : ℕ) (hd : 1 ≤ d)
    (ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V))
    (hν_restrict : ∀ (V W : Z.Opens) (h : W ≤ V) (b : Γ(Y, p ⁻¹ᵁ V)),
      ν W (Y.presheaf.map (homOfLE (p.preimage_mono h)).op b) =
        Z.presheaf.map (homOfLE h).op (ν V b))
    (hν_power : ∀ (V : Z.Opens) (a : Γ(Z, V)), ν V (p.app V a) = a ^ d)
    (hν_vanish : ∀ (V : Z.Opens) (b : Γ(Y, p ⁻¹ᵁ V)) (y : Y) (hy : y ∈ p ⁻¹ᵁ V),
      Y.evaluation (p ⁻¹ᵁ V) y hy b = 0 →
        Z.evaluation V (p y) hy (ν V b) = 0)
    (M : Y.Modules) [M.IsInvertible] :
    ∃ N : Z.Modules, N.IsInvertible ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (s : Γ(M.tensorPow n, ⊤)),
        ∃ t : Γ(N.tensorPow n, ⊤),
          nonvanishingLocus (N.tensorPow n) t =
              (p '' (nonvanishingLocus (M.tensorPow n) s)ᶜ)ᶜ ∧
            nonvanishingLocus (N.tensorPow n) t =
              {z : Z | p ⁻¹' {z} ⊆ nonvanishingLocus (M.tensorPow n) s} := by
  sorry

end AlgebraicGeometry.Scheme.Modules
