/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.FiniteDegree.Algebra
import WeilConjectures.Blowup.Proper
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth-center blowups and reduced strict transforms

Source: literature/stacks-project/more-morphisms.tex, Tag 0FUT, lemma-blowup;
Tag 02NS, divisors.tex lemma-blowing-up-projective; Tag 056B, morphisms.tex
lemma-scheme-theoretic-image-reduced (blueprint: lem-trf-smooth-center-blowup-geometry).
-/

@[expose] public section


open CategoryTheory

namespace AlgebraicGeometry

/-- Smooth-center blowups preserve smoothness, separatedness, and finite type, and preserve
reducedness of scheme-theoretic strict transforms. The empty center is allowed, and no
containment or stratum hypothesis is imposed. Source: more-morphisms.tex Tag 0FUT,
lemma-blowup; divisors.tex Tag 02NS; morphisms.tex Tag 056B.

Proof (the node's steps). Write `k = ℚ`, `I = c.ker` and `b_P : P⁺ = Bl_C P ⟶ P`.
1. By lem-pur-smooth-pair-local-coordinates (Tag 0FUE) every point of `C` has an open
   `V ⊆ P` and an étale `h : V ⟶ 𝔸^{a+b}_k` with `C ∩ V = h⁻¹(y₁ = ⋯ = y_b = 0)`; so `I`
   is of finite type and `C ⟶ P` is of finite presentation
   (def-sbc-closed-immersion-ideal-sheaf, def-weil-closed-immersion).
2. Flat base change of blowups (thm-nagata-blowup-flat-base-change with
   def-nagata-blowup-flat-base-change-map) along `V ⊆ P` and along `h` gives
   `b_P⁻¹(V) ≅ Bl_{C∩V} V ≅ V ×_{𝔸^{a+b}} Bl_J(Spec A)`, `A = k[x, y]`, `J = (y₁, …, y_b)`.
3. If `b > 0`, the charts `A[J/y_i]` (prop-nagata-affine-blowup-chart-cover,
   def-nagata-blowup-chart-ring) are polynomial rings `k[x, y_i, t_j (j ≠ i)]` via
   `t_j ↦ y_j / y_i` (surjective as `y_j = y_i t_j`, injective by Laurent exponents); if
   `b = 0` the only chart is `A[0/0] = 0` and the blowup is empty.
4. Affine space is smooth (sbc-lem-affine-space-smooth, transported along isomorphisms by
   lem-weil-pbc-smooth-restrict-open-subschemes (c)); the étale base change of a chart is
   étale (lem-weil-pbc-etale-scheme-base-change), hence smooth
   (lem-weil-pbc-etale-smooth-zero-dimensional-fibres), and composites of smooth maps are
   smooth (lem-trf-smooth-composition); by lem-weil-pbc-smooth-local-on-source
   `b_P⁻¹(V)` is smooth over `k` (also when it is empty).
5. Over `P ∖ C` the blowup is `P ∖ C` (thm-nagata-global-blowup-complement), smooth by
   lem-weil-pbc-smooth-restrict-open-subschemes; these opens and the `b_P⁻¹(V)` cover
   `P⁺`, so `P⁺` is smooth over `k` by lem-weil-pbc-smooth-local-on-source (`C = ∅`
   included).
6. `I` is quasi-coherent of finite type, so `b_P` is proper (lemma-nagata-blowup-proper),
   hence separated and of finite type (def-weil-proper-morphism); composing with
   `P ⟶ Spec k` gives finite type (lem-sfb-finite-type-composition-base-change (1)).
7. The diagonal of `P⁺` over `k` factors as `P⁺ ⟶ P⁺ ×_P P⁺ ⟶ P⁺ ×_k P⁺`: the first map
   is a closed immersion since `b_P` is separated, the second is a base change of the
   closed diagonal of `P` (lem-weil-pbc-closed-immersion-base-change), and closed
   immersions compose (def-weil-closed-immersion); so `P⁺` is separated over `k`.
8. With `U = P ∖ C`, the open `T = (X ×_P U) ×_U (P⁺ ×_P U)` of `X ×_P P⁺` is isomorphic
   to the reduced open `X_U` (def-pc-reduced-scheme, thm-nagata-global-blowup-complement).
   The strict transform is its scheme-theoretic closure (def-nagata-strict-transform),
   which is reduced by lem-trf-reduced-scheme-image (Tag 056B); the projection
   `X ×_P P⁺ ⟶ P⁺` is a closed immersion (lem-weil-pbc-closed-immersion-base-change), so
   this is also the strict transform in `P⁺`. `T = ∅` (e.g. `X ⊆ C`) is allowed.
(blueprint: lem-trf-smooth-center-blowup-geometry) -/
theorem smooth_center_blowup_geometry
    {P C X : Scheme.{0}} (p : P ⟶ Spec (CommRingCat.of ℚ))
    (c : C ⟶ P) (x : X ⟶ P)
    [Smooth p] [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [Smooth (c ≫ p)] [IsClosedImmersion c]
    [IsReduced X] [IsClosedImmersion x] :
    Smooth (c.ker.blowupMap ≫ p) ∧
      IsSeparated (c.ker.blowupMap ≫ p) ∧
      LocallyOfFiniteType (c.ker.blowupMap ≫ p) ∧
      QuasiCompact (c.ker.blowupMap ≫ p) ∧
      IsReduced (c.ker.strictTransform x) := by
  sorry

end AlgebraicGeometry
