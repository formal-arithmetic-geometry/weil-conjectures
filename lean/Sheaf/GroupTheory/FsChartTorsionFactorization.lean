/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.GroupTheory.Torsion
import Sheaf.GroupTheory.FineMonoidFiniteSaturation

/-!
# Separating the torsion in an fs chart

Source: Illusie--Laszlo--Orgogozo, Exposé VIII 3.1.17, printed p. 101, and
Exposé VI 2.1, printed p. 71; the ambient-group factorization is the elementary
argument recorded in the DAG (blueprint: lem-per-fs-chart-torsion-factorization).

The additive monoids use the existing fs predicate via the multiplicative type tag.
The existential submonoid and subgroup are fixed by their membership formulas.
The equivalences are normalized by the ambient inclusions, so they are canonical.
-/

set_option autoImplicit false

universe u v

open Algebra

namespace AlgebraicGeometry

/-- An injective fs chart factors through the root closure of its image. The first
factor is Kummer with cokernel the finite torsion subgroup of the original cokernel;
the second has torsion-free group cokernel. No sharpness or torsion-free completion
hypothesis is imposed.

Source: ILO VIII 3.1.17, printed p. 101 (root saturation), and VI 2.1, printed p. 71
(Kummer); the ambient-group argument is supplied in the DAG
(blueprint: lem-per-fs-chart-torsion-factorization).

Proof:
1. Put `G = Q^gp` and `A = h^gp(P^gp)`. Integrality in
   `def-trf-fs-log-blowup` embeds the monoids in their completions. Injectivity
   identifies `P^gp` with `A = P - P`. The root set `H` is a subgroup: witnesses
   `n*x ∈ A` and `m*y ∈ A` give `n*m*(x-y) ∈ A`.
2. The quotient map `G → G/A` takes `g` to a torsion class exactly when `g ∈ H`.
   Its restriction therefore identifies `H/A` canonically with `C_tor`. If a
   positive multiple of a class in `G/H` is zero, a further positive multiple of
   its representative belongs to `A`, so the class itself is zero.
3. The root set `R` contains the image of `P`, contains zero, and is closed under
   addition by multiplying positive witnesses. It is integral as a submonoid
   of `G`. If `k*g ∈ R`, saturation of `Q` first puts `g` in `Q`; a further
   positive multiple then lies in `P`, so `g ∈ R`. Thus `R` is root closed in `G`.
4. Clearly `R-R ⊆ H`. For `g ∈ H`, write `n*g = p₁-p₂`, with `n > 0`.
   Then `n*(g+p₂) = p₁+(n-1)*p₂ ∈ P`. Saturation of `Q` puts `g+p₂` in `R`,
   so `g = (g+p₂)-p₂ ∈ R-R`. Consequently `R^gp` identifies with `H`.
   The induced group map is injective because equality of two differences in
   `G` is the same cross-sum equality in the integral submonoid `R`.
5. The finite group `H/A` has representatives in `R`, by the preceding shift
   by `p₂`. Adjoin finitely many such representatives to the finite generators
   of `P`, obtaining a finitely generated integral monoid `M ⊆ R` with `M^gp = H`.
6. Apply `lem-trf-fine-monoid-finite-saturation` to `M`, allowing torsion in `H`.
   Its root saturation is `R`: one inclusion uses the positive multiple in `P`,
   the other uses root closure from step 3. Thus `R` is fine saturated.
7. Restrict `h` to `a : P → R`; let `b` be inclusion. Their group maps identify
   with the restriction of `h^gp` to `H` and the inclusion `H → G`, hence are
   injective. The cokernels are `H/A` and `G/H`. Every element of `R` has a
   positive multiple in `a(P)`, exactly the Kummer condition of ILO VI 2.1.
8. Let `N = #C_tor`. It is positive, since the finite group contains zero.
   Translation by `c` permutes this finite group. Summing all its elements
   before and after translation and cancelling gives `N*c = 0`. The canonical
   identifications transfer cardinality and annihilation to `coker(a^gp)`.
   For the trivial torsion subgroup this gives `N = 1`. -/
theorem fs_chart_torsion_factorization
    (P : Type u) (Q : Type v) [AddCommMonoid P] [AddCommMonoid Q]
    (hP : IsFineSaturatedMonoid (Multiplicative P))
    (hQ : IsFineSaturatedMonoid (Multiplicative Q)) (h : P →+ Q)
    (hinj : Function.Injective
      (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)))
    (hfinite : Finite (AddCommGroup.torsion
      (GrothendieckAddGroup Q ⧸
        (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range))) :
    ∃ R : AddSubmonoid Q,
      (∀ q : Q, q ∈ R ↔ ∃ n : ℕ, 0 < n ∧ n • q ∈ Set.range h) ∧
      IsFineSaturatedMonoid (Multiplicative R) ∧
      ∃ H : AddSubgroup (GrothendieckAddGroup Q),
        (∀ g : GrothendieckAddGroup Q,
          g ∈ H ↔ ∃ n : ℕ, 0 < n ∧
            n • g ∈ (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range) ∧
        (∃ e : GrothendieckAddGroup R ≃+ H,
          ∀ r : R, (e (GrothendieckAddGroup.of r)).1 = GrothendieckAddGroup.of r.1) ∧
        ∃ a : P →+ R,
          R.subtype.comp a = h ∧
          Function.Injective a ∧
          Function.Injective
            (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp a)) ∧
          Function.Injective
            (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp R.subtype)) ∧
          (∃ e : (H ⧸
              ((GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range.comap
                H.subtype)) ≃+
              AddCommGroup.torsion (GrothendieckAddGroup Q ⧸
                (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range),
            ∀ g : H, (e (QuotientAddGroup.mk g)).1 =
              (QuotientAddGroup.mk g.1 : GrothendieckAddGroup Q ⧸
                (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range)) ∧
          IsAddTorsionFree (GrothendieckAddGroup Q ⧸ H) ∧
          (∀ r : R, ∃ n : ℕ, 0 < n ∧ n • r ∈ Set.range a) ∧
          Nat.card (GrothendieckAddGroup R ⧸
            (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp a)).range) =
            Nat.card (AddCommGroup.torsion (GrothendieckAddGroup Q ⧸
              (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range)) ∧
          0 < Nat.card (AddCommGroup.torsion (GrothendieckAddGroup Q ⧸
            (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range)) ∧
          (∀ c : GrothendieckAddGroup R ⧸
              (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp a)).range,
            Nat.card (AddCommGroup.torsion (GrothendieckAddGroup Q ⧸
              (GrothendieckAddGroup.lift (GrothendieckAddGroup.of.comp h)).range)) • c = 0) := by
  sorry

end AlgebraicGeometry
