/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.AlgebraicGeometry.FormalBlowupCongruenceData
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import WeilConjectures.Blowup.Affine.StrictTransformChart
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.AlgebraicGeometry.FormalAffinePrincipalRefinement

/-! # Bounded precision loss for supported formal blowups

Source: Temkin, Non-embedded Desingularization, Lemma 3.3.3, printed p.23:
the chart calculation, its two-map version, finite iteration and flat pullback
(blueprint: lem-per-supported-blowup-precision-loss).

The affine blowup systems below are completions of the ordinary blowup, whose
ordinary charts are `AffineBlowup.chartRing H s`, i.e. A[H/s]. Their structure
sheaves are inverse limits of the quotient sheaves. General formal schemes use
the existing infinitesimal-system interface, so equality at finite precision is
actual equality of scheme morphisms, including their maps of structure sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AdicFormal

/-- Supported blowups lose at most the exponent of their center, and finite towers
lose at most the sum of these exponents, with unchanged bounds under flat pullback.

Source: Temkin, Lemma 3.3.3, printed p.23, generalized to two maps and finite towers
(blueprint: lem-per-supported-blowup-precision-loss).

The induced maps on blowups are characterized as the unique lifts over the base maps
(the universal property of the blowup), and it is these lifts that are congruent.

Proof plan (the seven steps of the DAG node):
1. For generators s_i of H, localization restricts to the ordinary chart maps
   A[H/s_i] -> B[L/w(s_i)] for w=u,v (strictChartMap). Extend them to completions
   using compatible quotient maps and glue on the overlaps. Use
   lem-per-formal-open-blowup-base-change for the completed chart cover, and
   lem-weil-pbc-localization-away-universal-property for uniqueness on overlaps.
2. Put k=m-e, t=u(s), t'=v(s) and t'-t=rho^m b. On the completed t chart,
   q=rho^e/t belongs to the ring, and t'/t=1+rho^k bq is a unit by
   lem-weil-pbc-adic-complete-jacobson-radical. The ordinary overlap localizes at
   this ratio. By lem-per-formal-affine-principal-refinement its completion is
   the whole t chart. Interchanging the two maps identifies their formal opens.
3. Subtract the fractions: u(a)/u(s)-v(a)/v(s) equals
   rho^k (rho^e/u(s)) (c_a-c_s v(a)/v(s)). This is in rho^k times the common
   chart ring. Coefficients agree as well. The chart generators generate the
   ordinary chart; lem-weil-pbc-adic-completion-mod-power extends agreement to
   its completion. No cancellation of a chart denominator is used.
4. The equalities on the common chart cover glue to equal reduced morphisms.
   For an automorphism take v=id. If e=0 the blowup is the identity; otherwise
   u(pi)=pi times a unit because m>=2. This gives the automorphism assertion.
5. Restrict to common formal affine neighbourhoods. Principal refinements use
   the completed-localization restriction maps of
   lem-per-formal-affine-principal-refinement. Blowup commutes with formal open
   restriction by lem-per-formal-open-blowup-base-change, so the local equalities glue.
6. Induct on the finite tower, keeping precision m minus the partial sum of the
   exponents. The center identities let the one-step assertion apply at each
   stage. Unit centers have exponent zero and identity blowups. The zero-length
   tower retains m; at exponent zero Congruent is vacuous, the empty reduction.
7. Flat formal pullback preserves the completed blowup chart models by
   lem-per-formal-open-blowup-base-change. The center inclusions and each displayed
   fraction identity extend with exactly the same exponents. Thus the induction
   and its congruences have the same bounds after flat pullback. This uses
   completed formal fibre products, never an uncompleted tensor product.
-/
theorem supportedBlowup_precision_loss :
    (∀ (A B : CommRingCat.{u}) [IsNoetherianRing A] [IsNoetherianRing B]
      (π : A) (ρ : B)
      [IsAdicComplete (Ideal.span {π}) A] [IsAdicComplete (Ideal.span {ρ}) B]
      (H : Ideal A) (L : Ideal B) (e m : ℕ) (u v : A →+* B),
      π ∈ nonZeroDivisors A → ρ ∈ nonZeroDivisors B →
      H.FG → L.FG → π ^ e ∈ H → ρ ^ e ∈ L → e < m →
      @Continuous _ _ (Ideal.span {π}).adicTopology (Ideal.span {ρ}).adicTopology u →
      @Continuous _ _ (Ideal.span {π}).adicTopology (Ideal.span {ρ}).adicTopology v →
      (Ideal.span {π}).map u = Ideal.span {ρ} →
      (Ideal.span {π}).map v = Ideal.span {ρ} → H.map u = L → H.map v = L →
      (∀ a : A, u a - v a ∈ Ideal.span {ρ} ^ m) →
      ∃ (f g : completion (affineIdeal B (Ideal.span {ρ})) ⟶
          completion (affineIdeal A (Ideal.span {π})))
        (bA : affineBlowupSystem A (Ideal.span {π}) H ⟶
          completion (affineIdeal A (Ideal.span {π})))
        (bB : affineBlowupSystem B (Ideal.span {ρ}) L ⟶
          completion (affineIdeal B (Ideal.span {ρ})))
        (f' g' : affineBlowupSystem B (Ideal.span {ρ}) L ⟶
          affineBlowupSystem A (Ideal.span {π}) H),
        InducesRingHom (Ideal.span {π}) (Ideal.span {ρ}) u f ∧
        InducesRingHom (Ideal.span {π}) (Ideal.span {ρ}) v g ∧
        IsAffineBlowupProjection A (Ideal.span {π}) H bA ∧
        IsAffineBlowupProjection B (Ideal.span {ρ}) L bB ∧
        (∀ x : affineBlowupSystem B (Ideal.span {ρ}) L ⟶
            affineBlowupSystem A (Ideal.span {π}) H, x ≫ bA = bB ≫ f ↔ x = f') ∧
        (∀ x : affineBlowupSystem B (Ideal.span {ρ}) L ⟶
            affineBlowupSystem A (Ideal.span {π}) H, x ≫ bA = bB ≫ g ↔ x = g') ∧
        Congruent f' g' (m - e)) ∧
    (∀ (F G F' G' : ℕ ⥤ Scheme.{u})
      (b : F' ⟶ F) (c : G' ⟶ G)
      (J : ∀ n : ℕ, (F.obj n).IdealSheafData)
      (K : ∀ n : ℕ, (G.obj n).IdealSheafData)
      (f g : G ⟶ F) (e m : ℕ),
      IsBlowup b J → IsBlowup c K →
      HasPrincipalRegularCharts F → HasPrincipalRegularCharts G →
      HasCenterExponent F J e → HasCenterExponent G K e →
      IsAdicMap f → IsAdicMap g →
      (∀ n : ℕ, (J n).comap (f.app n) = K n) →
      (∀ n : ℕ, (J n).comap (g.app n) = K n) →
      e < m → Congruent f g m →
      ∃ p : (G' ⟶ F') × (G' ⟶ F'),
        (∀ q : (G' ⟶ F') × (G' ⟶ F'),
          (q.1 ≫ b = c ≫ f ∧ q.2 ≫ b = c ≫ g ∧ IsAdicMap q.1 ∧ IsAdicMap q.2) ↔
            q = p) ∧
        Congruent p.1 p.2 (m - e)) ∧
    (∀ (F F' : ℕ ⥤ Scheme.{u}) (b : F' ⟶ F)
      (J : ∀ n : ℕ, (F.obj n).IdealSheafData) (a : F ≅ F) (e m : ℕ),
      IsBlowup b J → HasPrincipalRegularCharts F → HasCenterExponent F J e →
      (∀ n : ℕ, (J n).comap (a.hom.app n) = J n) →
      e < m → Congruent a.hom (𝟙 F) m →
      ∃ a' : F' ≅ F', (∀ a'' : F' ≅ F', a''.hom ≫ b = b ≫ a.hom ↔ a'' = a') ∧
        Congruent a'.hom (𝟙 F') (m - e)) ∧
    (∀ (r : ℕ) (S T : PrecisionTower.{u} r)
      (f g : PrecisionTowerMap S T) (m : ℕ),
      S.exponent = T.exponent →
      Congruent (f.map 0) (g.map 0) m →
      Congruent (f.map (Fin.last r)) (g.map (Fin.last r))
        (m - ∑ i : Fin r, T.exponent i)) ∧
    (∀ (r : ℕ) (S T S' T' : PrecisionTower.{u} r)
      (f g : PrecisionTowerMap S T) (f' g' : PrecisionTowerMap S' T')
      (hS : PrecisionTowerMap S' S) (hT : PrecisionTowerMap T' T) (m : ℕ),
      hS.IsFlatPullback → hT.IsFlatPullback →
      S.exponent = T.exponent → S'.exponent = S.exponent → T'.exponent = T.exponent →
      (∀ i : Fin (r + 1), f'.map i ≫ hT.map i = hS.map i ≫ f.map i) →
      (∀ i : Fin (r + 1), g'.map i ≫ hT.map i = hS.map i ≫ g.map i) →
      (∀ (Z Z' : ℕ ⥤ Scheme.{u}) (h : Z' ⟶ Z)
        (s : ∀ i : Fin (r + 1), S.level i ⟶ Z)
        (t : ∀ i : Fin (r + 1), T.level i ⟶ Z)
        (s' : ∀ i : Fin (r + 1), S'.level i ⟶ Z')
        (t' : ∀ i : Fin (r + 1), T'.level i ⟶ Z'),
        IsAdicMap h → (∀ n : ℕ, Flat (h.app n)) →
        (∀ i : Fin (r + 1), f.map i ≫ t i = s i ∧ g.map i ≫ t i = s i) →
        (∀ (i : Fin (r + 1)) (n : ℕ),
          IsPullback ((hS.map i).app n) ((s' i).app n) ((s i).app n) (h.app n)) →
        (∀ (i : Fin (r + 1)) (n : ℕ),
          IsPullback ((hT.map i).app n) ((t' i).app n) ((t i).app n) (h.app n)) →
        (∀ i : Fin (r + 1), f'.map i ≫ t' i = s' i ∧ g'.map i ≫ t' i = s' i) →
      Congruent (f.map 0) (g.map 0) m →
      Congruent (f'.map (Fin.last r)) (g'.map (Fin.last r))
        (m - ∑ i : Fin r, T.exponent i))) := by
  sorry

end AlgebraicGeometry.AdicFormal
