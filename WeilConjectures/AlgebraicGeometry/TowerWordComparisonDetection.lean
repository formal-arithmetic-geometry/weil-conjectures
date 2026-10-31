/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.TowerP1LevelWords
public import WeilConjectures.AlgebraicGeometry.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Equality detection for shifted rank-one coefficient towers

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, proof (1),
"After removing the shift [2d]"
(blueprint: lem-route-tower-word-comparison-detection).

The ordinary derived category is the published section-preserving system presentation
of strict coefficient towers. The same finite arrow and endpoint comparisons are used
for both maps. Only the specified shifted unit and ordered Tate-line endpoints occur.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

namespace SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E)

/-- The endpoint restriction in the detection lemma, expressed with the existing
normalized unit and ordered Tate-line objects. The ordered line of dimension d already
contains [2d]; the additional shift s - 2d places its degree-zero sheaf in the common
shift s. The unit alternative needs no choice of Tate-twist data.
Source: purity-bc-factors proof (1), remove [2d] before testing levelwise
(blueprint: lem-route-tower-word-comparison-detection). -/
def IsShiftedRankOneTower (T : Scheme.{u}) (s : ℤ) (K : SpTowerShriek.D l E T) : Prop :=
  Nonempty (K ≅ (SpTowerGamma.unit l E T)⟦s⟧) ∨
    ∃ (w : SpChartAdmissibility.Twists l E T) (d : ℕ),
      Nonempty (K ≅ (SpTowerGamma.orderedLine l E b T w d)⟦s - 2 * (d : ℤ)⟧)

/-- Finite WordComparison equations detect equality between the stipulated equally
shifted normalized rank-one sheaf towers. The LevelWords have literally the same tower
endpoints, finite objects, comparison arrows, and finite arrow for the two maps.
Geometric-coordinate words are the published LevelWords passed to this assertion.
Source: purity-bc-factors proof (1), final two sentences
(blueprint: lem-route-tower-word-comparison-detection).

Proof: (1) At every positive level cancel the invertible source comparison in the two
WordComparison equations; their common finite arrow and target comparison give equal
derived evaluations. No faithfulness of nu is needed. (2) Remove the common shift s.
The stipulated unit and ordered Tate-line objects are degree-zero sheaf towers in this
shift. Fullness of DerivedCategory.singleFunctor in the abelian tower category represents
both maps by sheaf-tower maps. (3) Exact evaluation commutes with the single embedding
and shifts. Faithfulness of the finite-level single embedding therefore identifies
every component of these sheaf-tower maps. (4) A strict tower morphism is its component
family, with transition compatibility a property, so the tower maps agree. Faithfulness
of the single embedding, the shift equivalence, and endpoint isomorphisms give r = r'. -/
theorem tower_wordComparison_detection
    (T : Scheme.{u}) (s : ℤ) (K L : SpTowerShriek.D l E T)
    (_hK : IsShiftedRankOneTower l E b T s K)
    (_hL : IsShiftedRankOneTower l E b T s L)
    (A B : ∀ n : ℕ, Etale.DerivedCategoryModule (levelRing l E n) T)
    (cK : ∀ n : ℕ, (nu l E n T).obj (A n) ⟶ (SpTowerShriek.Ev l E T n).obj K)
    (cL : ∀ n : ℕ, (nu l E n T).obj (B n) ⟶ (SpTowerShriek.Ev l E T n).obj L)
    (g : ∀ n : ℕ, A n ⟶ B n) (r r' : K ⟶ L)
    (_hr : ∀ n : ℕ,
      WordComparison l E n ⟨K, A n, cK n⟩ ⟨L, B n, cL n⟩ r (g n))
    (_hr' : ∀ n : ℕ,
      WordComparison l E n ⟨K, A n, cK n⟩ ⟨L, B n, cL n⟩ r' (g n)) :
    r = r' := by sorry

/-- The same detection implication after fixed tower-isomorphism conjugation.
Source: purity-bc-factors proof (1), return to the fixed endpoint identifications
(blueprint: lem-route-tower-word-comparison-detection).

Proof: apply tower_wordComparison_detection to i.hom composed with each map and j.hom,
using the given common-shift rank-one endpoints and finite WordComparison equations.
Its proof cancels the finite comparisons, removes the common shift, uses exact evaluation
and full faithfulness of the single embedding, and identifies the strict component
families. Then cancel i.hom and j.hom using their inverses to recover the original maps. -/
theorem tower_wordComparison_detection_conjugate
    (T : Scheme.{u}) (s : ℤ) (K L : SpTowerShriek.D l E T)
    (_hK : IsShiftedRankOneTower l E b T s K)
    (_hL : IsShiftedRankOneTower l E b T s L)
    (K₀ L₀ : SpTowerShriek.D l E T) (i : K ≅ K₀) (j : L₀ ≅ L)
    (A B : ∀ n : ℕ, Etale.DerivedCategoryModule (levelRing l E n) T)
    (cK : ∀ n : ℕ, (nu l E n T).obj (A n) ⟶ (SpTowerShriek.Ev l E T n).obj K)
    (cL : ∀ n : ℕ, (nu l E n T).obj (B n) ⟶ (SpTowerShriek.Ev l E T n).obj L)
    (g : ∀ n : ℕ, A n ⟶ B n) (r r' : K₀ ⟶ L₀)
    (_hr : ∀ n : ℕ, WordComparison l E n ⟨K, A n, cK n⟩ ⟨L, B n, cL n⟩
      (i.hom ≫ r ≫ j.hom) (g n))
    (_hr' : ∀ n : ℕ, WordComparison l E n ⟨K, A n, cK n⟩ ⟨L, B n, cL n⟩
      (i.hom ≫ r' ≫ j.hom) (g n)) :
    r = r' := by sorry

/-- Detection after transport by the fixed realization counits. The maps being tested
are in the original ordinary derived category of strict coefficient towers; the displayed
finite squares are for their counit-transported maps in the published system coordinates.
Source: purity-bc-factors proof (1), realization transport
(blueprint: lem-route-tower-word-comparison-detection).

Proof: apply tower_wordComparison_detection to the two displayed counit composites.
At each level the natural levelComparison of def-sp-coefficient-tower-shriek-interfaces
identifies exact original-tower evaluation with system evaluation, so these are the same
finite equations in the specified coordinates. Cancellation of their common invertible
LevelWord comparisons, exact evaluation after the common inverse shift, full faithfulness
of the single embedding, and equality of all strict sheaf-tower components give equality
of the transported maps. Cancel the fixed realization counits and use faithfulness of
the realization equivalence to get r = r'. Naturality gives the inverse transport via
the fixed unit as well. No new realization or counit is selected. -/
theorem tower_wordComparison_detection_realization
    (q : SpTowerCalculus.Coordinates l E b)
    (T : Scheme.{u}) (s : ℤ) (K L : SpTowerShriek.D l E T)
    (_hK : IsShiftedRankOneTower l E b T s K)
    (_hL : IsShiftedRankOneTower l E b T s L)
    (A B : ∀ n : ℕ, Etale.DerivedCategoryModule (levelRing l E n) T)
    (cK : ∀ n : ℕ, (nu l E n T).obj (A n) ⟶ (SpTowerShriek.Ev l E T n).obj K)
    (cL : ∀ n : ℕ, (nu l E n T).obj (B n) ⟶ (SpTowerShriek.Ev l E T n).obj L)
    (g : ∀ n : ℕ, A n ⟶ B n)
    (r r' : (SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj K ⟶
      (SpTowerCalculus.realization l E b T (q.abelian T)).inverse.obj L)
    (_hr : ∀ n : ℕ, WordComparison l E n ⟨K, A n, cK n⟩ ⟨L, B n, cL n⟩
      ((SpTowerCalculus.realization l E b T (q.abelian T)).counitIso.inv.app K ≫
        (SpTowerCalculus.realization l E b T (q.abelian T)).functor.map r ≫
        (SpTowerCalculus.realization l E b T (q.abelian T)).counitIso.hom.app L) (g n))
    (_hr' : ∀ n : ℕ, WordComparison l E n ⟨K, A n, cK n⟩ ⟨L, B n, cL n⟩
      ((SpTowerCalculus.realization l E b T (q.abelian T)).counitIso.inv.app K ≫
        (SpTowerCalculus.realization l E b T (q.abelian T)).functor.map r' ≫
        (SpTowerCalculus.realization l E b T (q.abelian T)).counitIso.hom.app L) (g n)) :
    r = r' := by sorry

end SpTowerP1

end AlgebraicGeometry.ProEtale
