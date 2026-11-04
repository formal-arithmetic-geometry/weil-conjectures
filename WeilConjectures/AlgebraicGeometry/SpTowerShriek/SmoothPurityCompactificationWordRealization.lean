/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCoordinatesExistence
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictPlusComparisonsRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictPlusEvaluationRealization

/-! # Construction and evaluation of compactification adjunction words

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-tower-geometric/sk-lem-sp-tower-bound/
sk-lem-sp-tower-bound-operations.proof.md, (1) and (2).
(blueprint: lem-sp-strict-compactification-comparison-realization).

All operations use the existing ordinary derived categories of actual coefficient
systems. Index n denotes positive level n+1. The statement retains the construction
and evaluation assertions, with bounded-below injective-resolution compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Naturality and evaluation of the two complete compactification words.
Source: blueprint operations proof (2)
(blueprint: def-sp-strict-compactification-comparison-interfaces). -/
def StrictWordComparisons (b : Base l E) (o : Operations l E b)
    (x : OpenExchange l E b o) (levels : ComparisonLevels l E b o) : Prop :=
  (∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    {K K' : D l E X} {L L' : D l E Y} (a : K ⟶ K') (d : L ⟶ L'),
    (tensor l E b Y).map (Prod.mkHom ((F l E b o c).map a) d) ≫
        projection l E b o c K' L' =
      projection l E b o c K L ≫
        (F l E b o c).map ((tensor l E b X).map
          (Prod.mkHom a ((pull l E b (o.geometry f)).map d)))) ∧
  (∀ {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) (n : ℕ)
    (K : D l E X) (L : D l E Y),
    (Ev l E Y n).map (projection l E b o c K L) ≫
        (Fcomparison l E b o c n).hom.app
          ((tensor l E b X).obj (K, (pull l E b (o.geometry f)).obj L)) ≫
        (finiteF l E b c n).map
          (((b.calculus X).tensorEvaluation n).hom.app
            (K, (pull l E b (o.geometry f)).obj L) ≫
            (comparisonLevelTensor l E b X n).map
              (Prod.mkHom (𝟙 _) (((o.geometry f).pullEvaluation n).hom.app L))) =
      ((b.calculus Y).tensorEvaluation n).hom.app ((F l E b o c).obj K, L) ≫
        (comparisonLevelTensor l E b Y n).map
          (Prod.mkHom ((Fcomparison l E b o c n).hom.app K) (𝟙 _)) ≫
        comparisonLevelProjection l E b o levels c n ((Ev l E X n).obj K)
          ((Ev l E Y n).obj L)) ∧
  (∀ {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (sq : IsPullback h f' f g) (c : Compactification f)
    (n : ℕ) (K : D l E X),
    (Ev l E Y' n).map ((exchange l E b o x sq c).app K) ≫
        (Fcomparison l E b o (c.ofIsPullback sq) n).hom.app
          ((pull l E b (o.geometry h)).obj K) ≫
        (finiteF l E b (c.ofIsPullback sq) n).map
          (((o.geometry h).pullEvaluation n).hom.app K) =
      ((o.geometry g).pullEvaluation n).hom.app ((F l E b o c).obj K) ≫
        (proEtaleConstantRingDerivedPullback (R l E n) g).map
          ((Fcomparison l E b o c n).hom.app K) ≫
        (comparisonLevelExchange l E b o levels sq c n).app ((Ev l E X n).obj K))

/-- Simultaneous realization of the compactification projection and exchange words
on actual quotient towers, with their finite evaluations and canonical D+ comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-prop-sp-tower-geometric/sk-lem-sp-tower-bound/
sk-lem-sp-tower-bound-operations.proof.md, (1) and (2).
(blueprint: lem-sp-strict-compactification-comparison-realization).

The section-normalized Base presents the actual tower category, preserving its
sections, restrictions and maps. Its calculus supplies exact derived evaluations and
tensor evaluation. Operations supplies geometric adjunctions, their evaluated units
and counits, exact open extension and evaluated pullback compositors. OpenExchange
and ComparisonLevels fix the inverse open maps by their open-unit transposes.
StrictWordComparisons states naturality of the actual projection and equality of the
two evaluated composites with the finite proper/open words. StrictPlusComparisons
and StrictPlusEvaluation pin the bounded-below comparison to right derivation by
injective resolutions. Tensor inputs range over all objects, including any specified
twist tower; no normalization condition is imposed on those inputs.

Proof:
1. Apply lem-sp-strict-coordinates-existence to choose Base and Operations whose
   selected system calculus extends, on every scheme, to the section-normalized
   SemilinearDerivedSectionsData. Interpret index n as the paper's positive n+1.
2. Apply lem-sp-strict-open-word-evaluation with this extension. It supplies the
   normalized open comparisons and finite ComparisonLevels. Form F = G_p J_j.
   The projection is the transpose of the proper counit tensored with the identity,
   followed by G_p of open tensor and the pullback compositor. Exchange is the
   proper unit--square--counit mate followed by G_p' of the open comparison.
   Evaluating these factors gives the identical finite composites, with their
   units, counits and open inverse normalizations; naturality follows factorwise.
3. The tower category is Grothendieck abelian, hence has enough injectives, as do
   the finite module categories. Resolve a bounded-below input by a bounded-below
   injective tower complex. It is K-injective; its components are direct-image
   acyclic by det-sp-tower-injective-components. Thus both right derivations and
   their evaluation comparison are computed by that same resolution. Uniqueness
   of right derivation gives StrictPlusComparisons and StrictPlusEvaluation.
   Exact termwise open extension preserves bounded-below inputs, so this also
   applies to F. These comparisons retain the ordinary adjunction normalization.
4. The tensor and word assertions already quantify over arbitrary derived inputs.
   Substitute any specified coefficient-twist tower, retaining its actual quotient
   transitions. This needs no additional origin witness or flat quotient map.
-/
theorem compactificationWordRealization :
    ∃ b : Base l E, ∃ o : Operations l E b, ∃ x : OpenExchange l E b o,
      ∃ levels : ComparisonLevels l E b o,
      ∃ h : ∀ T : Scheme.{u}, EnoughInjectives (S l E T),
      ∃ hlevels : ∀ (T : Scheme.{u}) (n : ℕ),
        EnoughInjectives (proEtaleRingModules T (proEtaleConstantRing T (R l E n))),
      (∀ T : Scheme.{u},
        ∃ s : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u + 1}
          (Scheme.ProEt.topology T) (B l E T) (tau l E T),
          s.systems = b.calculus T) ∧
      @StrictPlusComparisons l _ E _ _ _ b o h ∧
      @StrictPlusEvaluation l _ E _ _ _ b o h hlevels ∧
      StrictWordComparisons l E b o x levels := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerShriek
