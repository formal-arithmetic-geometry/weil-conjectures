/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerGeometryLimits
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerCompactificationCoherence
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerImageReconstruction
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerProjectionMates
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralTowerPullTensorConstructible

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- All three clauses of the integral tower description, with canonical strict tower
comparisons, completed-coefficient inverse limit, natural compactification comparisons,
and the actual proper and open projection mates.

Source: blueprint main-20261015,
sec-smooth-purity/sk-prop-sp-integral-adjunction/direct-image, clauses (1)--(3);
Stacks 09BP (blueprint: det-sp-integral-direct-image-tower).

Proof, following the eight DAG steps:
1. Use the completed-condensed coefficient comparison and cofinal ell/uniformizer
powers. The standing schemes are Noetherian. The integral-model criterion gives
finite Tor amplitude and derived completeness of M. Reduction-tower-normalized
makes red_X M a normalized constructible strict derived tower with the same Tor bounds.
2. First construct the scalar/pullback map on local generators: 1 tensor f*(x)
goes to f*(1 tensor x), using the specified geometric units. Assemble the ordinary
strict map since these formulas commute with every quotient transition. Localize
on flat-term K-flat representatives, using the recorded reduction counit and exact
pullback comparison; this gives ReductionGeometry with its representative equation.
The exact slice tensor identity makes openReductionInverse invertible. Transpose
the integral proper counit and open unit through the recorded strict adjunctions;
their composite is towerBaseChange. Its evaluations use the actual Fcomparison.
Tower-shriek-levels evaluates its compact-support image as the finite Rf_! values.
Tower-bound-uniform gives common Tor interval [a,b+2d] and constructibility. The
reduction transitions are the finite coefficient direct-image comparison followed
by Rf_! of the input reduction maps; reduction-direct-image makes both invertible.
The semilinear-derived-sections model fixes these as actual tower maps and cocycles.
3. Completion identifies M with Rlim red_X M. The compactification open is
quasi-compact by the Nagata open-immersion criterion. Open-closed-extension-zero-limits
and ringed-tower-pushforward-limit-comparison commute its two separate derived
factors with the strict inverse limit, preserving projections. Derived pushforward
composition identifies every finite term after restriction of scalars to R_Y.
4. Tower reconstruction gives bounded integral constructibility of that limit.
The adjunction/counit clauses of normalized-equivalence identify its reduction
with the original normalized strict tower. Evaluating yields all finite reductions.
The normalized derived adjunction above identifies reconstruction with the completion
unit followed by the limit of the same constructed strict tower comparison.
5. Compactification-coherence-cocycle applies on the ambient localizing closure:
O_E is admissible, Dbc equals Dctf by integral-models, and the localizing closure
contains Dctf. Restrict its natural comparisons to Dbc. Their common-dense-refinement
normalization, identity and cocycle persist in this full subcategory.
6. Integral-tensor-pullback preserves Dbc without completion. The canonical
ringed-topoi-derived-tensor-pullback comparison, computed on K-flat representatives,
commutes with the actual quotient maps, giving the stated pullback reductions.
7. Integral-tensor-product closes Dbc under ordinary relative derived tensor.
On flat-term K-flat Q,Q', the map (q tensor a) tensor (q' tensor b) maps to
(q tensor q') tensor ab, with inverse inserting 1. K-flat change of rings and
site-derived-tensor-descent give a comparison of strict reduction towers.
8. Apply tower-compact-support-projection-formula to red_X M and red_Y K over the
arbitrary standing field. Its proper counit and open unit mates are invertible.
Steps 2--7 identify their limits with the actual integral mates displayed here.
Integral completeness detects their invertibility; both projection endpoints lie
in Dbc. The inverse of the open mate composed with the proper mate gives the
projection isomorphism, or its inverse in the direction displayed in the source.
-/
theorem integral_direct_image_tower (s : Presentation l E) :
    ∃ (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q),
    ∃ L : ∀ T : Scheme.{u}, Limit l E s T,
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    (∃ φ : ∀ c₁ c₂ : Compactification f,
        (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₁ ≅
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₂,
      (∀ c : Compactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) ∧
      ∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (r : Compactification.DenseBoundaryCompactification f)
        (h₁ : r.obj ⟶ c₁) (h₂ : r.obj ⟶ c₂) (M : Constructible l E X),
        (φ c₁.obj.obj c₂.obj.obj).hom.app M ≫
          CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₂ M.obj =
        CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₁ M.obj) ∧
    ∀ c : Compactification f,
      ∃ _v : CanonicalTowerComparison l E s q hq c,
      (∀ M : Constructible l E X,
        spNormalizedConstructibleTorTowers l E Y (s.towers Y)
          (imageTower l E s c M.obj) ∧
        (∀ a b : ℤ, a ≤ b →
          DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
            (imageLevel l E s c M.obj n) a (b + 2 * d)) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj M.obj) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((lim l E s Y (L Y)).obj
            (imageTower l E s c M.obj)) ∧
        IsIso (reconstruction l E s c (L Y) q hq M) ∧
        ∀ n : ℕ, IsIso (finiteBaseChange l E s q hq c M.obj n)) ∧
      (∀ K : Constructible l E Y,
        constantModelBoundedConstructible (spIntegralCondensed l E) X
          ((pull l E f).obj K.obj)) ∧
      ∀ (M : Constructible l E X) (K : Constructible l E Y),
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj
            (((tensor l E X).obj M.obj).obj ((pull l E f).obj K.obj))) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          (((tensor l E Y).obj ((shriek l E c).obj M.obj)).obj K.obj) ∧
        IsIso (properProjection l E c M.obj K.obj) ∧
        IsIso (compactOpenProjection l E c M.obj K.obj) := by
  obtain ⟨q, hq, ⟨L⟩⟩ := normalized_geometry_limits l E s
  refine ⟨q, hq, L, ?_⟩
  intro k _ _ _ X Y _ _ _ _ _ _ _ _ f _ d _
  refine ⟨constructible_compactification_coherence l E k X Y f d, ?_⟩
  intro c
  obtain ⟨⟨v⟩, himage⟩ := image_reconstruction l E s q hq L k X Y f d c
  obtain ⟨hpull, htensor⟩ := integral_pull_tensor_constructible l E k X Y f
  refine ⟨v, ?_, hpull, ?_⟩
  · intro M
    obtain ⟨hnorm, hbound, hshriek, hlimit, hrecon⟩ := himage M
    refine ⟨hnorm, hbound, hshriek, hlimit, hrecon, ?_⟩
    intro n
    have hbase : IsIso (towerBaseChange l E s q hq c M.obj) := by
      rw [← v.hom_eq M]
      infer_instance
    unfold finiteBaseChange
    infer_instance
  · intro M K
    have hinput := htensor X M.obj ((pull l E f).obj K.obj) M.property (hpull K)
    have houtput := (himage M).2.2.1
    exact ⟨(himage ⟨_, hinput⟩).2.2.1,
      htensor Y ((shriek l E c).obj M.obj) K.obj houtput K.property,
      integral_projection_mates l E k X Y f d c M K⟩

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
