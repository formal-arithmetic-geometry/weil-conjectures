/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.CompactSupportUniformTorBound
public import Sheaf.Paper.TowerOperationsGroundFieldRetagging
public import Sheaf.Paper.SmoothPurityTowerBound
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.ComparisonTorInterval
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.AffineSpace

public import Sheaf.Paper.SmoothPurityTowerChartData
import Sheaf.Paper.SmoothPurityTowerBoundsDomain
import Sheaf.Paper.SmoothPurityTowerBoundsOperations
import Sheaf.Paper.SmoothPurityTowerCompactBounds
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth chart tower admissibility

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs and Uniformity (blueprint: lem-sp-tower-chart-admissibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_origins (T : Scheme.{u}) : origins l E T := by
  intro n M hM a b s t hab hst hcoh htor
  let A := SpTowerShriek.R l E n
  obtain ⟨L, ⟨e⟩⟩ := (finiteRing_constructibleDerived_origin T A).2.2.1 M |>.mpr
    ⟨hM.2.1, hM.1⟩
  have hplus : DerivedCategory.TStructure.t.plus L.obj := by
    obtain ⟨c, d, _, hv⟩ := L.property.2
    exact ⟨c, (DerivedCategory.isGE_iff L.obj c).2 fun i hi ↦ hv i (.inl hi)⟩
  let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
  let R := finiteCoefficientIntrinsicRealization T A
  let ec := (Functor.mapDerivedCategoryCompIso C R).app L.obj
  have ht := (comparison_torAmplitudeIn_iff A T s t hst ⟨L.obj, hplus⟩).mpr
    (tor_of_iso T A ec (tor_of_iso T A e.symm htor))
  refine ⟨L.obj, L.property, ht, ?_, ⟨e⟩⟩
  apply ((finiteRing_constructibleDerived_origin T A).2.2.2 L.obj a b).mpr
  intro i hi
  have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj M) := by
    by_contra hn
    have hm := hcoh (show i ∈ proEtaleCohomologicalSupport M from hn)
    rcases hi with hi | hi
    · exact (not_lt_of_ge hm.1) hi
    · exact (not_lt_of_ge hm.2) hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)

private theorem scheme_facts {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] :
    IsNoetherian T.left ∧ CompactSpace T.left ∧ QuasiSeparatedSpace T.left ∧
      (∀ U : T.left.Opens, IsNoetherian U.toScheme ∧ CompactSpace U.toScheme ∧
        QuasiSeparatedSpace U.toScheme) ∧ origins l E T.left := by
  have : IsNoetherian T.left := isNoetherian_of_locallyOfFiniteType T.hom
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, finite_origins l E T.left⟩
  intro U
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set T.left))
  exact ⟨{}, inferInstance, inferInstance⟩

/-- All admissibility clauses for smooth charts, with separate uniform intervals and
without input normalization. The universally supplied sheaf-level Tate data are fixed by
their finite sheaves and normalized quotient transitions. Any such presentation gives
the same bounds and domains, since these properties are invariant under isomorphism.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
Local pairs and Uniformity (blueprint: lem-sp-tower-chart-admissibility).

Proof:
1. Finite type over a field is Noetherian. Its opens are Noetherian and hence qcqs.
   The fixed coefficient quotient is finite and therefore Noetherian. For each
   finite level use finiteRing_constructibleDerived_origin to obtain an etale
   bounded constructible complex. Its exact comparison reflects the prescribed
   cohomological interval; comparison_torAmplitudeIn_iff reflects the Tor interval.
   No compatibility between these independent origins is imposed.
2. Apply domain_of_level_bounds to recover the actual ordinary tower domain from
   uniform bounds and the independent finite origins of step 1.
3. elementary_tower_bounds preserves both intervals under a single inverse image
   and a specified Tate tensor; a shift subtracts its index from all endpoints.
   Compose these laws for the chart, and induct over the ordered affine stages.
   At each successor the shift subtracts two. Apply step 2 to each resulting tower.
4. Open immersions are etale; their relative dimension is zero. Relative dimensions
   add under composition and survive arbitrary base change. Thus restrictions of
   f remain smooth of dimension d, including after arbitrary geometric points;
   the standard affine projection is smooth of dimension one.
5. smooth_tower_compact_bounds applies the existing uniform compact-support theorem
   to a single smooth map and uses the canonical evaluation and open-adjunction
   comparisons. It gives finite output bounds [s,t+2d]. Step 2 gives the output
   domain. Apply this argument to the restrictions, to each affine projection with
   dimension one, and to each open or etale extension with dimension zero.
-/
theorem tower_chart_admissibility
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
    (X Y : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : SpTowerShriek.D l E Y.left) (a b s t : ℤ) (_hab : a ≤ b) (_hst : s ≤ t)
    (_hK : bounds l E Y.left K a b s t) :
    ∀ w : ∀ T : Over (Spec (.of k)), Twists l E T.left,
      (∀ T : Over (Spec (.of k)),
        IsSeparated T.hom → LocallyOfFiniteType T.hom → QuasiCompact T.hom →
        IsNoetherian T.left ∧ CompactSpace T.left ∧ QuasiSeparatedSpace T.left ∧
        (∀ U : T.left.Opens,
          IsNoetherian U.toScheme ∧ CompactSpace U.toScheme ∧
          QuasiSeparatedSpace U.toScheme) ∧ origins l E T.left) ∧
      (∀ n : ℕ, IsNoetherianRing (SpTowerShriek.R l E n) ∧
        Finite (SpTowerShriek.R l E n)) ∧
      domain l E base Y.left K ∧
      intermediate l E base ops Y w K d a b s t ∧
      (∀ (U : X.left.Opens)
        (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y.left),
        Etale e → IsSeparated e → LocallyOfFiniteType e → QuasiCompact e →
        e ≫ (AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left) = U.ι ≫ f.left →
        bounds l E U.toScheme
          (chart l E base ops e (AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left)
            (w (Over.mk (U.ι ≫ X.hom))) K d)
          (a - 2 * (d : ℤ)) (b - 2 * (d : ℤ))
          (s - 2 * (d : ℤ)) (t - 2 * (d : ℤ)) ∧
        domain l E base U.toScheme
          (chart l E base ops e (AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left)
            (w (Over.mk (U.ι ≫ X.hom))) K d) ∧
        ∀ c : Compactification e, compact l E base ops c 0) ∧
      (∀ U : X.left.Opens,
        SmoothOfRelativeDimension d (U.ι ≫ f.left) ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y.left),
          SmoothOfRelativeDimension d (pullback.snd (U.ι ≫ f.left) y)) ∧
        (∀ c : Compactification (U.ι ≫ f.left), compact l E base ops c d) ∧
        ∀ c : Compactification U.ι, compact l E base ops c 0) := by
  classical
  have hX := (scheme_facts l E X).1
  have hY := (scheme_facts l E Y).1
  have hdom (T : Over (Spec (.of k))) [IsNoetherian T.left]
      (C : SpTowerShriek.D l E T.left) (a b s t : ℤ)
      (hab : a ≤ b) (hst : s ≤ t) (hC : bounds l E T.left C a b s t) :
      domain l E base T.left C :=
    domain_of_level_bounds l E base T.left (finite_origins l E T.left)
      C a b s t hab hst hC
  obtain ⟨hpull, htwist, hshift⟩ := elementary_tower_bounds l E p k _hlp base ops
  have hcpt (Z T : Over (Spec (.of k)))
      [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      [IsSeparated T.hom] [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
      (g : Z ⟶ T) (r : ℕ) [SmoothOfRelativeDimension r g.left]
      (c : Compactification g.left) : compact l E base ops c r := by
    have := (scheme_facts l E T).1
    intro C a b s t hab hst hC
    have hb := smooth_tower_compact_bounds l E p k _hlp base ops Z T g r c
      C a b s t hab hst hC
    exact ⟨hb, hdom T _ s (t + 2 * (r : ℤ)) s (t + 2 * (r : ℤ))
      (by omega) (by omega) hb⟩
  intro w
  refine ⟨?_, ?_, hdom Y K a b s t _hab _hst _hK, ?_, ?_, ?_⟩
  · intro T hs hf hq
    exact scheme_facts l E T
  · intro n
    exact ⟨inferInstance, inferInstance⟩
  · intro r hr
    let V (j : ℕ) : Over (Spec (.of k)) :=
      Over.mk ((space Y.left j ↘ Y.left) ≫ Y.hom)
    have hVs (j : ℕ) : IsSeparated (V j).hom :=
      inferInstanceAs (IsSeparated ((space Y.left j ↘ Y.left) ≫ Y.hom))
    have hVf (j : ℕ) : LocallyOfFiniteType (V j).hom :=
      inferInstanceAs (LocallyOfFiniteType ((space Y.left j ↘ Y.left) ≫ Y.hom))
    have hVq (j : ℕ) : QuasiCompact (V j).hom :=
      inferInstanceAs (QuasiCompact ((space Y.left j ↘ Y.left) ≫ Y.hom))
    have hV (j : ℕ) : IsNoetherian (V j).left := (scheme_facts l E (V j)).1
    have hv (j : ℕ) : bounds l E (space Y.left j)
        ((SpTowerShriek.pull l E base (ops.geometry (space Y.left j ↘ Y.left))).obj K)
        a b s t :=
      hpull (V j) Y (Over.homMk (space Y.left j ↘ Y.left) rfl) K a b s t _hK
    have ht (j : ℕ) := htwist (V j) (w (V j)) _ j a b s t (hv j)
    have hs (j : ℕ) := hshift _ _ (2 * (j : ℤ)) a b s t (ht j)
    have hstage (j : ℕ) : bounds l E (space Y.left j) (stage l E base ops Y w K j)
        (a - 2 * (j : ℤ)) (b - 2 * (j : ℤ))
        (s - 2 * (j : ℤ)) (t - 2 * (j : ℤ)) := by
      induction j with
      | zero => simpa [stage] using hv 0
      | succ j ih =>
        have hp := hpull (V (j + 1)) (V j)
          (Over.homMk (projection Y.left j) (by
            dsimp [V, projection]
            rw [← Category.assoc, AffineSpace.reindex_over]))
          _ _ _ _ _ ih
        have hh := htwist (V (j + 1)) (w (V (j + 1))) _ 1 _ _ _ _ hp
        have hsh := hshift _ _ 2 _ _ _ _ hh
        change bounds l E (space Y.left (j + 1)) (stage l E base ops Y w K (j + 1))
          ((a - 2 * (j : ℤ)) - 2) ((b - 2 * (j : ℤ)) - 2)
          ((s - 2 * (j : ℤ)) - 2) ((t - 2 * (j : ℤ)) - 2) at hsh
        simpa only [V, Over.mk_left, Over.homMk_left, stage, Nat.cast_add,
          Nat.cast_one, mul_add, mul_one, sub_sub] using hsh
    have hd0 : a - 2 * (r : ℤ) ≤ b - 2 * (r : ℤ) := by omega
    have hd1 : s - 2 * (r : ℤ) ≤ t - 2 * (r : ℤ) := by omega
    refine ⟨hv r, hdom (V r) _ a b s t _hab _hst (hv r), ht r,
      hdom (V r) _ a b s t _hab _hst (ht r), hs r,
      hdom (V r) _ _ _ _ _ hd0 hd1 (hs r), hstage r,
      hdom (V r) _ _ _ _ _ hd0 hd1 (hstage r), ?_, ?_⟩
    · intro W c
      have : IsNoetherian (space Y.left r) := hV r
      let Z : Over (Spec (.of k)) := Over.mk (W.ι ≫ (V r).hom)
      have : IsSeparated Z.hom := inferInstanceAs (IsSeparated (W.ι ≫ (V r).hom))
      have : LocallyOfFiniteType Z.hom :=
        inferInstanceAs (LocallyOfFiniteType (W.ι ≫ (V r).hom))
      have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (W.ι ≫ (V r).hom))
      let g : Z ⟶ V r := Over.homMk W.ι rfl
      have : SmoothOfRelativeDimension 0 g.left :=
        inferInstanceAs (SmoothOfRelativeDimension 0 W.ι)
      exact hcpt Z (V r) g 0 c
    · intro _
      have hp := hpull (V (r + 1)) (V r)
        (Over.homMk (projection Y.left r) (by
          dsimp [V, projection]
          rw [← Category.assoc, AffineSpace.reindex_over])) _ _ _ _ _ (hstage r)
      have hh := htwist (V (r + 1)) (w (V (r + 1))) _ 1 _ _ _ _ hp
      refine ⟨hp, hdom (V (r + 1)) _ _ _ _ _ hd0 hd1 hp,
        hh, hdom (V (r + 1)) _ _ _ _ _ hd0 hd1 hh, ?_⟩
      intro c
      let g : V (r + 1) ⟶ V r := Over.homMk (projection Y.left r) (by
        dsimp [V, projection]
        rw [← Category.assoc, AffineSpace.reindex_over])
      have : SmoothOfRelativeDimension 1 g.left :=
        AffineSpace.smoothOfRelativeDimension_reindex_succ r Y.left
      exact hcpt (V (r + 1)) (V r) g 1 c
  · intro U e he hsep hft hqc hfac
    let Z : Over (Spec (.of k)) := Over.mk (U.ι ≫ X.hom)
    let V : Over (Spec (.of k)) :=
      Over.mk ((AffineSpace (ULift.{u} (Fin d)) Y.left ↘ Y.left) ≫ Y.hom)
    have hZs : IsSeparated Z.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
    have hZf : LocallyOfFiniteType Z.hom :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
    have hZq : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (U.ι ≫ X.hom))
    have hZ := (scheme_facts l E Z).1
    have hVs : IsSeparated V.hom :=
      inferInstanceAs (IsSeparated ((space Y.left d ↘ Y.left) ≫ Y.hom))
    have hVf : LocallyOfFiniteType V.hom :=
      inferInstanceAs (LocallyOfFiniteType ((space Y.left d ↘ Y.left) ≫ Y.hom))
    have hVq : QuasiCompact V.hom :=
      inferInstanceAs (QuasiCompact ((space Y.left d ↘ Y.left) ≫ Y.hom))
    have hV := (scheme_facts l E V).1
    let pe : V ⟶ Y := Over.homMk _ rfl
    let ee : Z ⟶ V := Over.homMk e (by
      dsimp [Z, V]
      rw [← Category.assoc, hfac, Category.assoc, Over.w f])
    have hp := hpull V Y pe K a b s t _hK
    have hp' := hpull Z V ee _ a b s t hp
    have ht := htwist Z (w Z) _ d a b s t hp'
    have hs := hshift _ _ (2 * (d : ℤ)) a b s t ht
    refine ⟨hs, hdom Z _ _ _ _ _ (by omega) (by omega) hs, ?_⟩
    intro c
    have : SmoothOfRelativeDimension 0 ee.left :=
      (Etale.iff_smoothOfRelativeDimension_zero e).mp he
    exact hcpt Z V ee 0 c
  · intro U
    let Z : Over (Spec (.of k)) := Over.mk (U.ι ≫ X.hom)
    have hZs : IsSeparated Z.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
    have hZf : LocallyOfFiniteType Z.hom :=
      inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
    have hZq : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (U.ι ≫ X.hom))
    have hsm : SmoothOfRelativeDimension d (U.ι ≫ f.left) := by
      simpa using (inferInstance : SmoothOfRelativeDimension (0 + d) (U.ι ≫ f.left))
    refine ⟨hsm, ?_, ?_, ?_⟩
    · intro Ω _ _ y
      infer_instance
    · intro c
      let g : Z ⟶ Y := Over.homMk (U.ι ≫ f.left) (by
        simp only [Z, Over.mk_hom, Category.assoc, Over.w f])
      have : SmoothOfRelativeDimension d g.left := hsm
      exact hcpt Z Y g d c
    · intro c
      let g : Z ⟶ X := Over.homMk U.ι rfl
      have : SmoothOfRelativeDimension 0 g.left :=
        inferInstanceAs (SmoothOfRelativeDimension 0 U.ι)
      exact hcpt Z X g 0 c

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
