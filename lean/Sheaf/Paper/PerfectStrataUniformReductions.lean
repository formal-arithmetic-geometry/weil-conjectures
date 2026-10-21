/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Paper.PerfectLocalReductionModels
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import all Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all Sheaf.Paper.ConstructibleCoefficientSerre
import all Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal
import Sheaf.Algebra.Homology.SitePerfectModelRestriction

/-! # Uniform bounds and finite reductions of stratified perfect models

Source: Bhatt--Scholze, Lemma 6.6.10(1), Proposition 6.6.11, reverse implication;
Stacks Tags 06YS, 06YT, 06YU and 093J.
(blueprint: lem-weil-pbc-perfect-strata-uniform-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private def commRingInverseImageUnderlying {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf ((adicLisseForget Y).obj R) ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} :=
  (proEtale_moduleInverseImage_comparison f R).1.some

private theorem finite_lisse_of_cover_models {X Y : Scheme.{u}} (g : Y ⟶ X)
    (B : Type (u + 1)) [CommRing B]
    (F : pbcModules Y ((adicTowerInverseImage g).obj (adicLisseConstantRing X B)))
    (J : Type (u + 1)) (U : J → Y.ProEt)
    (f : ∀ j, U j ⟶ ProEt.mk (𝟙 Y))
    (hcover : Presieve.ofArrows U f ∈ (ProEt.precoverage Y).coverings _)
    (hmodel : ∀ j, ∃ M : ModuleCat.{u + 1} B, Finite M ∧
      Nonempty ((SheafOfModules.overFunctor _ (U j)).obj F ≅
        (SheafOfModules.overFunctor _ (U j)).obj
          ((proEtaleModuleInverseImage g (adicLisseConstantRing X B)).obj
            ((adicLisseConstantModules X B).obj M)))) :
    IsRelativelyFiniteLisseModule g B F := by
  apply (CoefficientSerre.relative_finite_iff g B F).mpr
  apply (CoefficientSerre.fixedFiniteSieve_iff B _).mp
  let topo := ProEt.topology Y
  let e : ProEt.mk (𝟙 Y) ≅ ⊤_ Y.ProEt :=
    (ProEt.isTerminalMkId Y).uniqueUpToIso terminalIsTerminal
  apply (GrothendieckTopology.pullback_mem_iff_of_isIso (i := e.hom)).mp
  apply (ProEt.topology Y).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_)
    (Precoverage.generate_mem_toGrothendieck hcover)
  rintro V a ⟨j⟩
  obtain ⟨M, hM, ⟨c⟩⟩ := hmodel j
  exact ⟨M, hM, ⟨(CoefficientSerre.relativeOverRestriction g B (U j)).mapIso c ≪≫
    (topo.overPullback (ModuleCat.{u + 1} B) (U j)).mapIso
      (CoefficientSerre.relativeConstantEncoding g B M)⟩⟩

private theorem constructible_of_cover_models
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : pbcModules X (adicLisseConstantRing X B))
    (S : FiniteLocallyClosedStratification X)
    (J : Fin S.n → Type (u + 1)) (U : ∀ i : Fin S.n, J i → (S.domain i).ProEt)
    (f : ∀ (i : Fin S.n) (j : J i), U i j ⟶ ProEt.mk (𝟙 (S.domain i)))
    (hcover : ∀ i, Presieve.ofArrows (U i) (f i) ∈
      (ProEt.precoverage (S.domain i)).coverings _)
    (hmodel : ∀ i j, ∃ M : ModuleCat.{u + 1} B, Finite M ∧
      Nonempty ((SheafOfModules.overFunctor _ (U i j)).obj
        ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing X B)).obj F) ≅
        (SheafOfModules.overFunctor _ (U i j)).obj
          ((proEtaleModuleInverseImage (S.immersion i) (adicLisseConstantRing X B)).obj
            ((adicLisseConstantModules X B).obj M)))) :
    IsConstructibleProEtaleCoefficientModuleSheaf X B F := by
  have : IsNoetherian X := {}
  let s := Stratification.ofNoetherianSpace S.n S.stratum S.isLocallyClosed_stratum
    S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum S.domain S.immersion
    S.isImmersion S.range_immersion
  apply (CoefficientSerre.coefficient_constructible_iff X B F).mpr
  refine ⟨s, fun i ↦ ?_⟩
  exact ProEtale.isFiniteLocallyConstant_of_iso
    (CoefficientSerre.relativePullbackComparison (s.immersion i) B F)
    ((CoefficientSerre.relative_finite_iff (s.immersion i) B _).mp
      (finite_lisse_of_cover_models (s.immersion i) B _ (J i) (U i) (f i)
        (hcover i) (hmodel i)))

private theorem uniform_bounds_of_local_vanishing
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (S : FiniteLocallyClosedStratification X)
    (J : Fin S.n → Type (u + 1)) (U : ∀ i, J i → (S.domain i).ProEt)
    (f : ∀ i j, U i j ⟶ ProEt.mk (𝟙 (S.domain i)))
    (hcover : ∀ i, Presieve.ofArrows (U i) (f i) ∈
      (ProEt.precoverage (S.domain i)).coverings _)
    (R : ℕ → Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (H : ∀ t, ℤ → pbcModules X (R t))
    (a b : ∀ i, J i → ℤ)
    (hloc : ∀ i j t q, q < a i j ∨ b i j < q →
      IsZero ((SheafOfModules.overFunctor _ (U i j)).obj
        ((proEtaleModuleInverseImage (S.immersion i) (R t)).obj (H t q)))) :
    ∃ a₀ b₀ : ℤ, a₀ ≤ b₀ ∧ ∀ t q, q < a₀ ∨ b₀ < q → IsZero (H t q) := by
  classical
  have : IsNoetherian X := {}
  let s := Stratification.ofNoetherianSpace S.n S.stratum S.isLocallyClosed_stratum
    S.iUnion_stratum_eq_univ S.pairwise_disjoint_stratum S.domain S.immersion
    S.isImmersion S.range_immersion
  have hn (i : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain i) := by
    have := S.isImmersion i
    exact (S.immersion i).isEmbedding.isInducing.noetherianSpace
  let := hn
  have hc (i : Fin S.n) : CompactSpace (ProEt.mk (𝟙 (S.domain i))).left := by
    change CompactSpace (S.domain i)
    let := hn i
    infer_instance
  let := hc
  have hcov (i : Fin S.n) : Sieve.ofArrows (U i) (f i) ∈
      ProEt.topology (S.domain i) (ProEt.mk (𝟙 (S.domain i))) :=
    Precoverage.generate_mem_toGrothendieck (hcover i)
  choose I hI V g hV hg using fun i ↦ ProEt.qc_finite_cover (S.domain i)
    (ProEt.mk (𝟙 (S.domain i))) (Sieve.ofArrows (U i) (f i)) (hcov i)
  let := hI
  have hfactor (i : Fin S.n) (j : I i) : ∃ k : J i, Nonempty (V i j ⟶ U i k) := by
    obtain ⟨W, h, l, ⟨k⟩, -⟩ := hg i j
    exact ⟨k, ⟨h⟩⟩
  choose k v using hfactor
  let v' (i : Fin S.n) (j : I i) : V i j ⟶ U i (k i j) := (v i j).some
  let L := Σ i : Fin S.n, I i
  let : Fintype L := Fintype.ofFinite L
  let a₀ : ℤ := -∑ l : L, |a l.1 (k l.1 l.2)|
  let b₀ : ℤ := ∑ l : L, |b l.1 (k l.1 l.2)|
  refine ⟨a₀, b₀, ?_, fun t q hq ↦ ?_⟩
  · have ha : 0 ≤ ∑ l : L, |a l.1 (k l.1 l.2)| :=
      Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    have hb : 0 ≤ b₀ := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    dsimp only [a₀]
    linarith
  · have hstr (i : Fin S.n) :
        IsZero ((proEtaleModuleInverseImage (S.immersion i) (R t)).obj (H t q)) := by
      let B := (adicLisseForget (S.domain i)).obj
        ((adicTowerInverseImage (S.immersion i)).obj (R t))
      have hcV : (ProEt.topology (S.domain i)).CoversTop (V i) :=
        ((ProEt.topology (S.domain i)).coversTop_iff_of_isTerminal
          (ProEt.mk (𝟙 (S.domain i))) (ProEt.isTerminalMkId _) (V i)).mpr
            ((ProEt.topology (S.domain i)).superset_covering
              (Sieve.ofArrows_le_ofObjects (V i) (g i)) (hV i))
      apply CategoryTheory.isZero_of_slice_cover B (V i) hcV
      intro j
      have hq' : q < a i (k i j) ∨ b i (k i j) < q := by
        rcases hq with hq | hq
        · left
          have hsum := Finset.single_le_sum
            (f := fun l : L ↦ |a l.1 (k l.1 l.2)|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ (⟨i, j⟩ : L))
          dsimp [a₀] at hq
          linarith [neg_abs_le (a i (k i j))]
        · right
          have hsum := Finset.single_le_sum
            (f := fun l : L ↦ |b l.1 (k l.1 l.2)|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ (⟨i, j⟩ : L))
          dsimp [b₀] at hq
          linarith [le_abs_self (b i (k i j))]
      exact ((SheafOfModules.overMap B (v' i j)).map_isZero
        (hloc i (k i j) t q hq')).of_iso
          ((SheafOfModules.overFunctorMap B (v' i j)).app _).symm
    have hz : IsZero ((SheafOfModules.toSheaf ((adicLisseForget X).obj (R t))).obj
        (H t q)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply AlgebraicGeometry.ProEtale.abDetectMaps S.immersion
      · intro x
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
          (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
        exact ⟨i, (S.range_immersion i).symm ▸ hi⟩
      · intro i
        rw [(AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1}
          (S.immersion i)).map_id]
        have hi := (SheafOfModules.toSheaf _).map_isZero (hstr i)
        have hz := hi.of_iso
          ((commRingInverseImageUnderlying (S.immersion i) (R t)).app (H t q)).symm
        exact hz.eq_of_src _ _
    apply (IsZero.iff_id_eq_zero (H t q)).2
    apply (SheafOfModules.toSheaf ((adicLisseForget X).obj (R t))).map_injective
    simpa using hz.eq_of_src
      ((SheafOfModules.toSheaf _).map (𝟙 (H t q))) ((SheafOfModules.toSheaf _).map 0)

/-- Uniform bounds for K and all positive finite reductions, intrinsic constructibility,
and finite constant models on every member of the original stratum covers.
Source: Bhatt--Scholze, Lemma 6.6.10(1), Proposition 6.6.11, reverse implication;
Stacks Tags 06YS, 06YT, 06YU and 093J
(blueprint: lem-weil-pbc-perfect-strata-uniform-reductions).

Proof: choose a bounded finite-projective representative on every original chart.
The local reduction lemma computes the completed model by its K-flat constant
complex, and every normalized finite reduction by its constant quotient tensor
complex. Exact inverse image, slice restriction and constants commute with homology.
The tensor terms are finite over the finite quotient ring, so their cycles and
homology are finite sets. This gives local vanishing intervals and finite constant
models on every original chart.

Each stratum is Noetherian and hence quasi-compact. A covering sieve of its terminal
object has a finite quasi-compact refinement, each member factoring through an
original chart. Choose this refinement once, before the reduction index. The negative
sum of the absolute lower bounds and the sum of the absolute upper bounds give one
interval containing all selected intervals; an empty family gives [0,0]. Vanishing
passes along the factoring maps, then descends along the covering sieve. Exact
underlying-abelian inverse image and detection by the finite locally closed strata
give global vanishing for K and every reduction. Scalar restriction leaves the
underlying abelian sheaf unchanged, so normalized vanishing is also raw vanishing.

For constructibility, finite constant models on the original covering sieve give
relative finite lisseness on each stratum by the intrinsic coefficient criterion.
The Noetherian finite stratification is a constructible stratification. The intrinsic
coefficient constructibility equivalence then gives the conclusion directly, retaining
the original covers and models. No completeness or compatible etale-origin witness
is concluded. -/
theorem perfect_strata_uniform_reductions
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : d.derived X) (S : FiniteLocallyClosedStratification X)
    (J : Fin S.n → Type (u + 1)) (U : ∀ i : Fin S.n, J i → (S.domain i).ProEt)
    (f : ∀ (i : Fin S.n) (j : J i), U i j ⟶ ProEt.mk (𝟙 (S.domain i)))
    (_hcover : ∀ i : Fin S.n,
      Presieve.ofArrows (U i) (f i) ∈ (ProEt.precoverage (S.domain i)).coverings _)
    (_hmodel : ∀ (i : Fin S.n) (j : J i),
      ∃ P : @DerivedCategory (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.standard _),
        @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P ∧
          Nonempty
            (@ringedSiteDerivedRestrictionOfUniverses (S.domain i).ProEt _
                (ProEt.topology (S.domain i))
                ((adicLisseForget (S.domain i)).obj
                  ((adicTowerInverseImage (S.immersion i)).obj (d.completedRing X)))
                (U i j) _ _ _ _ _ (HasDerivedCategory.standard _)
                ((adicTowerPullback (S.immersion i) (d.completedRing X)).obj K) ≅
              @ringedSiteDerivedRestrictionOfUniverses (S.domain i).ProEt _
                (ProEt.topology (S.domain i))
                ((adicLisseForget (S.domain i)).obj
                  ((adicTowerInverseImage (S.immersion i)).obj (d.completedRing X)))
                (U i j) _ _ _ _ _ (HasDerivedCategory.standard _)
                ((adicTowerPullback (S.immersion i) (d.completedRing X)).obj
                  ((pbcDerivedExtend (CompletedConstantReduction.base X d.ideal ≫
                    (pbcCompletedComparison X d).hom)).obj
                      (DerivedCategory.Q.obj
                        ((CompletedConstantReduction.constantComplex X A).obj
                          ((@DerivedCategory.Q (ModuleCat.{u + 1} A) _ _
                            (HasDerivedCategory.standard _)).objPreimage P))))))) :
    (∃ a b : ℤ, a ≤ b ∧
      (∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor
          (reductionModules X (d.completedRing X)) q).obj K)) ∧
      ∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor (reductionModules X (d.finiteRing X n)) q).obj
          ((d.reduction X n).obj K))) ∧
    (∀ (n : ℕ) (q : ℤ), IsConstructibleProEtaleCoefficientModuleSheaf X
      (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
        ((DerivedCategory.homologyFunctor (reductionModules X (d.finiteRing X n)) q).obj
          ((d.reduction X n).obj K)))) ∧
    ∀ (n : ℕ) (q : ℤ) (i : Fin S.n) (j : J i),
      ∃ M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)), Finite M ∧
        Nonempty
          ((SheafOfModules.overFunctor _ (U i j)).obj
            ((proEtaleModuleInverseImage (S.immersion i)
              (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
                ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
                  ((DerivedCategory.homologyFunctor
                    (reductionModules X (d.finiteRing X n)) q).obj
                      ((d.reduction X n).obj K)))) ≅
            (SheafOfModules.overFunctor _ (U i j)).obj
              ((proEtaleModuleInverseImage (S.immersion i)
                (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
                  ((adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1))).obj M))) := by
  classical
  choose P hP e using _hmodel
  have hlocal (i : Fin S.n) (j : J i) := by
    have := S.isImmersion i
    exact perfect_local_reduction_models (S.immersion i) d K (U i j)
      (P i j) (hP i j) (e i j)
  choose a b hab hc hr hm using hlocal
  let R : ℕ → Sheaf (ProEt.topology X) CommRingCat.{u + 1}
    | 0 => d.completedRing X
    | n + 1 => adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1))
  let H (t : ℕ) (q : ℤ) : pbcModules X (R t) :=
    match t with
    | 0 => (DerivedCategory.homologyFunctor _ q).obj K
    | n + 1 => (pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
        ((DerivedCategory.homologyFunctor _ q).obj ((d.reduction X n).obj K))
  obtain ⟨a₀, b₀, hab₀, hzero⟩ := uniform_bounds_of_local_vanishing X S J U f _hcover
    R H a b (by
      intro i j t q hq
      cases t with
      | zero => exact hc i j q hq
      | succ n => exact hr i j n q hq)
  refine ⟨⟨a₀, b₀, hab₀, hzero 0, ?_⟩, ?_, ?_⟩
  · intro n q hq
    apply (IsZero.iff_id_eq_zero _).2
    apply (SheafOfModules.toSheaf _).map_injective
    have hz := (SheafOfModules.toSheaf _).map_isZero (hzero (n + 1) q hq)
    have e : (SheafOfModules.toSheaf _).obj (H (n + 1) q) ≅
        (SheafOfModules.toSheaf _).obj
          ((DerivedCategory.homologyFunctor _ q).obj ((d.reduction X n).obj K)) := by
      exact Iso.refl _
    have hz' := hz.of_iso e.symm
    simpa using hz'.eq_of_src
      ((SheafOfModules.toSheaf _).map (𝟙 _)) ((SheafOfModules.toSheaf _).map 0)
  · intro n q
    have := d.quotientFinite n
    exact constructible_of_cover_models X (A ⧸ d.ideal ^ (n + 1)) _ S J U f _hcover
      (fun i j ↦ hm i j n q)
  · intro n q i j
    exact hm i j n q

end AlgebraicGeometry.Scheme
