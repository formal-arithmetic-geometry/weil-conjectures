/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerBound
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGlobalChartAdjunction
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerChartAdjunctionLevels

/-! # Gluing the local tower adjunctions

The shared definitions are re-exported unchanged. The proof combines global chart
representability with its finite compatibility and proves uniqueness by transposes.
Source: blueprint det-sp-tower-gluing, Local pairs, Gluing, Uniformity and Levels.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

private theorem tower_gluing_hF
    (pchar : ℕ) (_hp : 0 < pchar) (_hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj) := by
  have : Fact pchar.Prime :=
    ⟨(CharP.char_is_prime_or_zero k pchar).resolve_right (Nat.ne_of_gt _hp)⟩
  have : IsSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  intro M
  exact ((sp_tower_bound l E pchar k (Ne.symm _hne) X Y f d
    (Or.inl inferInstance) (CondensedRing.compactificationOverField f) b o
    (q.abelian X.left) (q.abelian Y.left)).2.2 M.obj M.property).2

private theorem counit_unique_iso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (K : D)
    (G' : C) (eps : F.obj G' ⟶ K)
    (rep : ∀ M : C, Function.Bijective (fun a : M ⟶ G' ↦ F.map a ≫ eps)) :
    ∃! i : G.obj K ≅ G', F.map i.hom ≫ eps = adj.counit.app K := by
  obtain ⟨a, ha⟩ := (rep (G.obj K)).2 (adj.counit.app K)
  let z : G' ⟶ G.obj K := adj.homEquiv _ _ eps
  have hz : F.map z ≫ adj.counit.app K = eps := by
    exact (adj.homEquiv _ _).symm_apply_apply eps
  have az : a ≫ z = 𝟙 _ := by
    apply (adj.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, F.map_comp, Category.assoc,
      hz, ha, F.map_id, Category.id_comp]
  have za : z ≫ a = 𝟙 _ := by
    apply (rep G').1
    simp only [F.map_comp, Category.assoc, ha, hz, F.map_id, Category.id_comp]
  refine ⟨⟨a, z, az, za⟩, ha, ?_⟩
  intro i hi
  apply Iso.ext
  exact (rep (G.obj K)).1 (hi.trans ha.symm)

/-- The representing pair on the full uniformly constructible finite-Tor tower category,
its uniqueness, every counit-normalized coordinate chart, and all finite-level comparisons.
Source: latest blueprint, det-sp-tower-gluing, clauses (1)--(3)
(blueprint: det-sp-tower-gluing).

Proof:
1. Choose the finite admissible coordinate cover of lem-sp-smooth-admissible-coordinate-cover.
Apply lem-sp-tower-chart-admissibility to K: all chart models share its cohomological and
Tor intervals shifted by -2d. The empty scheme has the zero pair.
2. lem-sp-tower-coordinate-adjunction supplies the chart representing pairs. Their counits
are etale fibre summation followed by the ordered projective-line integrations, as actual
tower maps, with their finite evaluations. The graph-extension construction of
lem-sp-varying-ring-graph-summand gives etale_normalized: transport its ordinary
sum-to-compact-support map through the section-normalized graph coordinates.
3. Induct on the number of charts. On U union V, identify the overlap pairs uniquely by
lem-sp-tower-binary-counit-representability, apply lem-sp-tower-binary-ctf-fibre, and use
the former lemma for its representing counit. This preserves the same common intervals.
4. On any further chart restriction still represents the local functor. Uniqueness of
representing pairs gives the counit-preserving chart isomorphism.
5. Transpose either counit under the other representing bijection. The resulting two maps
are inverse by injectivity. For K -> L transpose its composite with the counit at K.
Injectivity proves identity and composition laws, naturality, and both triangle identities.
This constructs the right adjoint without choosing cones functorially.
6. lem-sp-tower-evaluated-representability applies to every finite ctf test object. It gives
natural comparisons with the finite right adjoints and matches both units and counits.
7. lem-sp-tower-reduction-transpose identifies reductions with the coefficient counit mate
followed by the finite right adjoint of the reduction of K. The equality includes n=m
and all triple reductions, using the recorded ordinary scalar associators.
-/
theorem tower_gluing
    (pchar : ℕ) (_hp : 0 < pchar) (_hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    ∃ hF : ∀ M : SpTowerCalculus.C l E b q X.left,
        spConstructibleTorTowers l E Y.left (q.abelian Y.left)
          ((SpTowerCalculus.F l E b o q
            (CondensedRing.compactificationOverField f)).obj M.obj),
      ∃ G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left,
      ∃ adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G,
        Nonempty (Charts l E b o q k X Y
          ⟨inferInstance, inferInstance, inferInstance⟩ f d
          (CondensedRing.compactificationOverField f) hF G adj) ∧
        Nonempty (Levels l E b o q (CondensedRing.compactificationOverField f) hF G adj) ∧
        ∀ (K : SpTowerCalculus.C l E b q Y.left)
          (G' : SpTowerCalculus.C l E b q X.left)
          (ε' : (support l E b o q (CondensedRing.compactificationOverField f) hF).obj G' ⟶ K),
          (∀ M : SpTowerCalculus.C l E b q X.left,
            Function.Bijective (fun a : M ⟶ G' ↦
              (support l E b o q (CondensedRing.compactificationOverField f) hF).map a ≫ ε')) →
          ∃! i : G.obj K ≅ G',
            (support l E b o q (CondensedRing.compactificationOverField f) hF).map i.hom ≫ ε' =
              adj.counit.app K := by
  have : Fact pchar.Prime :=
    ⟨(CharP.char_is_prime_or_zero k pchar).resolve_right (Nat.ne_of_gt _hp)⟩
  have hF := tower_gluing_hF l E b o q pchar _hp _hne k X Y f d
  obtain ⟨G, adj, ⟨charts⟩⟩ :=
    tower_global_chart_adjunction l E b o q pchar k _hne X Y f d hF
  obtain ⟨levels⟩ :=
    tower_chart_adjunction_levels l E b o q pchar k _hne X Y f d hF G adj charts
  refine ⟨hF, G, adj, ⟨charts⟩, ⟨levels⟩, ?_⟩
  intro K G' eps rep
  exact counit_unique_iso adj K G' eps rep

end AlgebraicGeometry.ProEtale.SpTowerGluing

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
