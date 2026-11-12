/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap

/-!
# Proper base change for complete complexes

Let `f : X ⟶ Y` be proper, `g : Y' ⟶ Y` arbitrary and `X' = X ×_Y Y'` with projections
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`. For a quotient-tower complete `K` on `X` whose reductions
`K_n` have bounded below étale origin (blueprint
`proposition-proper-base-change-complete-integral`):

* `Rf_* K` is complete (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.push_complete`);
* `ĝ^* Rf_* K ≅ Rlim_n g^* Rf_* K_n`
  (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPullPushIso`);
* `Rf'_* ĝ'^* K ≅ Rlim_n Rf'_* g'^* K_n`
  (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.pushCompletedPullIso`);
* under these, the derived limit of the finite base change maps is an isomorphism
  `ĝ^* Rf_* K ≅ Rf'_* ĝ'^* K`
  (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.isIso_completedBaseChangeMap`).

The last point reduces, by conservativity of the evaluations of derived towers, to finite-level
proper base change (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteExchange_isIso`),
once the reduction of the integral base change map is identified with the finite base change
map (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.finiteProjection_comp_finiteExchange`).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The four finite-level arrows commute: at every finite level `n`, the finite base change map
`g_n^* Rf_{n*} K_n ⟶ Rf'_{n*} g'_n^* K_n` is the reduction of the integral base change map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K`, modulo the projection-formula identifications
`(Rf_* K)_n ≅ Rf_{n*} K_n` and the reduction/pullback comparisons. This is the statement, used
in the proof of blueprint `proposition-proper-base-change-complete-integral--4`, that the finite
base change maps form a map of towers. -/
theorem AdicCoefficientDatum.finiteProjection_comp_finiteExchange (K : d.derived X) (n : ℕ) :
    (d.finitePull g n).map (d.finiteProjection f K n) ≫
        (d.finiteExchange sq n).app ((d.reduction X n).obj K) =
      (d.chi g n).hom.app ((d.push f).obj K) ≫
        (d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
        d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map (d.delta (g' := g') K n).hom := by
  sorry

/-- For proper `f`, the reduction of the integral base change map at a level whose reduction has
bounded below étale origin is an isomorphism. -/
theorem AdicCoefficientDatum.isIso_reduction_map_integralExchange [IsProper f]
    (K : d.derived X) (n : ℕ)
    (W : FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1)) ((d.reduction X n).obj K)) :
    IsIso ((d.reduction Y' n).map ((d.integralExchange sq).app K)) := by
  have := d.finiteExchange_isIso sq K n W
  have := d.finiteProjection_isIso f K n
  have := d.finiteProjection_isIso f' ((d.pull g').obj K) n
  have h := d.finiteProjection_comp_finiteExchange sq K n
  have : IsIso ((d.chi g n).hom.app ((d.push f).obj K) ≫
      (d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
        d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map (d.delta (g' := g') K n).hom) := by
    rw [← h]
    infer_instance
  have : IsIso ((d.reduction Y' n).map ((d.integralExchange sq).app K) ≫
      d.finiteProjection f' ((d.pull g').obj K) n ≫
        (d.finitePush f' n).map (d.delta (g' := g') K n).hom) :=
    IsIso.of_isIso_comp_left ((d.chi g n).hom.app ((d.push f).obj K)) _
  exact IsIso.of_isIso_comp_right _
    (d.finiteProjection f' ((d.pull g').obj K) n ≫
      (d.finitePush f' n).map (d.delta (g' := g') K n).hom)

/-- A morphism of derived towers is invertible if all its evaluations are. -/
private theorem isIso_of_isIso_evaluation
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    {X Y : DerivedCategory (ℕᵒᵖ ⥤ B)} (a : X ⟶ Y)
    (h : ∀ n : ℕᵒᵖ,
      IsIso ((((CategoryTheory.evaluation ℕᵒᵖ B).obj n).mapDerivedCategory).map a)) :
    IsIso a := by
  rw [DerivedCategory.isIso_iff]
  intro i
  have (n : ℕᵒᵖ) : IsIso
      (((DerivedCategory.homologyFunctor (ℕᵒᵖ ⥤ B) i).map a).app n) := by
    let E := (CategoryTheory.evaluation ℕᵒᵖ B).obj n
    have : IsIso ((E.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B i).map a) := by
      change IsIso ((DerivedCategory.homologyFunctor B i).map (E.mapDerivedCategory.map a))
      infer_instance
    exact (NatIso.isIso_map_iff (E.mapDerivedCategoryHomologyFunctorIso i) a).2 inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- A morphism of complexes over the completed coefficients whose reductions are all invertible
has an invertible reduction tower. -/
theorem AdicCoefficientDatum.isIso_completedReductionTower_map {T : Scheme.{t}}
    {M N : d.derived T} (φ : M ⟶ N) (h : ∀ n : ℕ, IsIso ((d.reduction T n).map φ)) :
    IsIso ((completedReductionTower T d).map φ) := by
  have he (n : ℕ) : IsIso ((reductionTowerDerivedEvaluation T
      (reductionModuleRing T (d.completedRing T)) n).map
        ((completedReductionTower T d).map φ)) := by
    have hn := (completedReductionEvaluation T d n).naturality φ
    have : IsIso ((reductionDerivedRestrict T (d.projection T n)).map
        ((d.reduction T n).map φ)) := by
      have := h n
      infer_instance
    have : IsIso ((completedReductionEvaluation T d n).app M ≫
        (reductionDerivedRestrict T (d.projection T n)).map ((d.reduction T n).map φ)) := by
      infer_instance
    have : IsIso ((reductionTowerDerivedEvaluation T
        (reductionModuleRing T (d.completedRing T)) n).map
          ((completedReductionTower T d).map φ) ≫
        (completedReductionEvaluation T d n).app N) := by
      erw [hn]
      exact this
    exact IsIso.of_isIso_comp_right _ ((completedReductionEvaluation T d n).app N)
  exact isIso_of_isIso_evaluation (B := ringedSiteModules.{t + 1}
    (reductionModuleRing T (d.completedRing T))) ((completedReductionTower T d).map φ)
    (fun n ↦ he n.unop)

/-- For proper `f`, the strict tower of finite base change maps is an isomorphism of derived
towers when every reduction of `K` has bounded below étale origin. -/
theorem AdicCoefficientDatum.isIso_towerV' [IsProper f] (K : d.derived X)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso (d.towerV' sq K) := by
  have : IsIso ((completedReductionTower Y' d).map ((d.integralExchange sq).app K)) :=
    d.isIso_completedReductionTower_map _
      fun n ↦ d.isIso_reduction_map_integralExchange sq K n (W n)
  have : IsIso (d.towerV sq K) := by
    unfold AdicCoefficientDatum.towerV
    infer_instance
  unfold AdicCoefficientDatum.towerV'
  infer_instance

/-- Blueprint `proposition-proper-base-change-complete-integral--2`: the canonical isomorphism
`ĝ^* Rf_* K ≅ Rlim_n g^* Rf_* K_n`. The completed pullback `ĝ^*` is by definition the derived
limit of the pullback of the reduction tower, and the reduction tower of `Rf_* K` is the tower
`(Rf_{n*} K_n)_n` through the projection-formula isomorphisms
(`AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerProjection`). -/
def AdicCoefficientDatum.completedPullPushIso (K : d.derived X) :
    (d.completedPull g).obj ((d.push f).obj K) ≅
      (completedRlim Y' (d.completedRing Y')).obj
        ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) :=
  (completedRlim Y' (d.completedRing Y')).mapIso
    (d.towerH (f := f) (f' := f') (g := g) (g' := g') K)

/-- Blueprint `proposition-proper-base-change-complete-integral--3`: the canonical isomorphism
`Rf'_* ĝ'^* K ≅ Rlim_n Rf'_* g'^* K_n`, since the direct image commutes with derived limits of
towers (`AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso`). -/
def AdicCoefficientDatum.pushCompletedPullIso (K : d.derived X) :
    (d.push f').obj ((d.completedPull g').obj K) ≅
      (completedRlim Y' (d.completedRing Y')).obj
        ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) :=
  (d.directImageRlimIso f').app ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The completed base change map is the derived limit of the tower of finite base change maps,
transported along the isomorphisms of blueprint
`proposition-proper-base-change-complete-integral--2` and `--3`. -/
lemma AdicCoefficientDatum.completedExchange_eq (K : d.derived X) :
    d.completedExchange sq K =
      (d.completedPullPushIso (f' := f') (g' := g') K).hom ≫
        (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) ≫
        (d.pushCompletedPullIso (g' := g') K).inv := by
  simp [AdicCoefficientDatum.completedExchange, AdicCoefficientDatum.completedPullPushIso,
    AdicCoefficientDatum.pushCompletedPullIso]

/-- Blueprint `proposition-proper-base-change-complete-integral--4`: for proper `f` and complete
`K` whose reductions `K_n` have bounded below étale origin, the derived limit of the finite base
change maps `g^* Rf_* K_n ⟶ Rf'_* g'^* K_n` is an isomorphism, and hence so is the completed base
change map `ĝ^* Rf_* K ⟶ Rf'_* ĝ'^* K`. -/
theorem AdicCoefficientDatum.isIso_completedBaseChangeMap [IsProper f] (K : d.derived X)
    (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    IsIso ((completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K)) ∧
      IsIso (d.completedBaseChangeMap sq K hK W) := by
  have := d.isIso_towerV' sq K W
  refine ⟨inferInstance, ?_⟩
  change IsIso (d.completedExchange sq K)
  rw [d.completedExchange_eq sq K]
  infer_instance

/-- Blueprint `proposition-proper-base-change-complete-integral`: **proper base change for
complete complexes**. Let `f` be proper and `K` complete with reductions of bounded below étale
origin. Then `Rf_* K` is complete, `ĝ^* Rf_* K ≅ Rlim_n g^* Rf_* K_n`,
`Rf'_* ĝ'^* K ≅ Rlim_n Rf'_* g'^* K_n`, and under these isomorphisms the derived limit of the
finite base change maps is an isomorphism `ĝ^* Rf_* K ≅ Rf'_* ĝ'^* K`. -/
theorem AdicCoefficientDatum.properBaseChange_complete [IsProper f] (K : d.derived X)
    (hK : d.TowerComplete X K)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    d.TowerComplete Y ((d.push f).obj K) ∧
      Nonempty ((d.completedPull g).obj ((d.push f).obj K) ≅
        (completedRlim Y' (d.completedRing Y')).obj
          ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K)))) ∧
      Nonempty ((d.push f').obj ((d.completedPull g').obj K) ≅
        (completedRlim Y' (d.completedRing Y')).obj
          ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K)))) ∧
      IsIso (d.completedBaseChangeMap sq K hK W) :=
  ⟨d.push_complete f K hK, ⟨d.completedPullPushIso (f' := f') (g' := g') K⟩,
    ⟨d.pushCompletedPullIso (g' := g') K⟩, (d.isIso_completedBaseChangeMap sq K hK W).2⟩

end AlgebraicGeometry.Scheme
