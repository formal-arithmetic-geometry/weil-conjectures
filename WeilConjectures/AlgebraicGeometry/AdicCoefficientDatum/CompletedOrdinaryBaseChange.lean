/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeReconstructionEquations

/-!
# Completed and ordinary base change

For a cartesian square `g' ≫ f = f' ≫ g` and `K` on `X`, the ordinary base change map
`g^* Rf_* K ⟶ Rf'_* g'^* K` (`AdicCoefficientDatum.integralExchange`), the completed base change
map `ĝ^* Rf_* K ⟶ Rf'_* ĝ'^* K` (`AdicCoefficientDatum.completedExchange`) and the completion
maps `g^* M ⟶ ĝ^* M` (`AdicCoefficientDatum.ordinaryToCompleted`) form a commutative square.

## Main results

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.ordinaryToCompleted_comp_completedExchange`:
  the square commutes (blueprint `lemma-completed-ordinary-base-change--1`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The completion unit is natural. -/
theorem AdicCoefficientDatum.completionUnit_naturality {T : Scheme.{t}} {K L : d.derived T}
    (a : K ⟶ L) :
    a ≫ d.completionUnit T L = d.completionUnit T K ≫
      (completedRlim T (d.completedRing T)).map ((completedReductionTower T d).map a) := by
  have h := (d.constantRlimAdjunction T).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h
  rw [AdicCoefficientDatum.completionUnit, AdicCoefficientDatum.completionUnit,
    reassoc_of% h, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    (completedReductionAugmentation d T).naturality a]

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- **Completed and ordinary base change.** The square formed by the ordinary base change map
`g^* Rf_* K ⟶ Rf'_* g'^* K`, the completed base change map `ĝ^* Rf_* K ⟶ Rf'_* ĝ'^* K` and the
completion maps `g^* Rf_* K ⟶ ĝ^* Rf_* K` and `Rf'_* g'^* K ⟶ Rf'_* ĝ'^* K` commutes. This holds
for every `K`; on the inputs of the proper base change theorem for complete complexes the
completed base change map is `AdicCoefficientDatum.completedBaseChangeMap`.

Both maps are built from the counit of `f^* ⊣ Rf_*`: the completion map followed by the
reduction/pullback identification is the completion unit
(`OrderedExchange.ordinaryToCompleted_reconstruction`), the completion unit is natural, and it
commutes with `Rf'_*` (`AdicCoefficientDatum.towerProjection_properties`).
(blueprint: lemma-completed-ordinary-base-change--1) -/
theorem AdicCoefficientDatum.ordinaryToCompleted_comp_completedExchange (K : d.derived X) :
    d.ordinaryToCompleted g ((d.push f).obj K) ≫ d.completedExchange sq K =
      (d.integralExchange sq).app K ≫ (d.push f').map (d.ordinaryToCompleted g' K) := by
  let R := completedRlim Y' (d.completedRing Y')
  let R' := completedRlim X' (d.completedRing X')
  let M := (d.pull g').obj K
  let φ := (d.reductionTowerPullbackIso g').inv.app K
  -- the completion map of `g'^* K` is the completion unit followed by the
  -- reduction/pullback identification
  have hg' : d.ordinaryToCompleted g' K = d.completionUnit X' M ≫ R'.map φ := by
    rw [← OrderedExchange.ordinaryToCompleted_reconstruction, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  -- `Rf'_*` commutes with the completion unit
  have hproj := (d.towerProjection_properties f' M).2.2
  have hnat := (d.directImageRlimIso f').hom.naturality φ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hdir : (d.directImageRlimIso f').hom.app ((completedReductionTower X' d).obj M) ≫
      (completedRlim Y' (d.completedRing Y')).map ((d.towerPush f').map φ) ≫
        (d.directImageRlimIso f').inv.app ((d.towerPull g').obj
          ((completedReductionTower X d).obj K)) = (d.push f').map (R'.map φ) := by
    rw [← reassoc_of% hnat, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  simp only [AdicCoefficientDatum.completedExchange, AdicCoefficientDatum.towerV',
    AdicCoefficientDatum.towerV, AdicCoefficientDatum.towerH',
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Iso.app_hom,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc, Category.assoc]
  rw [Functor.map_comp_assoc, ← Category.assoc (d.ordinaryToCompleted _ _),
    OrderedExchange.ordinaryToCompleted_reconstruction, Functor.map_comp_assoc,
    ← Category.assoc (d.completionUnit _ _), ← d.completionUnit_naturality,
    Category.assoc, Functor.map_comp_assoc, reassoc_of% hproj, hg', Functor.map_comp]
  exact congrArg
    (fun x ↦ (d.integralExchange sq).app K ≫ (d.push f').map (d.completionUnit X' M) ≫ x) hdir

end AlgebraicGeometry.Scheme
