/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.FreeSitePullback
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeReading

/-! # Independent coefficient/pullback infrastructure: FreeReading -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The existing free-module site reading is compatible with the actual finite
coefficient pullback comparison and the canonical geometric pullbacks. -/
lemma purity_comparisonUpperStarFreeIso_pullback
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (finiteCoefficientModEquivalence X T).functor.map
          ((Strategy3.freeFunctorCompUpperStarIso
            (coeffRing T) g).hom.app (ν^*(Y)[Ab.{u + 1}].obj M)) ≫
        (finiteCoefficientModEquivalence X T).functor.map
          ((Mod.freeFunctor (condensedRingObj (coeffRing T) X)).map
            ((comparisonUpperStarUpperStarIso Ab.{u + 1} g).hom.app M)) ≫
        (comparisonUpperStarFreeIso T X).hom.app ((Etale.upperStar Ab.{u + 1} g).obj M) =
      (upperStarFiniteCoefficientModEquivalenceIso g T).hom.app
          ((Mod.freeFunctor (condensedRingObj (coeffRing T) Y)).obj
            (ν^*(Y)[Ab.{u + 1}].obj M)) ≫
        (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].map
          ((comparisonUpperStarFreeIso T Y).hom.app M) ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (coeffType.{u} T)) g).hom.app
          ((Etale.extendScalars (coeffType.{u} T) Y).obj M) ≫
        ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)].map
          ((Etale.upperStarExtendScalarsIso (coeffType.{u} T) g).hom.app M) := by
  rw [purity_comparisonUpperStarFreeIso_hom_app,
    purity_comparisonUpperStarFreeIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (purityFiniteCoefficientFreeIso T X).hom.naturality
    ((comparisonUpperStarUpperStarIso Ab.{u + 1} g).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% (purity_upperStarFiniteCoefficient_free T g (ν^*(Y)[Ab.{u + 1}].obj M))]
  have h := purity_comparisonFreeSheaf_pullback_forward T g M
  simp only [purityComparisonFreePullbackIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] at h
  rw [← h]


end AlgebraicGeometry.ProEtale.Strategy3
