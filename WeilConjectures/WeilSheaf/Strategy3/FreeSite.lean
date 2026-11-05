/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.FreePullback
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeSite

/-! # Independent coefficient/pullback infrastructure: FreeSite -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] (X : Scheme.{u})

/-- Free sheaves commute with the comparison-site inverse image. -/
noncomputable def purityComparisonFreeSheafIso :
    ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T X ≅
      Etale.extendScalars (coeffType.{u} T) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (coeffType.{u} T)] :=
  (conjugateIsoEquiv
    ((Etale.extendScalarsAdjunction (coeffType.{u} T) X).comp (comparisonAdjunction _ X))
    ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X))).symm
    (Iso.refl _)

/-- The existing finite-root free-module comparison factors through the ordinary
free sheaf and the comparison-site free-sheaf isomorphism. -/
lemma purity_comparisonUpperStarFreeIso_factor :
    comparisonUpperStarFreeIso T X =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft ν^*(X)[Ab.{u + 1}] (purityFiniteCoefficientFreeIso T X) ≪≫
        purityComparisonFreeSheafIso T X := by
  unfold comparisonUpperStarFreeIso
  rw [CategoryTheory.purity_leftAdjointUniq_ofNatIsoRight]
  have h := purity_conjugate_comp_factor (comparisonAdjunction Ab.{u + 1} X)
    (Mod.freeForgetAdjunction (condensedRingObj (Profinite.continuousMapRingObj T) X))
    (finiteCoefficientModEquivalence X T).toAdjunction
    (purityFiniteFreeSheafAdjunction T X)
    ((Etale.extendScalarsAdjunction (coeffType.{u} T) X).comp (comparisonAdjunction _ X))
    (finiteCoefficientModEquivalenceInverseCompForgetIso T X).symm (Iso.refl _)
  refine Eq.trans ?_ h
  congr 1

/-- Component form of the factorization, without associator identities. -/
lemma purity_comparisonUpperStarFreeIso_hom_app
    (M : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (comparisonUpperStarFreeIso T X).hom.app M =
      (purityFiniteCoefficientFreeIso T X).hom.app (ν^*(X)[Ab.{u + 1}].obj M) ≫
        (purityComparisonFreeSheafIso T X).hom.app M := by
  rw [purity_comparisonUpperStarFreeIso_factor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  erw [Category.id_comp]


end AlgebraicGeometry.ProEtale.Strategy3
