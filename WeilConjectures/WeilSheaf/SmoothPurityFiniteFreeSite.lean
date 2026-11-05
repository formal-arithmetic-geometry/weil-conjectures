/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreePullback

/-! # Factoring the finite free-module comparison through the pro-étale site -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

private lemma purity_leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] (X : Scheme.{u})

/-- Free sheaves commute with the comparison-site inverse image. -/
noncomputable def purityComparisonFreeSheafIso :
    ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T X ≅
      Etale.extendScalars (ULift.{u + 1} T) X ⋙
        ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  (conjugateIsoEquiv
    ((Etale.extendScalarsAdjunction (ULift.{u + 1} T) X).comp (comparisonAdjunction _ X))
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
  apply (conjugateIsoEquiv
    ((Etale.extendScalarsAdjunction (ULift.{u + 1} T) X).comp (comparisonAdjunction _ X))
    (((comparisonAdjunction Ab.{u + 1} X).comp
      (Mod.freeForgetAdjunction (condensedRingObj (Profinite.continuousMapRingObj T) X))).comp
        (finiteCoefficientModEquivalence X T).toAdjunction)).injective
  rw [Equiv.apply_symm_apply]
  rw [conjugateIsoEquiv_trans _
      ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X)),
    conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} X).comp
      ((Mod.freeForgetAdjunction _).comp (finiteCoefficientModEquivalence X T).toAdjunction)),
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator]
  simp only [purityComparisonFreeSheafIso, purityFiniteCoefficientFreeIso,
    Equiv.apply_symm_apply]
  ext N
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    NatIso.ofComponents_hom_app]

end AlgebraicGeometry.ProEtale
