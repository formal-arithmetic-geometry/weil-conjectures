/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreeSite
public import WeilConjectures.WeilSheaf.SmoothPurityComparisonRestriction

/-! # Free-sheaf site comparison and geometric pullback -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The free pro-étale sheaf on the inverse image of an étale abelian sheaf
commutes with geometric pullback. -/
noncomputable def purityComparisonFreePullbackIso :
    (ν^*(Y)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T Y) ⋙
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      Etale.upperStar Ab.{u + 1} g ⋙ (ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T X) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (purityFiniteFreeSheafPullbackIso T g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (comparisonUpperStarUpperStarIso Ab.{u + 1} g) _ ≪≫
    Functor.associator _ _ _

lemma purityComparisonFreePullbackIso_conjugate :
    conjugateIsoEquiv
      ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X)))
      (((comparisonAdjunction Ab.{u + 1} Y).comp (purityFiniteFreeSheafAdjunction T Y)).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g))
      (purityComparisonFreePullbackIso T g) = Iso.refl _ := by
  unfold purityComparisonFreePullbackIso
  rw [conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} Y).comp
      ((purityFiniteFreeSheafAdjunction T Y).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g))),
    conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} Y).comp
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (purityFiniteFreeSheafAdjunction T X))),
    conjugateIsoEquiv_trans _ (((comparisonAdjunction Ab.{u + 1} Y).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} g)).comp
        (purityFiniteFreeSheafAdjunction T X)),
    conjugateIsoEquiv_trans _ (((Etale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (comparisonAdjunction Ab.{u + 1} X)).comp (purityFiniteFreeSheafAdjunction T X)),
    conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator]
  simp only [purityFiniteFreeSheafPullbackIso, comparisonUpperStarUpperStarIso,
    lowerStarComparisonLowerStarIso, Equiv.apply_symm_apply]
  ext N
  simp

/-- The site comparison respects the free-sheaf geometric datum. -/
lemma purity_comparisonFreeSheaf_pullback
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    ν^*(X)[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((Etale.upperStarExtendScalarsIso (ULift.{u + 1} T) g).hom.app M) ≫
        (purityComparisonFreeSheafIso T X).inv.app ((Etale.upperStar Ab.{u + 1} g).obj M) =
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).inv.app
          ((Etale.extendScalars (ULift.{u + 1} T) Y).obj M) ≫
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)].map
          ((purityComparisonFreeSheafIso T Y).inv.app M) ≫
        (purityComparisonFreePullbackIso T g).hom.app M := by
  apply purity_free_pullback_cube
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Etale.extendScalarsAdjunction (ULift.{u + 1} T) Y)
    (Etale.extendScalarsAdjunction (ULift.{u + 1} T) X)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)
    (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y)
    (comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) X)
    ((comparisonAdjunction Ab.{u + 1} Y).comp (purityFiniteFreeSheafAdjunction T Y))
    ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction T X))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) g)
    (Etale.upperStarExtendScalarsIso (ULift.{u + 1} T) g)
    (purityComparisonFreePullbackIso T g)
    (purityComparisonFreeSheafIso T Y).symm
    (purityComparisonFreeSheafIso T X).symm
    (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} T)) g).symm
  intro N
  rw [purityComparisonFreePullbackIso_conjugate]
  simp only [purityComparisonFreeSheafIso, comparisonUpperStarUpperStarIso,
    Etale.upperStarExtendScalarsIso, purity_leftAdjointUniq_ofNatIsoRight,
    Adjunction.symm_conjugateIsoEquiv_symm_apply, Equiv.apply_symm_apply,
    lowerStarComparisonLowerStarIso, Iso.refl_symm, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, Functor.map_id, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.ProEtale
