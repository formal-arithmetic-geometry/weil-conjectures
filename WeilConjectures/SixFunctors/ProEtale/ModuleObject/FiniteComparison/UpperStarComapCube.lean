/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionUpperStar

/-!
# The finite-coefficient comparison, restriction of scalars and pullbacks: mates

Under the adjunctions `f^* ⊣ f_*`, the commutation of the finite-coefficient comparison `Φ`
(`finiteCoefficientModEquivalence`) with the pullbacks is the mate of its commutation with the
pushforwards, and the commutations of the restrictions of scalars with the pullbacks are the mates
of those with the pushforwards. On pushforwards all these commutations are identities on the
underlying abelian sheaves, so the corresponding square commutes; by
`CategoryTheory.mateEquiv_app_cube_converse` so does the cube of the pullbacks:
`ProEtale.map_comapUpperStarIso_symm_hom_app_comp_finiteCoefficientModEquivalenceComapIso_hom_app`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {T T' : Type} [TopologicalSpace T] [CommRing T]
  [IsTopologicalRing T] [DiscreteTopology T] [Finite T] [TopologicalSpace T'] [CommRing T']
  [IsTopologicalRing T'] [DiscreteTopology T'] [Finite T'] (ρ : T →+* T')

/-- The mate along the adjunctions `f^* ⊣ f_*` of the inverse of the commutation of the
finite-coefficient comparison `Φ` with the pullbacks is its commutation with the pushforwards. -/
lemma mateEquiv_upperStarFiniteCoefficientModEquivalenceIso_inv (T : Type) [TopologicalSpace T]
    [CommRing T] [IsTopologicalRing T] [DiscreteTopology T] [Finite T] :
    mateEquiv (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
      (upperStarFiniteCoefficientModEquivalenceIso f T).inv =
      TwoSquare.mk _ _ _ _ (lowerStarFiniteCoefficientModEquivalenceIso f T).hom :=
  mateEquiv_eq_of_unit _ _ _ _
    (unit_app_comp_lowerStarFiniteCoefficientModEquivalenceIso_hom_app T f)

/-- The square of pushforwards: the commutations of `Φ` with the pushforwards and with the
restrictions of scalars are compatible with the commutation of the restrictions of scalars with
the pushforwards. -/
lemma finiteCoefficientModEquivalenceComapIso_hom_app_lowerStar
    (K : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T') X)) :
    (finiteCoefficientModEquivalenceComapIso Y ρ).hom.app
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj T') f).obj K) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology Y) ρ.ulift).map
        ((lowerStarFiniteCoefficientModEquivalenceIso f T').hom.app K) =
    (finiteCoefficientModEquivalence Y T).functor.map
        ((CondensedRing.comapLowerStarIso (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) f).hom.app K) ≫
      (lowerStarFiniteCoefficientModEquivalenceIso f T).hom.app
        ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) X)).obj K) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).map
        ((finiteCoefficientModEquivalenceComapIso X ρ).hom.app K) := by
  ext U x
  rfl

/-- **The cube of the finite-coefficient comparison, restriction of scalars and pullbacks**: the
commutations of `Φ` with the pullbacks (`upperStarFiniteCoefficientModEquivalenceIso`) and with
the restrictions of scalars (`finiteCoefficientModEquivalenceComapIso`) are compatible with the
commutations of the restrictions of scalars with the pullbacks, pro-étale
(`upperStarRestrictScalarsIso`) and condensed (`CondensedRing.comapUpperStarIso`). Proof: the
mates along `f^* ⊣ f_*` form the square `finiteCoefficientModEquivalenceComapIso_hom_app_lowerStar`
(`mateEquiv_app_cube_converse`). -/
lemma upperStar_map_finiteCoefficientModEquivalenceComapIso_hom_app_comp
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T') Y)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).map
        ((finiteCoefficientModEquivalenceComapIso Y ρ).hom.app N) ≫
      (upperStarRestrictScalarsIso ρ.ulift f).hom.app
        ((finiteCoefficientModEquivalence Y T').functor.obj N) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) ρ.ulift).map
        ((upperStarFiniteCoefficientModEquivalenceIso f T').inv.app N) =
    (upperStarFiniteCoefficientModEquivalenceIso f T).inv.app
        ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) Y)).obj N) ≫
      (finiteCoefficientModEquivalence X T).functor.map
        ((CondensedRing.comapUpperStarIso (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) f).inv.app N) ≫
      (finiteCoefficientModEquivalenceComapIso X ρ).hom.app
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj T') f).obj N) := by
  refine mateEquiv_app_cube_converse
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T') f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T')) f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} T)) f)
    (upperStarFiniteCoefficientModEquivalenceIso f T').inv
    (upperStarFiniteCoefficientModEquivalenceIso f T).inv
    (CondensedRing.comapUpperStarIso (Profinite.continuousMapRingObjMap.{u} ρ
      continuous_of_discreteTopology) f).inv
    (upperStarRestrictScalarsIso ρ.ulift f).hom
    (finiteCoefficientModEquivalenceComapIso Y ρ).hom
    (finiteCoefficientModEquivalenceComapIso X ρ).hom (fun K ↦ ?_) N
  rw [mateEquiv_upperStarFiniteCoefficientModEquivalenceIso_inv,
    mateEquiv_upperStarFiniteCoefficientModEquivalenceIso_inv, CondensedRing.comapUpperStarIso_mate]
  have e := NatTrans.congr_app
    (mateEquiv_upperStarLowerStarAdjunction_upperStarRestrictScalarsIso_hom ρ.ulift f)
    ((finiteCoefficientModEquivalence X T').functor.obj K)
  erw [e, NatTrans.id_app, comp_id]
  exact finiteCoefficientModEquivalenceComapIso_hom_app_lowerStar f ρ K

/-- The form of `upperStar_map_finiteCoefficientModEquivalenceComapIso_hom_app_comp` with the
commutations of `Φ` with the pullbacks in the opposite direction. -/
lemma map_comapUpperStarIso_symm_hom_app_comp_finiteCoefficientModEquivalenceComapIso_hom_app
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T') Y)) :
    (finiteCoefficientModEquivalence X T).functor.map
        ((CondensedRing.comapUpperStarIso (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) f).symm.hom.app N) ≫
      (finiteCoefficientModEquivalenceComapIso X ρ).hom.app
        ((CondensedRing.upperStar (Profinite.continuousMapRingObj T') f).obj N) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) ρ.ulift).map
        ((upperStarFiniteCoefficientModEquivalenceIso f T').symm.inv.app N) =
    (upperStarFiniteCoefficientModEquivalenceIso f T).symm.inv.app
        ((Mod.comap (coefficientMap (Profinite.continuousMapRingObjMap.{u} ρ
          continuous_of_discreteTopology) Y)).obj N) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} T)) f).map
        ((finiteCoefficientModEquivalenceComapIso Y ρ).hom.app N) ≫
      (upperStarRestrictScalarsIso ρ.ulift f).hom.app
        ((finiteCoefficientModEquivalence Y T').functor.obj N) := by
  rw [Iso.symm_hom, Iso.symm_inv, Iso.symm_inv,
    ← cancel_epi ((upperStarFiniteCoefficientModEquivalenceIso f T).inv.app _),
    Iso.inv_hom_id_app_assoc,
    ← reassoc_of% (upperStar_map_finiteCoefficientModEquivalenceComapIso_hom_app_comp f ρ N)]
  simp [← Functor.map_comp]

end AlgebraicGeometry.ProEtale
