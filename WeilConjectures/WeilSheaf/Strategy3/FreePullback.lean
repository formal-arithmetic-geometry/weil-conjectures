/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Strategy3.FinitePullback
public import WeilConjectures.WeilSheaf.Strategy3.FiniteRoots
public import WeilConjectures.WeilSheaf.Strategy3.ChangeCoefficients
public import WeilConjectures.WeilSheaf.SmoothPurityFiniteFreePullback

/-! # Independent coefficient/pullback infrastructure: FreePullback -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- Extension of scalars from abelian sheaves on the pro-étale site. -/
noncomputable def purityFiniteFreeSheaf (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T)) :=
  Sheaf.composeAndSheafify (ProEt.topology X)
    (ModuleCat.extendScalarsAddCommGrp (coeffType.{u} T))

/-- The free/forget adjunction on the pro-étale site. -/
noncomputable def purityFiniteFreeSheafAdjunction (X : Scheme.{u}) :
    purityFiniteFreeSheaf T X ⊣
      sheafCompose (ProEt.topology X) (forget₂ (ModuleCat.{u + 1} (coeffType.{u} T)) Ab.{u + 1}) :=
  Sheaf.adjunction _ (ModuleCat.extendScalarsAddCommGrpAdj (coeffType.{u} T))

/-- The finite coefficient equivalence carries free module objects to free sheaves. -/
noncomputable def purityFiniteCoefficientFreeIso (X : Scheme.{u}) :
    Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) X) ⋙
        (finiteCoefficientModEquivalence X T).functor ≅ purityFiniteFreeSheaf T X :=
  (conjugateIsoEquiv (purityFiniteFreeSheafAdjunction T X)
    ((Mod.freeForgetAdjunction _).comp (finiteCoefficientModEquivalence X T).toAdjunction)).symm
    (finiteCoefficientModEquivalenceInverseCompForgetIso T X).symm

/-- Free sheaves commute with geometric pullback by the canonical mate of the
identity on the underlying direct-image abelian sheaves. -/
noncomputable def purityFiniteFreeSheafPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    purityFiniteFreeSheaf T Y ⋙ (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)] ≅
      (g)^*[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf T X :=
  (conjugateIsoEquiv ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
    (purityFiniteFreeSheafAdjunction T X))
    ((purityFiniteFreeSheafAdjunction T Y).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (coeffType.{u} T)) g))).symm
    (Iso.refl _)

lemma purity_finiteCoefficientInverseForget_inv_app (X : Scheme.{u})
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T))) :
    (finiteCoefficientModEquivalenceInverseCompForgetIso T X).inv.app N =
      (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (coeffType.{u} T)) Ab.{u + 1})).map
          ((finiteCoefficientModEquivalence X T).counitInv.app N) := by
  simp [finiteCoefficientModEquivalenceInverseCompForgetIso]

lemma purity_finiteCoefficient_forget_map (X : Scheme.{u})
    {M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)} (a : M ⟶ N) :
    (Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) X)).map a =
      (sheafCompose (ProEt.topology X)
        (forget₂ (ModuleCat.{u + 1} (coeffType.{u} T)) Ab.{u + 1})).map
          ((finiteCoefficientModEquivalence X T).functor.map a) := rfl

lemma purity_lowerStarFiniteCoefficient_forget_inv {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ (ModuleCat.{u + 1} (coeffType.{u} T)) Ab.{u + 1})).map
        ((lowerStarFiniteCoefficientModEquivalenceIso g T).inv.app M) = 𝟙 _ := rfl

/-- Compatibility of the inverse-equivalence forget comparison with pushforward. -/
lemma purity_finiteCoefficient_free_right_square {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (coeffType.{u} T))) :
    (g)_*[Ab.{u + 1}].map
        ((finiteCoefficientModEquivalenceInverseCompForgetIso T X).inv.app N) =
      (finiteCoefficientModEquivalenceInverseCompForgetIso T Y).inv.app
          ((g)_*[ModuleCat.{u + 1} (coeffType.{u} T)].obj N) ≫
        (Mod.forget (condensedRingObj (Profinite.continuousMapRingObj T) Y)).map
          ((Iso.inverseCompIso (Iso.isoCompInverse (lowerStarFiniteCoefficientModEquivalenceIso g T)
            ≪≫ Functor.associator _ _ _)).inv.app N) := by
  rw [purity_finiteCoefficientInverseForget_inv_app,
    purity_finiteCoefficientInverseForget_inv_app, purity_finiteCoefficient_forget_map,
    Adjunction.functor_map_inverseCompIso_isoCompInverse_inv_app]
  simp only [Functor.map_comp]
  rw [← Functor.map_comp_assoc]
  erw [Equivalence.counitIso_inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp,
    purity_lowerStarFiniteCoefficient_forget_inv]
  erw [Category.comp_id]
  rfl

/-- The actual finite coefficient pullback comparison respects the free-module
comparisons. This is the coefficient-reading part of the finite Tate line square. -/
lemma purity_upperStarFiniteCoefficient_free {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Sheaf (ProEt.topology Y) Ab.{u + 1}) :
    (finiteCoefficientModEquivalence X T).functor.map
          ((Strategy3.freeFunctorCompUpperStarIso
            (Profinite.continuousMapRingObj T) g).hom.app M) ≫
        (purityFiniteCoefficientFreeIso T X).hom.app ((g)^*[Ab.{u + 1}].obj M) =
      (upperStarFiniteCoefficientModEquivalenceIso g T).hom.app
          ((Mod.freeFunctor (condensedRingObj (Profinite.continuousMapRingObj T) Y)).obj M) ≫
        (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)].map
          ((purityFiniteCoefficientFreeIso T Y).hom.app M) ≫
        (purityFiniteFreeSheafPullbackIso T g).hom.app M := by
  apply purity_free_pullback_cube
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Mod.freeForgetAdjunction _) (Mod.freeForgetAdjunction _)
    (Strategy3.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) g)
    (finiteCoefficientModEquivalence Y T).toAdjunction
    (finiteCoefficientModEquivalence X T).toAdjunction
    (purityFiniteFreeSheafAdjunction T Y) (purityFiniteFreeSheafAdjunction T X)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (coeffType.{u} T)) g)
  intro N
  simp only [purityFiniteCoefficientFreeIso, purityFiniteFreeSheafPullbackIso,
    Strategy3.freeFunctorCompUpperStarIso, upperStarFiniteCoefficientModEquivalenceIso,
    Adjunction.symm_conjugateIsoEquiv_symm_apply, Equiv.apply_symm_apply,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Iso.symm_hom]
  simpa only [Functor.comp_obj, Category.comp_id] using
    purity_finiteCoefficient_free_right_square T g N


end AlgebraicGeometry.ProEtale.Strategy3
