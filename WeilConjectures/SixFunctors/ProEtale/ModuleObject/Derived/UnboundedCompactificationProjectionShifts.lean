/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaShift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Signed shifts of the unbounded compactification projection map

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/
lem-sf-tensor-hom.proof.md, Step 2: shifts of the actual proper/open projection ingredient
(blueprint: lem-sf-unbounded-compactification-projection-shifts).

The statement uses the existing canonical proper projection followed by the inverse open
projection and pullback compositor. All inputs belong to ordinary unbounded derived categories.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option synthInstance.maxHeartbeats 1000000 in
-- Native module-object derived tensor instances have large structural expressions.
set_option maxHeartbeats 1000000 in
-- Elaborate both native shift squares without unfolding their canonical constructions.
/-- The canonical compactification projection commutes separately with every integer shift
of either unbounded input. The tensor comparisons are the signed total-complex ones, and the
adjunction comparisons are the native unit/counit-compatible ones.

Source: latest blueprint, lem-sf-tensor-hom.proof.md, Step 2
(blueprint: lem-sf-unbounded-compactification-projection-shifts).

Proof: work with the native module-object transformations. The lax open tensor comparison
is the inverse of the signed oplax comparison, by the monoidal inverse identity. The
adjunction projection-map shift lemma therefore gives the first-variable shift square for
the open projection. Invert it and paste with the proper projection square and the pullback
compositor. The resulting transformation has exactly the components of the specified
compactification projection. For the second variable use the native source-library
CommShift instance, which expands the same proper/open composite.
No proper projection map or compact-support projection map is inverted. -/
theorem unboundedCompactificationProjection_shifts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) [QuasiCompact c.i]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) (r : ℤ) :
    (exceptionalProjectionMorphismOfCompactification Λ c (K⟦r⟧) L ≫
        (((curriedTensor _).flip.obj ((L((f)^*⟦Λ⟧)).obj L) ⋙
          Rf_!(c)⟦Λ⟧).commShiftIso r).hom.app K =
      ((Rf_!(c)⟦Λ⟧ ⋙ (curriedTensor _).flip.obj L).commShiftIso r).hom.app K ≫
        (shiftFunctor _ r).map
          (exceptionalProjectionMorphismOfCompactification Λ c K L)) ∧
    (exceptionalProjectionMorphismOfCompactification Λ c K (L⟦r⟧) ≫
        (((L((f)^*⟦Λ⟧) ⋙ (curriedTensor _).obj K) ⋙
          Rf_!(c)⟦Λ⟧).commShiftIso r).hom.app L =
      (((curriedTensor _).obj ((Rf_!(c)⟦Λ⟧).obj K)).commShiftIso r).hom.app L ≫
        (shiftFunctor _ r).map
          (exceptionalProjectionMorphismOfCompactification Λ c K L)) := by
  constructor
  · let J := D((c.i)_!open⟦Λ⟧)
    let R := R((c.g)_*⟦Λ⟧)
    let P := L((c.i)^*⟦Λ⟧)
    let N := (L((c.g)^*⟦Λ⟧)).obj L
    let T := curriedTensor (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    let S := curriedTensor (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology c.Z) Ab.{u + 1}) (condensedRingObj Λ c.Z)))
    let adj := derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction Λ c.i
    have : adj.CommShift ℤ :=
      commShift_derivedOpenImmersionLowerShriekUpperStarAdjunction_ofNatIsoRight Λ c.i
    let d := Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ c.i) N
    have : IsIso d := by
      have : ∀ M, IsIso (d.app M) := fun M ↦ by
        change IsIso (((leftDerivedUpperStarTensor Λ c.i).app M).app N)
        infer_instance
      exact NatIso.isIso_of_isIso_app d
    have : NatTrans.CommShift d ℤ := commShift_leftDerivedUpperStarTensor_flipApp Λ c.i N
    let b := Adjunction.comparisonFlipApp' P T S (Functor.LaxMonoidal.μNatTrans P) N
    have hb : b = (asIso d).inv := by
      ext M
      rw [← cancel_epi (d.app M)]
      exact (Functor.Monoidal.δ_μ P M N).trans
        ((asIso d).hom_inv_id_app M).symm
    have : NatTrans.CommShift b ℤ := by
      rw [hb]
      exact NatTrans.CommShift.of_iso_inv (asIso d) ℤ
    let q := adj.projectionMapFlipApp P T S (Functor.LaxMonoidal.μNatTrans P) N
    have : NatTrans.CommShift q ℤ :=
      Adjunction.commShift_projectionMapFlipApp adj P T S
        (Functor.LaxMonoidal.μNatTrans P) ℤ N
    have : IsIso q := by
      have : ∀ M, IsIso (q.app M) := fun M ↦ by
        change IsIso (openImmersionProjectionComparison Λ c.i M N)
        infer_instance
      exact NatIso.isIso_of_isIso_app q
    have : NatTrans.CommShift (inv q) ℤ := NatTrans.CommShift.of_isIso q ℤ
    let a : R ⋙ (curriedTensor _).flip.obj L ⟶ S.flip.obj N ⋙ R :=
      NatTrans.flipApp (projectionMap Λ c.g) L
    have : NatTrans.CommShift a ℤ := commShift_projectionMap_flipApp Λ c.g L
    let t := T.flip.map ((leftDerivedUpperStarCompactificationIso Λ c).inv.app L)
    have : NatTrans.CommShift t ℤ := by dsimp only [t]; infer_instance
    let τ : Rf_!(c)⟦Λ⟧ ⋙ (curriedTensor _).flip.obj L ⟶
        T.flip.obj ((L((f)^*⟦Λ⟧)).obj L) ⋙ Rf_!(c)⟦Λ⟧ :=
      (Functor.associator J R _).hom ≫ Functor.whiskerLeft J a ≫
        (Functor.associator J _ R).inv ≫ Functor.whiskerRight (inv q) R ≫
        (Functor.associator _ J R).hom ≫ Functor.whiskerRight t (J ⋙ R)
    have : NatTrans.CommShift τ ℤ := by dsimp only [τ]; infer_instance
    have hτ (M) : τ.app M = exceptionalProjectionMorphismOfCompactification Λ c M L := by
      simp only [τ, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        NatIso.isIso_inv_app, Functor.comp_map, Category.id_comp]
      erw [Category.id_comp, Category.id_comp]
      unfold exceptionalProjectionMorphismOfCompactification
      rw [Functor.map_comp]
      rfl
    simpa only [hτ] using (NatTrans.shift_app_comm τ r K).symm
  · exact (NatTrans.shift_app_comm
      (exceptionalProjectionMorphismOfCompactificationNatTrans Λ c K) r L).symm

end AlgebraicGeometry.ProEtale.CondensedRing
