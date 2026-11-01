/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Separable
import WeilConjectures.FieldTheory.TensorProductDiagonal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTower.FiniteEtaleTowerConstructibleAssembly
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude

/-! # Object descent for finite etale towers

This is the concrete object-descent assertion used by the parent theorem.  It is
stated for the actual tower schemes, coefficient category, and pullback functor.
The proof is the finite-term constructible descent argument of Stacks 03TT and
09YU, followed by the faithful-flatness and finite-Tor checks.
(blueprint: lem-sf-finite-etale-tower-constructible-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.FiniteEtaleTower

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem finiteEtaleTower_constructible_object_descent
    [Finite k] [Algebra.IsSeparable k L]
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (P : C A (limitScheme (L := L) y)) :
    ∃ (i : Index k L) (P_i : C A (stage y i.val)),
      Nonempty ((pull A (projection y i.val)).obj P_i.obj ≅ P.obj) := by
  obtain ⟨K, e⟩ :=
    (show ∃ K : towerComplex A (limitScheme (L := L) y),
        Nonempty ((_root_.DerivedCategory.Q).obj K ≅ P.obj) from
      ⟨_root_.DerivedCategory.Q.objPreimage P.obj,
        ⟨_root_.DerivedCategory.Q.objObjPreimageIso P.obj⟩⟩)
  let eP := Classical.choice e
  have := (constantModelConstructibleFiniteTor_wellDefined
    (Profinite.continuousCoefficientRingObj A) (limitScheme (L := L) y)).2.1
  have hK : constantModelBoundedConstructible
        (Profinite.continuousCoefficientRingObj A) (limitScheme (L := L) y)
        ((_root_.DerivedCategory.Q).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((_root_.DerivedCategory.Q).obj K) := by
    exact ⟨
      (constantModelBoundedConstructible
        (Profinite.continuousCoefficientRingObj A) (limitScheme (L := L) y)).prop_of_iso
        eP.symm P.property.1,
      (DerivedCategory.finiteTorAmplitude _).prop_of_iso eP.symm P.property.2⟩
  obtain ⟨d⟩ := finiteEtaleTower_constructible_term_stage_descent y A K hK
  obtain ⟨P_i, e_i⟩ := finiteEtaleTower_constructible_assembly y A K d
  obtain ⟨e_i⟩ := e_i
  obtain ⟨eK⟩ := d.modelIso
  exact ⟨d.i, P_i, ⟨e_i ≪≫ eK ≪≫ eP⟩⟩

end AlgebraicGeometry.ProEtale.FiniteEtaleTower
