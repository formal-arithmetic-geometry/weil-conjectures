/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.AlgebraicGeometry.HypercoverFreeAbelianZero
import Sheaf.AlgebraicGeometry.HypercoverFreeAbelianPositive
import Sheaf.AlgebraicGeometry.HypercoverFreeModuleZero
import Sheaf.AlgebraicGeometry.HypercoverFreeModulePositive
import Sheaf.AlgebraicGeometry.HypercoverInjectiveAbelianZero
import Sheaf.AlgebraicGeometry.HypercoverInjectiveAbelianPositive
import Sheaf.AlgebraicGeometry.HypercoverInjectiveModuleZero
import Sheaf.AlgebraicGeometry.HypercoverInjectiveModulePositive

/-!
# Blueprint statements

lem-weil-pbc-hypercover-free-resolution.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover

/-- Blueprint: lem-weil-pbc-hypercover-free-resolution. -/
theorem freeAbelian_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) AddCommGrpCat.{w + 1}).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w + 1})).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero => exact hypercover_freeAbelian_quasiIsoAt_zero U
  | succ n => exact hypercover_freeAbelian_quasiIsoAt_pos U (n + 1) (Nat.succ_pos n)

/-- Blueprint: lem-weil-pbc-hypercover-free-resolution. -/
theorem injective_abelian_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  exact ⟨(hypercover_injective_abelian_zero U I).1,
    (hypercover_injective_abelian_zero U I).2,
    hypercover_injective_abelian_positive U I⟩

/-- Blueprint: lem-weil-pbc-hypercover-free-resolution. -/
theorem freeModule_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R] :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) (ModuleCat.{w + 1} R)).obj
            (ModuleCat.free R) ⋙
          presheafToSheaf X.smallEtaleTopology (ModuleCat.{w + 1} R))).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) := by
  rw [quasiIso_iff]
  intro i
  cases i with
  | zero => exact hypercover_freeModule_quasiIsoAt_zero U R
  | succ n => exact hypercover_freeModule_quasiIsoAt_pos U R (n + 1) (Nat.succ_pos n)

/-- Blueprint: lem-weil-pbc-hypercover-free-resolution. -/
theorem injective_module_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [CommRing R]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) := by
  exact ⟨(hypercover_injective_module_zero U R I).1,
    (hypercover_injective_module_zero U R I).2,
    hypercover_injective_module_positive U R I⟩

end AlgebraicGeometry.SplitEtaleHypercover
