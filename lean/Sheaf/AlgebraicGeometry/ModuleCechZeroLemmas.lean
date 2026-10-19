/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison

/-! # Two identities of the degree-zero Cech comparison

The two helper identities of the former `Sheaf.AlgebraicGeometry.ModuleCechComparison` that
its consumers used through `import all`; that module now re-exports its upstream twin, which
keeps them inline (upstream sync 69cccb9b8).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Restrictions of global sections commute with coefficient morphisms.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
theorem moduleCechZero_naturality {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {F G : X.Modules} (f : F ⟶ G) :
    moduleCechZero U F ≫
        ((CategoryTheory.cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            f.val)).f 0 =
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map f ≫ moduleCechZero U G := by
  apply Pi.hom_ext
  intro y
  dsimp [moduleCechZero, CategoryTheory.cechComplexFunctor,
    FormalCoproduct.cochainComplexFunctor, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.map]
  simp only [Category.assoc]
  erw [Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
  ext x
  simp only [ModuleCat.comp_apply]
  exact PresheafOfModules.naturality_apply f.val _ x

/-- The two restrictions of a global section to each pairwise intersection agree.
Source: Stacks 01EQ (blueprint: def-sc-module-cech-comparison). -/
theorem moduleCechZero_d {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) :
    moduleCechZero U F ≫
      ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).d 0 1 = 0 := by
  change moduleCechZero U F ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj F.presheafModuleCat) 0 = 0
  dsimp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Fin.sum_univ_two]
  simp only [
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    Preadditive.comp_add, Preadditive.comp_neg]
  rw [← sub_eq_add_neg]
  apply sub_eq_zero.mpr
  apply Pi.hom_ext
  intro y
  dsimp [moduleCechZero, FormalCoproduct.cosimplicialObjectFunctor,
    FormalCoproduct.evalOp, CosimplicialObject.δ]
  simp only [Category.assoc]
  erw [Pi.lift_π, Pi.lift_π]
  erw [Pi.lift_π_assoc, Pi.lift_π_assoc]
  congr 1
  erw [← F.presheafModuleCat.map_comp, ← F.presheafModuleCat.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.Modules
