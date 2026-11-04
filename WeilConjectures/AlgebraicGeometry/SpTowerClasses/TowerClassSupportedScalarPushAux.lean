/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarSingleCounit
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarCounitNormalization

/-! # Scalar counit transposes on K-flat degree-zero systems -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- On a K-flat degree-zero system, the derived scalar adjunct of the universal
counit followed by an ordinary map is the single of its ordinary adjunct.

Proof: the representative transpose equation of the scalar data applies to the
single complex. The ordinary adjunction on single complexes is the single of the
ordinary adjunct, and the exact restriction single comparison is the standard
localization comparison. -/
theorem scalarSingleCounit_transpose {T : Scheme.{u}} (c : Chern l E T)
    (M : Systems T (Rrings l T)) (N : Systems T (Arings l E T))
    (hM : CochainComplex.IsKFlatIndependentCoefficients
      (R := WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ (Rrings l T).obj (op n))
        (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op))
      ((HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj M))
    (e : c.scalar.model.E.obj M ⟶ N) :
    (c.scalar.adjunction.homEquiv _ _)
        ((scalarSingleCounit c).app M ≫
          (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map e) ≫
      ((WeilConjectures.SemilinearSections.res
        (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
    (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
      ((c.scalar.ordinaryAdjunction.homEquiv _ _) e) := by
  let s := c.scalar
  let G := WeilConjectures.SemilinearSections.res.{u + 1, u, u + 1}
    (coefficientSystemMap l E T)
  let P := (HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj M
  let Q := (HomologicalComplex.single (Systems T (Arings l E T)) (.up ℤ) 0).obj N
  let f : (s.model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q :=
    (HomologicalComplex.singleMapHomologicalComplex s.model.E (.up ℤ) 0).hom.app M ≫
      (HomologicalComplex.single _ (.up ℤ) 0).map e
  have ht := s.transpose_model P Q hM f
  have hg : (G.mapDerivedCategorySingleFunctor 0).hom.app N =
      G.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app N) := by
    erw [← G.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
    erw [Iso.hom_inv_id_app_assoc]
  have hf : ((s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app N =
      (HomologicalComplex.single _ (.up ℤ) 0).map
        ((s.ordinaryAdjunction.homEquiv _ _) e) := by
    exact singleAdjunct s.ordinaryAdjunction e
  have hrep : (scalarSingleCounit c).app M ≫
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map e =
      s.model.ε.app P ≫ DerivedCategory.Q.map f := by
    simp only [scalarSingleCounit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
      Iso.refl_inv, NatTrans.id_app, Functor.map_comp, f]
    erw [s.T.map_id]
    simp only [Category.assoc]
    erw [Category.id_comp, Category.id_comp]
    rfl
  rw [hrep, hg, ← Category.assoc]
  erw [ht]
  rw [← Functor.map_comp, hf]
  rfl

/-- The universal scalar counit is invertible on a K-flat degree-zero system.

Proof: the single comparisons are identities and the model counit computes the
derived extension on K-flat complexes. -/
theorem isIso_scalarSingleCounit_app {T : Scheme.{u}} (c : Chern l E T)
    (M : Systems T (Rrings l T))
    (hM : CochainComplex.IsKFlatIndependentCoefficients
      (R := WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (fun n ↦ (Rrings l T).obj (op n))
        (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op))
      ((HomologicalComplex.single (Systems T (Rrings l T)) (.up ℤ) 0).obj M)) :
    IsIso ((scalarSingleCounit c).app M) := by
  have := c.scalar.model.computes _ hM
  simp only [scalarSingleCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

end AlgebraicGeometry.ProEtale.SpTowerClasses
