/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleAffineLineCounit

import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Canonical pro-etale ordered integration arrows
Source: main-20261015 vector-bundle integration and projective-line normalization
(blueprint: def-pur-proetale-ordered-integration).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

private theorem pullback_plus (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.DerivedCategoryModule R Y) (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((Etale.ordinaryFinitePullback R f).obj K) := by
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) f).app K).symm
    (((Etale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategoryPlus.obj ⟨K, hK⟩).property)

private theorem p1Right_plus (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hN : 0 < N) (hR : (N : R) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤)))
    (K : Etale.DerivedCategoryModule R T) (hK : DerivedCategory.TStructure.t.plus K) :
    DerivedCategory.TStructure.t.plus ((Etale.ordinaryFiniteP1Right R N hR T).obj K) := by
  let X := ProjectiveLine T
  let L := Scheme.finiteEtaleTateLine X N R hR
  let H := (Etale.ordinaryFinitePullback R (ProjectiveLine T ↘ T)).obj K
  have hH := pullback_plus R (ProjectiveLine T ↘ T) K hK
  have hX := affineTraceProjectiveInvertible N T hT
  have hInv : ∀ x : X, IsUnit (N : X.presheaf.stalk x) := fun x ↦ by
    simpa only [map_natCast] using hX.map (X.presheaf.germ ⊤ x (by trivial)).hom
  have hf : ObjectProperty.flat L :=
    (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line X N hN hInv R hR 1).2.2.1
  obtain ⟨a, ha⟩ := hH
  have : H.IsGE a := ha
  let S := (DerivedCategory.singleFunctor _ 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf
  have : (S ⊗ H).IsGE (0 + a) := DerivedCategory.isGE_tensor_of_torAmplitudeIn ht H a
  have hs : DerivedCategory.TStructure.t.plus ((S ⊗ H)⟦(2 : ℤ)⟧) :=
    ⟨0 + a - 2, DerivedCategory.TStructure.t.isGE_shift _ (0 + a) 2
      (0 + a - 2) (by omega)⟩
  have hs' : DerivedCategory.TStructure.t.plus (S⟦(2 : ℤ)⟧ ⊗ H) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      (((MonoidalCategory.tensorRight H).commShiftIso (2 : ℤ)).app S).symm hs
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} R) X).app (S⟦(2 : ℤ)⟧)).app H) hs'

set_option linter.unusedVariables false in
/-- Boundedness of every ordered Tate coefficient, including arbitrary D+ input.
Source: finite Tate lines are locally free and inverse image is exact
(blueprint: def-pur-proetale-ordered-integration).
Proof: each step tensors with a flat degree-zero line, shifts by two, and applies
exact inverse image. It lowers a lower bound by two. Induct on the number of
coordinates; the zero step is the identity. No flatness of A over Z/l^r occurs.
-/
theorem rightTower_plus (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (d : ℕ) (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    DerivedCategory.TStructure.t.plus
      ((Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj K.obj) := by
  induction d with
  | zero => exact K.property
  | succ d ih =>
    let X := affineTraceTower T d
    let J := (Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj K.obj
    have hX := (affineTraceInvertible l T hT d).pow (r + 1)
    have hX' : IsUnit ((l ^ (r + 1) : ℕ) : Γ(X, ⊤)) := by
      simpa only [Nat.cast_pow] using hX
    exact pullback_plus _ (ProjectiveLine.affineChart X) _
      (p1Right_plus _ (l ^ (r + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hA X hX' J ih)

/-- The ordered pro-etale left composite. Zero coordinates means the identity.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
abbrev towerLeft (T : Scheme.{u}) (d : ℕ) :=
  Etale.affineTraceLeftTower
    (C := fun e ↦ DerivedCategory (Sheaf (Scheme.ProEt.topology (affineTraceTower T e))
      (ModuleCat.{u + 1} A))) (fun e ↦ lineLeft A (affineTraceTower T e)) d

/-- The family of Hom types in the ordered counit recursion.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
@[implicit_reducible]
def TowerCounitFamily (T : Scheme.{u}) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :=
  (d : ℕ) → (towerLeft (Scheme.finiteTateCoefficient l E n) T d).obj
    ((comparison (Scheme.finiteTateCoefficient l E n) (affineTraceTower T d)).obj
      ((Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj K)) ⟶
    (comparison (Scheme.finiteTateCoefficient l E n) T).obj K

/-- Exact zero and successor equations for the ordered counit family.
HEq only avoids expanding the defining successor identification of the right tower.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
def TowerCounitRecursion (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (e : TowerCounitFamily l E n T r hA K.obj) : Prop :=
  HEq (e 0) (𝟙 ((comparison (Scheme.finiteTateCoefficient l E n) T).obj K.obj)) ∧
    ∀ d : ℕ,
      letI := affineTraceNoetherian T d
      HEq (e (d + 1))
        ((towerLeft (Scheme.finiteTateCoefficient l E n) T d).map
          (lineCounit l E n (affineTraceTower T d)
            (affineTraceInvertible l T hT d) (infinityCartier _) r hA
            ⟨_, rightTower_plus l E n T hT r hA d K⟩) ≫ e d)

/-- The ordered counit recursion determines the entire family uniquely.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration).
Proof: use orderedCounit on the line functors and the compared right objects,
identifying each successor by the defining recursion of affineTraceRightTower.
It satisfies the displayed zero
and successor equations. Induction on the number of coordinates proves equality
of any two such families; function extensionality concludes uniqueness.
-/
theorem existsUniqueTowerCounit (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    ∃! e : TowerCounitFamily l E n T r hA K.obj,
      TowerCounitRecursion l E n T hT r hA K e := by
  let J := fun d ↦
    (comparison (Scheme.finiteTateCoefficient l E n) (affineTraceTower T d)).obj
      ((Etale.affineTraceRight _ (l ^ (r + 1)) hA T d).obj K.obj)
  let c := fun d ↦
    letI := affineTraceNoetherian T d
    lineCounit l E n (affineTraceTower T d)
      (affineTraceInvertible l T hT d) (infinityCartier _) r hA
      ⟨_, rightTower_plus l E n T hT r hA d K⟩
  let e : TowerCounitFamily l E n T r hA K.obj :=
    fun d ↦ Nat.rec (motive := fun d ↦
      (towerLeft (Scheme.finiteTateCoefficient l E n) T d).obj (J d) ⟶ J 0)
      (𝟙 _) (fun d prev ↦
        (towerLeft (Scheme.finiteTateCoefficient l E n) T d).map (c d) ≫ prev) d
  have he : TowerCounitRecursion l E n T hT r hA K e := by
    constructor
    · exact HEq.rfl
    · intro d
      exact HEq.rfl
  refine ⟨e, he, ?_⟩
  intro f hf
  funext d
  induction d with
  | zero => exact (eq_of_heq hf.1).trans (eq_of_heq he.1).symm
  | succ d ih =>
    have hf' := eq_of_heq (hf.2 d)
    have he' := eq_of_heq (he.2 d)
    rw [hf', he', ih]

/-- The unique ordered composition of the actual pro-etale line counits.
Source: blueprint affine-space trace (blueprint: def-pur-proetale-ordered-integration). -/
@[irreducible]
def towerCounit (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)))) :
    TowerCounitFamily l E n T r hA K.obj :=
  (existsUniqueTowerCounit l E n T hT r hA K).exists.choose

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
