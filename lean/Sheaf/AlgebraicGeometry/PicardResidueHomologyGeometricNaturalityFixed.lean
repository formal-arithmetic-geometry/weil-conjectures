/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.AffineResidueCycleHomology
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage

import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Geometric naturality after passing to residue homology

Source: Stacks Project, Tags 0B91, 0BF2 and 01XK.
(blueprint: lem-sc-picard-residue-homology-geometric-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-! Naturality after fixing the geometric comparison equivalences.
(blueprint: new-picard-residue-homology-naturality-fixed) -/

/-- Auxiliary split theorem.
Proof: With the additive equivalences fixed, apply the coefficient pullback adjunction
unit to each ui and pass to the derived direct-image arrows. Functoriality of derived
residue pullback and the termwise K-flat comparison show that every chain map phi
whose derived arrow is the resulting a i satisfies the stated homology equation.
(blueprint: new-picard-residue-homology-naturality-fixed-positive) -/
theorem picard_residue_homology_geometric_naturality_fixed_positive
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
    (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
    (hn : 0 < n) :
    ∃ (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z) := by sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

theorem picard_residue_homology_geometric_naturality_fixed
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i)))
    (eK : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
    (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1) :
    ∃ (a : ∀ i, DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i)),
      ∀ i (φ : K ⟶ C i), DerivedCategory.Q.map φ = a i →
        ∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eK z) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    intro i
    exact Fin.elim0 i
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    exact picard_residue_homology_geometric_naturality_fixed_positive
      f Xi fi ui hui L W k w s hw τ U hwU hU p hp K hK hE C hC hCi eK eC hnpos


end AlgebraicGeometry.Scheme
