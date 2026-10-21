/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PicardDerivedCoefficientMap
public import Sheaf.AlgebraicGeometry.AffineResidueModelNaturality
public import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData

/-! Fixed-model naturality core for the derived fibre residue bridge.

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 0B91.
(blueprint: new-picard-derived-fibre-residue-bridge-core)

Proof: Apply the affine residue model naturality theorem to the coefficient
arrow and choose a chain representative by the affine perfect map theorem.
Compose the residue-to-derived-fibre comparisons with the geometric residue
comparisons.  Naturality of the geometric residue comparison gives the two
required equations simultaneously for every index.  This fixed-model core is
strictly below the common-neighbourhood selection theorem.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 1600000 in
-- The fixed-model naturality traverses derived and residue comparisons.
/-- Fixed affine-model residue naturality data for a finite family.
Source: Stacks Project, Tags 01IB, 064K, 06YJ and 0B91.
(blueprint: new-picard-derived-fibre-residue-bridge-core) -/
theorem picard_derived_fibre_residue_bridge_core
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)]
    [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (L : X.Modules) [Modules.IsInvertible L]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
      SheafOfModules.unit (pullback f (S.fromSpecResidueField s)).ringCatSheaf)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K) (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅ DerivedCategory.Q.obj K))
    (hCi : ∀ i, Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ (eK : affineResidueCycleHomology W U p K ≃+
      derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) 1 w)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        derivedFiberCohomology W
          ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
              ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
                ((Modules.tensorPullback (ui i)).obj L)))) 1 w)
      (eKg : affineResidueCycleHomology W U p K ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eCg : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i, ∃ (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (C i))
        (φ : K ⟶ C i), DerivedCategory.Q.map φ = a ∧
        (∀ z : affineResidueCycleHomology W U p K,
          eC i (affineResidueCycleHomologyMap φ z) =
            (derivedFiberCohomologyFunctor W w 1).map
              (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k)
              (eK z)) ∧
        (∀ z : affineResidueCycleHomology W U p K,
          eCg i (affineResidueCycleHomologyMap φ z) =
            structureSheafCohomologyPullback
              (((Over.pullback (S.fromSpecResidueField s)).map
                (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                  (ui i) (hui i))).left) 1 (eKg z)) := by
  sorry

end AlgebraicGeometry.Scheme
