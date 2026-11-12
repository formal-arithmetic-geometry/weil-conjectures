/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
public import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyChosenGeometricData
import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedFibreNaturality

/-! # Affine residue data for the chosen geometric maps

Source: Stacks Project, Tags 0B91, 0BF2, 01IB and 08CR.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

(blueprint: new-picard-residue-homology-chosen-geometric-fibre-data)

This intermediate statement packages affine residue data with the geometric fibre comparisons.
The enclosing theorem only composes additive equivalences. -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
  picardDerivedCoefficientMap structureSheafAb structureSheafCohomologyPullback

set_option maxHeartbeats 800000 in
-- The dependent family of derived-category maps requires extra elaboration heartbeats.
/-- For fixed strictly perfect affine models, the coefficient arrows have chain
representatives intertwining the canonical affine residue comparisons, and geometric fibre
comparisons `e`, `ei` intertwine the derived coefficient arrows with structure-sheaf pullback.

Proof: Apply the affine residue data theorem to choose the chain maps, and
`picard_derived_fibre_naturality` to choose `e` and `ei`. -/
theorem picard_residue_homology_chosen_geometric_fibre_data
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
    (m : ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K))
    (C : Fin n → CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hC : ∀ i, IsStrictlyPerfect W U (C i))
    (m' : ∀ i, ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
            ((Modules.tensorPullback (ui i)).obj L)))) ≅ DerivedCategory.Q.obj (C i))) :
    ∃ (φ : ∀ i, K ⟶ C i)
      (e : derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd f k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst f k)).obj L))) 1 w ≃+
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (ei : ∀ i, derivedFiberCohomology W
        ((schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
            ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
              ((Modules.tensorPullback (ui i)).obj L)))) 1 w ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1),
      ∀ i, DerivedCategory.Q.map (φ i) = m.inv ≫ (SheafOfModules.overFunctor.{v}
          (moduleRings W.toRingedSpace) U).mapDerivedCategory.map
            (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) ≫ (m' i).hom ∧
        (∀ z, affineResidueModelEquiv W w U hwU hU p hp _ (C i) (hC i) (m' i)
            (affineResidueCycleHomologyMap (φ i) z) =
          (derivedFiberCohomologyFunctor W w 1).map
            (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k)
            (affineResidueModelEquiv W w U hwU hU p hp _ K hK m z)) ∧
        ∀ z, ei i ((derivedFiberCohomologyFunctor W w 1).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k) z) =
          structureSheafCohomologyPullback
            (((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                (ui i) (hui i))).left) 1 (e z) := by
  obtain ⟨φ, hφ⟩ := picard_residue_homology_chosen_geometric_data
    f Xi fi ui hui L W k w s hw τ U hwU hU p hp K hK m C hC m'
  obtain ⟨e, he⟩ := picard_derived_fibre_naturality
    f Xi fi ui hui L W k w s hw τ
  choose ei hei using he
  exact ⟨φ, e, ei, fun i ↦ ⟨(hφ i).1, (hφ i).2, hei i⟩⟩

end AlgebraicGeometry.Scheme
