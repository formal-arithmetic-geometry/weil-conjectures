/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyChosenMap

/-! # Affine residue data for the chosen geometric maps

Source: Stacks Project, Tags 0B91, 0BF2, 01IB and 08CR.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

This intermediate statement retains the derived-fibre targets. The enclosing theorem
later composes these with the geometric fibre comparisons. -/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The finite family of dependent derived-category maps requires extra elaboration heartbeats.
/-- The affine residue comparisons and chain representatives can be chosen before
transporting to structure-sheaf cohomology. -/
theorem picard_residue_homology_chosen_geometric_data
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
 :
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
      (φ : ∀ i, K ⟶ C i),
      ∀ i z, eC i (affineResidueCycleHomologyMap (φ i) z) =
        (derivedFiberCohomologyFunctor W w 1).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k)
          (eK z) := by
  classical
  let _hw := hw
  let _τ := τ
  let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj L))
  let Ei := fun i ↦ (schemeDerivedDirectImage (pullback.snd (fi i) k)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (pullback (fi i) k).toRingedSpace)) 0).obj
        ((Modules.tensorPullback (pullback.fst (fi i) k)).obj
          ((Modules.tensorPullback (ui i)).obj L)))
  obtain ⟨m⟩ := hE
  obtain ⟨eK, heK⟩ := affine_residue_model_naturality W w U hwU hU p hp E K hK m
  let R := (SheafOfModules.overFunctor.{v}
    (moduleRings W.toRingedSpace) U).mapDerivedCategory
  let b : ∀ i, E ⟶ Ei i := fun i ↦
    picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k
  let m' : ∀ i, R.obj (Ei i) ≅ DerivedCategory.Q.obj (C i) := fun i ↦
    Classical.choice (hCi i)
  have hdata : ∀ i, ∃ (eCi : affineResidueCycleHomology W U p (C i) ≃+
      derivedFiberCohomology W (Ei i) 1 w) (φi : K ⟶ C i),
      ∀ z, eCi (affineResidueCycleHomologyMap φi z) =
        (derivedFiberCohomologyFunctor W w 1).map (b i) (eK z) := by
    intro i
    obtain ⟨eCi, φi, heCi⟩ := picard_residue_homology_choose_model_map W w U
      hU hwU p hp E (Ei i) (b i) K (C i) hK (hC i) m (m' i) eK
      (heK (Ei i) (b i) (C i) (hC i) (m' i))
    exact ⟨eCi, φi, heCi⟩
  choose eC φ heC using hdata
  exact ⟨eK, eC, φ, heC⟩

end AlgebraicGeometry.Scheme
