/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Derived.PicardDerivedCoefficientMap
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedFiberCohomologyFunctor
import WeilConjectures.AlgebraicGeometry.Affine.AffineResidueModelNaturality
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative

/-! Affine residue data for the fixed-model bridge.

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 0B91.
(blueprint: new-picard-derived-fibre-residue-affine-data)

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
(blueprint: new-picard-derived-fibre-residue-affine-data) -/
theorem picard_derived_fibre_residue_affine_data
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
    (w : W) (s : S) (_hw : k w = s)
    (_τ : (Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
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
      (φ : ∀ i, K ⟶ C i),
    ∀ i z, eC i (affineResidueCycleHomologyMap (φ i) z) =
        (derivedFiberCohomologyFunctor W w 1).map
          (picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k)
          (eK z) := by
  classical
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
  have hE' : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
      DerivedCategory.Q.obj K) := ⟨m⟩
  obtain ⟨eK, heK⟩ := affine_residue_model_naturality W w U hwU hU p hp E K hK m
  let R := (SheafOfModules.overFunctor.{v}
    (moduleRings W.toRingedSpace) U).mapDerivedCategory
  let b : ∀ i, E ⟶ Ei i := fun i ↦
    picardDerivedCoefficientMap f (fi i) (ui i) (hui i) L W k
  let m' : ∀ i, R.obj (Ei i) ≅ DerivedCategory.Q.obj (C i) := fun i ↦
    Classical.choice (hCi i)
  have hdata : ∀ i, ∃ (eCi : affineResidueCycleHomology W U p (C i) ≃+
      derivedFiberCohomology W (Ei i) 1 w) (φi : K ⟶ C i),
      (∀ z, eCi (affineResidueCycleHomologyMap φi z) =
        (derivedFiberCohomologyFunctor W w 1).map (b i) (eK z)) ∧
      DerivedCategory.Q.map φi = m.inv ≫ R.map (b i) ≫ (m' i).hom := by
    intro i
    obtain ⟨eCi, heCi⟩ := heK (Ei i) (b i) (C i) (hC i) (m' i)
    obtain ⟨φi, hφi⟩ := perfect_affine_map_representative W U hU K (C i)
      hK (hC i) (m.inv ≫ R.map (b i) ≫ (m' i).hom)
    exact ⟨eCi, φi, heCi φi hφi, hφi⟩
  choose eC φ hdata hφ using hdata
  exact ⟨eK, eC, φ, hdata⟩
end AlgebraicGeometry.Scheme
