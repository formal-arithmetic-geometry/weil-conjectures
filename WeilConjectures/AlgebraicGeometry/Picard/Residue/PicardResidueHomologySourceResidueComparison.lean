/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
import WeilConjectures.AlgebraicGeometry.PicardResidueQuotientModelHomology

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyChosenGeometricFibreData
import WeilConjectures.AlgebraicGeometry.AbelianVariety.PicardResidueHomologyComposeData
import WeilConjectures.AlgebraicGeometry.Picard.Residue.PicardResidueHomologyGeometricDataToMaps
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! # A strictly perfect affine model computes residue cycle homology

Source: Stacks Project, Tags 01IB, 064K, 06YJ and 010V.
(blueprint: new-picard-residue-homology-comparison-source-residue)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
  picardDerivedCoefficientMap

set_option maxHeartbeats 800000 in
-- The chosen geometric square compares derived pullback and explicit tensor quotients.
/-- Choose only the chain maps and compatible fibre comparisons used by the Picard
finite-free calculation. The source comparison is common to the entire family.
Source: Stacks Project, Tags 0BF2, 0B91, 01XK, 06YJ and 010V.
(blueprint: lem-sc-picard-residue-homology-chosen-geometric-maps)

Proof: For each base-changed ui, transpose the coefficient pullback identity under
pullback/direct-image adjunction. Compose derived direct images to obtain E → Ei.
Restrict to U and conjugate by the supplied model isomorphisms. The affine perfect
representative theorem gives the chosen chain maps φi. Use one source trivialization
τ and its pullbacks to every target. The K-flat residue comparison is natural on
strictly perfect complexes, and the quotient comparison is chosen simultaneously
by picard_residue_quotient_model_homology_naturality. Compose it with derived base
change and the affine higher-direct-image comparison to obtain eK and eCi. Naturality
identifies the chosen maps with structure-sheaf pullback. The immersion and affine
evaluation identify the residue fields. The empty family still has the source
comparison. No compatibility with every representative or with arbitrary additive
equivalences is asserted. This is the single remaining geometric compatibility
obligation of the direct fixed-model route; the quotient naturality is proved. -/
theorem picard_residue_homology_chosen_geometric_maps
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
        Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
      (eC : ∀ i, affineResidueCycleHomology W U p (C i) ≃+
        Sheaf.H (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)
      (φ : ∀ i, K ⟶ C i),
      ∀ i z, eC i (affineResidueCycleHomologyMap (φ i) z) =
        structureSheafCohomologyPullback
          (((Over.pullback (S.fromSpecResidueField s)).map
            (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
              (ui i) (hui i))).left) 1 (eK z) := by
  classical
  have hdata0 := picard_residue_homology_chosen_geometric_fibre_data
    f Xi fi ui hui L W k w s hw τ U hwU hU p hp K hK hE C hC hCi
  obtain ⟨d⟩ := hdata0
  let M : ∀ i, (K ⟶ C i) → affineResidueCycleHomology W U p K →
      affineResidueCycleHomology W U p (C i) :=
    fun i ψ z ↦ (affineResidueCycleHomologyMap ψ) z
  let N : ∀ i, Sheaf.H (structureSheafAb
      (pullback f (S.fromSpecResidueField s))) 1 →
      Sheaf.H (structureSheafAb
        (pullback (fi i) (S.fromSpecResidueField s))) 1 :=
    fun i z ↦ structureSheafCohomologyPullback
      (((Over.pullback (S.fromSpecResidueField s)).map
        (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
          (ui i) (hui i))).left) 1 z
  exact picard_residue_homology_geometric_data_to_maps
    (M := M) (N := N) d

end AlgebraicGeometry.Scheme
