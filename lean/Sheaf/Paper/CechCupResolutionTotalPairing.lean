/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct
import Sheaf.Paper.CupCechTotalCochainPairing
import Sheaf.Algebra.Homology.NatCochainPairingDescent

/-! # The two axis squares of the signed total Cech pairing

Source: Stacks Project, Tags 07MB and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
open scoped TensorProduct

private def map_cycle {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (L.sc n).moduleCatLeftHomologyData.K :=
  (L.sc n).moduleCatCyclesIso.hom
    (HomologicalComplex.cyclesMap φ n ((K.sc n).moduleCatCyclesIso.inv a))

private theorem map_cycle_val {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (map_cycle φ n a).val = φ.f n a.val := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
      (L.sc n).moduleCatCyclesIso.hom ≫ (L.sc n).moduleCatLeftHomologyData.i =
      (K.sc n).moduleCatLeftHomologyData.i ≫ φ.f n := by
    rw [ShortComplex.moduleCatCyclesIso_hom_i]
    change (K.sc n).moduleCatCyclesIso.inv ≫
      ShortComplex.cyclesMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) ≫
        (L.sc n).iCycles = _
    rw [ShortComplex.cyclesMap_i, ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
    rfl
  exact congrArg (fun k ↦ k a) h

private theorem map_cycle_class {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.homologyMap φ n (cupCycleClass K n a) =
      cupCycleClass L n (map_cycle φ n a) := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ ≫
      HomologicalComplex.homologyMap φ n =
      (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (L.sc n).homologyπ := by
    exact congrArg ((K.sc n).moduleCatCyclesIso.inv ≫ ·)
      (ShortComplex.homologyπ_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))
  have h' : (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ ≫
      HomologicalComplex.homologyMap φ n =
      (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (L.sc n).moduleCatCyclesIso.hom ≫ (L.sc n).moduleCatCyclesIso.inv ≫
          (L.sc n).homologyπ := by
    rw [Iso.hom_inv_id_assoc]
    exact h
  exact congrArg (fun k ↦ k a) h'


set_option maxHeartbeats 2000000 in
-- Comparing the canonical total-complex maps requires nested degree transports.
/-- The signed total Cech pairing preserves both axes: restriction of global
resolution cocycles and augmentation of coefficient Cech cocycles.
Source: Stacks Project, Tag 07MB (signed total map) and Tag 0FKV, proof, final diagram.
(blueprint: lem-sc-cech-cup-resolution-total-pairing)

Proof: take the signed total cochain morphism and its two axis equations.
Descend its tensor-of-cycles formula to a bilinear map on homology. The component
identities alpha_f and beta_f identify the six comparison maps with the canonical
axis maps. Naturality of cycle classes then turns both cochain axis identities
into the required homology identities. -/
theorem cupCechResolution_total_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap A.alpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.alpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.alpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c)) := by
  have hA : A.alpha = cupCechAlpha U D.left := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact A.alpha_f n
  have hB : B.alpha = cupCechAlpha U D.right := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact B.alpha_f n
  have hC : C.alpha = cupCechAlpha U D.target := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact C.alpha_f n
  have kA : A.beta = cupCechBeta U D.left := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact A.beta_f n
  have kB : B.beta = cupCechBeta U D.right := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact B.beta_f n
  have kC : C.beta = cupCechBeta U D.target := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact C.beta_f n
  obtain ⟨h, ha, hb⟩ := exists_cupCech_total_cochain_pairing U D
  obtain ⟨t, ht⟩ := natCochain_pairing_descent _ _ _ h p q
  refine ⟨t, ?_, ?_⟩
  · intro a b c hc
    rw [map_cycle_class, map_cycle_class, map_cycle_class]
    apply ht
    simp only [map_cycle_val]
    rw [hc, hA, hB, hC]
    exact (ha p q a.val b.val).symm
  · intro a b c hc
    rw [map_cycle_class, map_cycle_class, map_cycle_class]
    apply ht
    simp only [map_cycle_val]
    rw [hc, kA, kB, kC]
    exact (hb p q a.val b.val).symm

end
end AlgebraicGeometry.Scheme.Modules
