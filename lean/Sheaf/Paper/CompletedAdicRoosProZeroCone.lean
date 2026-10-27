/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Paper.KoszulReconstructionModels
public import Sheaf.Algebra.Homology.ExactProductsRoosComparison
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # The concrete completed adic Roos functor kills pro-zero cones

Source: Stacks Project, Tags 0940 and 0941.
(blueprint: lem-weil-pbc-completed-adic-roos-pro-zero-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

private instance roosAbSheafify :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} T

private instance roosAbLocallyBijective :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

private theorem countableProducts_exact :
    HasExactLimitsOfShape (Discrete ℕ) (CompletedAdicModules T d) := by
  let B := CompletedAdicModules T d
  have hp (F G : ℕ → B) (f : ∀ n, F n ⟶ G n) (hf : ∀ n, Epi (f n)) :
      Epi (Limits.Pi.map f) :=
    (ProEt.countableProducts_exact.{t, 0, 0} T (completedAdicCommRing T d)).2.2 ℕ F G f hf
  have : (lim (J := Discrete ℕ) (C := B)).PreservesEpimorphisms := by
    constructor
    intro F G f hf
    have h : lim.map f = (Pi.isoLimit F).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit G).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp only [Category.assoc, Pi.isoLimit_hom_π, Limits.Pi.map_π,
        Pi.isoLimit_inv_π_assoc, ← limMap_eq, limMap_π]
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) :=
      hp (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩) (fun n ↦ f.app ⟨n⟩)
        (fun n ↦ inferInstance)
    rw [h]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi B (Discrete ℕ)


/-- The concrete Roos fibre kills an eventually derived-zero strict cone tower.

Source: Stacks Project, Tags 0940 and 0941; the pro-zero derived-limit argument.
(blueprint: lem-weil-pbc-completed-adic-roos-pro-zero-cone).

Proof: countable products of completed module sheaves are exact by the pro-etale
countable-products theorem. The strict derived-limit comparison supplies an evaluation
isomorphism between the derived image of the strict cone and its tower of levelwise
derived complexes. Naturality of this isomorphism transports each zero transition to
zero in that tower. The pro-zero clause of the ringed strict derived-limit theorem
then makes the derived-limit map invertible. The exact-products Roos comparison
identifies this map with the derived image of the displayed concrete fibre map.
A chain map has invertible derived image precisely when it is a quasi-isomorphism. -/
theorem completedAdicRoosMapQuasiIsoOfProZero
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : CochainComplex (CompletedAdicTowers T d) ℤ} (v : X ⟶ Y)
    (hv : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map
      ((CochainComplex.mappingCone v).asFunctor.map (homOfLE h).op) = 0) :
    QuasiIso (ExactProductsRoos.fibre.map v) := by
  have : HasExactLimitsOfShape (Discrete ℕ) (CompletedAdicModules T d) :=
    countableProducts_exact T d
  obtain ⟨RF, η, _, hI, _, hshift, hp, E, ε, p, δ, _, _, _, _, _, hi⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients (ProEt.topology T)
      (completedAdicRing T d) (completedAdicRing_mul_comm T d)
  have hE : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m),
      (E.obj (DerivedCategory.Q.obj (CochainComplex.mappingCone v))).map (homOfLE h).op =
        0 := by
    intro n
    obtain ⟨m, h, hm⟩ := hv n
    refine ⟨m, h, ?_⟩
    apply (cancel_mono ((ε.app (CochainComplex.mappingCone v)).hom.app (Opposite.op n))).1
    have hn := (ε.app (CochainComplex.mappingCone v)).hom.naturality (homOfLE h).op
    dsimp only [Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map] at hn
    rw [hn]
    change _ ≫ DerivedCategory.Q.map
      ((CochainComplex.mappingCone v).asFunctor.map (homOfLE h).op) = 0 ≫ _
    rw [hm, comp_zero, zero_comp]
  have hv' := hi X Y v hE
  obtain ⟨e, _⟩ := ExactProductsRoos.comparisonIso RF η hI
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (CompletedAdicModules T d) _).1
    ((NatIso.isIso_map_iff e v).2 hv')

end AlgebraicGeometry.Scheme
