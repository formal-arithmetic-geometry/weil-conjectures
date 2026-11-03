/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleUnitLerayChainFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # Compact-support bounds for an individual smooth tower map

Source: blueprint latest, Uniformity
(blueprint: lem-sp-smooth-tower-compact-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpChartAdmissibility

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def open_coordinates (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    proEtaleRingDerivedOpenExtension j (proEtaleConstantRing Z A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A) ≅
      sfIntrinsicDerivedOpen A j := by
  let a := Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback A j)
  let b := (sfIntrinsicOpenAdjunction A j).ofNatIsoRight
    (openSquarePullbackModel A j).symm
  exact Functor.mapDerivedCategoryNatIso (a.leftAdjointUniq b)

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP M i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem finite_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hv⟩, hc, s, t, ht⟩ := h
  refine ⟨⟨a, b, hab, ?_⟩, ?_, s, t, tor_of_iso T A e ht⟩
  · intro i hi
    exact (hv i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · intro i
    have hcons := hc i
    rw [proEtaleModuleRestriction_constructible_iff] at hcons ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hcons

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
