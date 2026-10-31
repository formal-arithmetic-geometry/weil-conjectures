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

/-- The compactification composite for one smooth map has the finite uniform bounds.
This asserts bounds only; the actual ordinary tower domain is a separate argument.
Source: blueprint latest, Uniformity, chart-admissibility proof steps 7--8
(blueprint: lem-sp-smooth-tower-compact-bounds).

Proof: separated schemes of finite type over the field are Noetherian and qcqs, and
so are their opens. Thus the open factor of the chosen compactification is
quasi-compact. Smoothness of relative dimension d bounds all geometric fibres by d;
this uses base change even at algebraic closures of nonclosed residue fields.
Apply compactSupport_uniform_tor_bound to each level with the same input Tor
interval [s,t]. The actual coefficient R_n is finite and killed by ell^(n+1).
The finite assertion gives intrinsic constructibility and Tor interval [s,t+2d];
the tower assertion gives the cohomology vanishing in the same interval.
Fcomparison identifies evaluated tower compact support with the finite composite.
Its open and direct-image factors are the canonical constant-ring factors, identified
by their normalized inverse-image adjunctions. Transfer all finite properties across
these isomorphisms. The resulting bounds are independent of n and of the input
cohomological interval; no normalization of C or new tower morphism is used. -/
theorem smooth_tower_compact_bounds
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (hlp : l ≠ p)
    (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
    (X Y : Over (Spec (.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (c : Compactification f.left) (C : SpTowerShriek.D l E X.left)
    (a b s t : ℤ) (_hab : a ≤ b) (hst : s ≤ t)
    (hC : bounds l E X.left C a b s t) :
    bounds l E Y.left ((SpTowerShriek.F l E base ops c).obj C)
      s (t + 2 * (d : ℤ)) s (t + 2 * (d : ℤ)) := by
  classical
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  have : f.left.IsOver (Spec (.of k)) := ⟨Over.w f⟩
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  have hsep : IsSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have hft : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  have : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
  have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  have : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
  have hd (y : Y.left) : topologicalKrullDim
      (↑(pullback f.left (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.left.residueField y) (AlgebraicClosure (Y.left.residueField y)))) ≫
          Y.left.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞) := by
    exact topologicalKrullDim_le_of_smoothOfRelativeDimension (pullback.snd _ _) d
  have h := compactSupport_uniform_tor_bound p l k hlp X.left Y.left f.left c d hd
    s t hst
  intro n
  have hout := h.2 E base ops C (fun n ↦ ⟨(hC n).1, (hC n).2.2⟩) n
  have hnil : (l : SpTowerShriek.R l E n) ^ (n + 1) = 0 := by
    change (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)))
      ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) (n + 1))
  have hfinite := h.1 (SpTowerShriek.R l E n) ⟨n + 1, Nat.succ_pos n, hnil⟩
    ((SpTowerShriek.Ev l E X.left n).obj C) (hC n).1 (hC n).2.2
  let eo := (Functor.isoWhiskerRight (open_coordinates (SpTowerShriek.R l E n) c.i)
    (proEtaleConstantRingPushforward (SpTowerShriek.R l E n) c.g).rightDerivedFunctor).app
      ((SpTowerShriek.Ev l E X.left n).obj C)
  let e := (SpTowerShriek.Fcomparison l E base ops c n).app C ≪≫ eo.symm
  refine ⟨finite_of_iso Y.left (SpTowerShriek.R l E n) e.symm hfinite.1, ?_, hout.1⟩
  intro q hq
  by_contra hn
  have hv : IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((SpTowerShriek.Ev l E Y.left n).obj ((SpTowerShriek.F l E base ops c).obj C))) := by
    apply hout.2 q
    exact (not_and_or.mp hn).imp (fun h ↦ lt_of_not_ge h) (fun h ↦ lt_of_not_ge h)
  exact hq hv

end AlgebraicGeometry.ProEtale.SpChartAdmissibility
