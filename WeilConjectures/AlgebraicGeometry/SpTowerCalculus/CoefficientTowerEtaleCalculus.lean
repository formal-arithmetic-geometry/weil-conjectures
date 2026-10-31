/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerEtaleSumSupport
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerEtaleFiniteBounds

/-! # Exact étale sum calculus on coefficient towers

The étale calculus is constructed independently of any compactification compositor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P he f hf hp M i hi
  exact h.2 C P (he.map (fun z ↦ z ≪≫ e.symm)) f hf hp M i hi
private theorem finite_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  obtain ⟨⟨a, b, hab, hb⟩, hc, c, d, ht⟩ := h
  refine ⟨⟨a, b, hab, fun i hi ↦ ?_⟩, fun i ↦ ?_, c, d, tor_iso T A e ht⟩
  · exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm
  · apply (proEtaleModuleRestriction_constructible_iff T A _).mpr
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e))
      ((proEtaleModuleRestriction_constructible_iff T A _).mp (hc i))
private theorem towers_iso (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    {K L : spDerivedCoefficientTowers l E T D} (e : K ≅ L)
    (h : spConstructibleTorTowers l E T D K) : spConstructibleTorTowers l E T D L := by
  obtain ⟨hf, a, b, c, d, hab, hcd, hb⟩ := h
  let en := fun n ↦ (spDerivedCoefficientEvaluation l E T D n).mapIso e
  refine ⟨fun n ↦ finite_iso T _ (en n) (hf n), a, b, c, d, hab, hcd, fun n ↦ ⟨?_, ?_⟩⟩
  · intro i hi
    exact ((hb n).1 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (en n)).symm
  · exact tor_iso T _ (en n) (hb n).2

private theorem uniform_preserves
    {U T : Scheme.{u}} (aU : SpCoefficientTowersAbelian l E U)
    (aT : SpCoefficientTowersAbelian l E T)
    (G : spDerivedCoefficientTowers l E U aU ⥤ spDerivedCoefficientTowers l E T aT)
    (Gn : ∀ n, proEtaleDerivedCategory U (SpTowerShriek.R l E n) ⥤
      proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (e : ∀ K n, (spDerivedCoefficientEvaluation l E T aT n).obj (G.obj K) ≅
      (Gn n).obj ((spDerivedCoefficientEvaluation l E U aU n).obj K))
    (hfinite : ∀ n K, spFiniteConstructibleTor U (SpTowerShriek.R l E n) K →
      spFiniteConstructibleTor T (SpTowerShriek.R l E n) ((Gn n).obj K))
    (hcoh : ∀ n K a b, cohomologicalInterval l E U n K a b →
      cohomologicalInterval l E T n ((Gn n).obj K) a b)
    (htor : ∀ n K a b, HasProEtaleTorAmplitude U (SpTowerShriek.R l E n) K a b →
      HasProEtaleTorAmplitude T (SpTowerShriek.R l E n) ((Gn n).obj K) a b)
    (K : spDerivedCoefficientTowers l E U aU) (hK : spConstructibleTorTowers l E U aU K) :
    spConstructibleTorTowers l E T aT (G.obj K) := by
  obtain ⟨hf, a, b, c, d, hab, hcd, hb⟩ := hK
  refine ⟨fun n ↦ finite_iso T _ (e K n).symm (hfinite n _ (hf n)),
    a, b, c, d, hab, hcd, fun n ↦ ⟨?_, ?_⟩⟩
  · intro i hi
    exact (hcoh n _ a b (hb n).1 i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (e K n))
  · exact tor_iso T _ (e K n).symm (htor n _ c d (hb n).2)

private def pullback_eval (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : Coordinates l E b)
    {U T : Scheme.{u}} (e : U ⟶ T)
    (K : spDerivedCoefficientTowers l E T (q.abelian T)) (n : ℕ) :
    (spDerivedCoefficientEvaluation l E U (q.abelian U) n).obj
        ((etalePullback l E b o q e).obj K) ≅
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).obj
        ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K) := by
  exact ((levelComparison l E b q U n).app _).symm ≪≫
    (SpTowerShriek.Ev l E U n).mapIso
      ((realization l E b U (q.abelian U)).counitIso.app _) ≪≫
    ((o.geometry e).pullEvaluation n).app _ ≪≫
    (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).mapIso
      ((levelComparison l E b q T n).app K)

private theorem extension_interval (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (z : FiniteCoordinates l E)
    {U T : Scheme.{u}} {e : U ⟶ T} [Etale e] (d : EtaleOperation l E b o z e)
    (n : ℕ) (K : proEtaleDerivedCategory U (SpTowerShriek.R l E n)) (a c : ℤ)
    (h : cohomologicalInterval l E U n K a c) :
    cohomologicalInterval l E T n ((finiteEtaleDerived l E b o z d n).obj K) a c := by
  have := d.finiteAdditive n
  have := d.finiteLimits n
  have := d.finiteColimits n
  intro i hi
  exact Functor.isZero_homologyFunctor_mapDerivedCategory_obj
    (finiteEtaleExtension e (SpTowerShriek.R l E n)) (h i hi)

private theorem pullback_interval {U T : Scheme.{u}} (e : U ⟶ T) (n : ℕ)
    (K : proEtaleDerivedCategory T (SpTowerShriek.R l E n)) (a c : ℤ)
    (h : cohomologicalInterval l E T n K a c) :
    cohomologicalInterval l E U n
      ((proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).obj K) a c := by
  intro i hi
  exact Functor.isZero_homologyFunctor_mapDerivedCategory_obj
    (proEtaleConstantRingPullback (SpTowerShriek.R l E n) e) (h i hi)

/-- Exact étale sum extension, its unbounded derived adjunction and its comparison
with compact support, together with constructibility and unchanged interval bounds.
Source: Stacks 03DI--03DJ, 03S5 and blueprint Local pairs and Levels.

Proof: The sum-support theorem supplies normalized exact ordinary operations,
their termwise unbounded derived adjunctions and compact-support comparisons.
The extension is determined up to its adjunction-normalized isomorphism by its fixed
right adjoint. Transport the assumed compact-support preservation along the support
comparison to obtain preservation by extension. The finite-bounds theorem supplies
finite constructibility and unchanged Tor intervals. Exact functors commute with
homology, so the cohomological interval assertions follow directly. Conjugating the
recorded pullback evaluation comparison by realization counits gives the finite
evaluation comparison in original coordinates. Transport finite constructibility,
cohomology vanishing and Tor amplitude across that comparison, retaining the input's
four common bounds for all levels; this proves pullback preservation of towers.
Package these fields into EtaleCalculus. No geometric compositor is used.
(blueprint: lem-route-geometric-calculus-etale-existence). -/
theorem etale_calculus_exists
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (h : Preservation l E k b o q) :
    Nonempty (EtaleCalculus l E k b o q z) := by
  classical
  let data {U T : Scheme.{u}}
      [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
      [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
      [T.Over (Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
      [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
      (e : U ⟶ T) [e.IsOver (Spec (.of k))]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e] [Etale e] :=
    Classical.choice (etale_sum_support_exists l E pchar hp hne k b o x laws q z e)
  refine ⟨{
    etale := fun e ↦ (data e).1
    etale_shriek := by
      intro U T _ _ _ _ _ _ _ _ e _ _ _ _ _ c
      exact (data e).2 c
    etale_preserves := ?_
    finite_etale_constructible := ?_
    finite_etale_intervals := ?_ }⟩
  · intro U T _ _ _ _ _ _ _ _ e _ _ _ _ _
    obtain ⟨hf, hi⟩ := etale_finite_bounds l E pchar hp hne k b o q z e (data e).1
    constructor
    · intro K
      have := hasCompactification_of_finiteType_over_field k U T e
      let c := HasCompactification.compactification e
      exact towers_iso l E T (q.abelian T) (((data e).2 c).app K)
        (h e c K.obj K.property)
    · intro K
      exact uniform_preserves l E (q.abelian T) (q.abelian U)
        (etalePullback l E b o q e)
        (fun n ↦ proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e)
        (pullback_eval l E b o q e)
        (fun n L hL ↦ (hf n).2 L hL)
        (pullback_interval l E e)
        (fun n L a c hL ↦ (hi n a c).2 L hL) K.obj K.property
  · intro U T _ _ _ _ _ _ _ _ e _ _ _ _ _ n
    exact (etale_finite_bounds l E pchar hp hne k b o q z e (data e).1).1 n
  · intro U T _ _ _ _ _ _ _ _ e _ _ _ _ _ n a c
    have hi := (etale_finite_bounds l E pchar hp hne k b o q z e (data e).1).2 n a c
    exact ⟨fun K ↦ ⟨extension_interval l E b o z (data e).1 n K a c, hi.1 K⟩,
      fun K ↦ ⟨pullback_interval l E e n K a c, hi.2 K⟩⟩


end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
