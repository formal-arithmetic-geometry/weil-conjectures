/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.FiniteSupportCoordinates
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleConstructibility
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Preservation for fixed compact-support tower operations

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
`sk-prop-sp-tower-geometric-gluing.proof.md`, Uniformity and Levels
(blueprint: lem-sp-global-fixed-preservation).

The preservation proof belongs to the supplied base, operations, and section-normalized
coordinates. The full constructible finite-Tor tower category has uniform bounds, without
requiring its objects to be normalized towers.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

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

/-- The specified compact-support functor preserves the uniformly bounded constructible
finite-Tor tower category for every separated finite-type map over the field.
Source: blueprint, geometric tower gluing proof, Uniformity and Levels
(blueprint: lem-sp-global-fixed-preservation).

Proof:
1. Fix a separated finite-type k-morphism f, an arbitrary compactification c, and an
input tower K in the recorded subcategory. The one-element affine cover of Spec k is
Noetherian and Spec k has dimension zero. Apply
`lem-cbc-compactification-geometry-fibre-bound` to the structure morphism of Y, which
gives Y a finite Noetherian affine cover and finite dimension, and then to f, which gives
a geometric fibre bound d independent of the coefficient level and of K. The open factor
of c is quasi-compact since f is. Keep c fixed.
2. The predicate of `sk-def-sp-normalized-towers` supplies one Tor interval [v,w] for all
levels of K and levelwise finite-Tor constructibility. Let RC be the realization of K for
the supplied b. The supplied levelComparison identifies each finite evaluation of RC with
the corresponding level of K; Tor amplitude transports along isomorphisms by composing
representative isomorphisms, and constructibility by applying homology and the restriction
to fixed modules of `lem-weil-pbc-proetale-constant-module-constructibility`.
3. Apply both clauses of `det-sp-tower-bound-uniform` to f, c, d, [v,w] and RC. The tower
clause gives the common output interval [v,w+2d] and cohomology vanishing outside it;
transport them to the levels of F K through the inverse realization counit and the target
levelComparison. Each quotient R_n = O_E/ell^(n+1) is killed by ell^(n+1). The finite
clause gives finite constructibility of the finite compact-support image of RC_n. The
ringed open extension is identified with the intrinsic one by uniqueness of left adjoints
to the fixed constant-ring pullback; deriving this isomorphism, whiskering with the proper
direct image and composing with `def-sp-tower-shriek-data`'s Fcomparison transports finite
constructibility to each level of F K.
4. Levelwise finite constructibility and the common interval [v,w+2d] (ordered since v ≤ w
and d ≥ 0) are exactly spConstructibleTorTowers for F K. Since f, c and K were arbitrary,
this proves Preservation for the supplied b, o, q, with no Laws assumption, no new
operation package and no input reduction map assumed to be an isomorphism.
-/
theorem global_fixed_preservation
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [CharP k p] (_hlp : l ≠ p)
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) : Preservation l E k b o q := by
  classical
  intro X Y _ _ _ _ _ _ _ _ f _ _ _ _ c K hK
  have : QuasiCompact c.i := c.quasiCompact_openImmersion_iff.mpr inferInstance
  have hcover : ∃ (n : ℕ) (U : Fin n → (Spec (.of k)).affineOpens),
      (⨆ i, (U i).1) = ⊤ ∧ ∀ i, IsNoetherianRing Γ(Spec (.of k), (U i).1) := by
    refine ⟨1, fun _ ↦ ⟨⊤, isAffineOpen_top _⟩, by simp, ?_⟩
    intro i
    exact IsLocallyNoetherian.component_noetherian _
  have hdim : ∃ d : ℕ, topologicalKrullDim (Spec (.of k)) ≤ (d : WithBot ℕ∞) := by
    refine ⟨0, ?_⟩
    change topologicalKrullDim (PrimeSpectrum k) ≤ _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨hYcover, hYdim, -⟩ :=
    finiteType_noetherianCover_dimension_geometricFibres (Y ↘ Spec (.of k)) hcover hdim
  obtain ⟨_, _, ⟨d, hd⟩, _⟩ :=
    finiteType_noetherianCover_dimension_geometricFibres f hYcover hYdim
  have hdf (y : Y) : topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞) := hd _ _
  obtain ⟨a, z, v, w, haz, hvw, hlev⟩ := hK.2
  have hf := compactSupport_uniform_tor_bound p l k _hlp X Y f c d hdf v w hvw
  let RC := (realization l E b X (q.abelian X)).functor.obj K
  have hinput (n : ℕ) :
      spFiniteConstructibleTor X (SpTowerShriek.R l E n)
        ((SpTowerShriek.Ev l E X n).obj RC) ∧
      HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
        ((SpTowerShriek.Ev l E X n).obj RC) v w := by
    let e := (levelComparison l E b q X n).app K
    exact ⟨finite_of_iso X _ e.symm (hK.1 n), tor_of_iso X _ e.symm (hlev n).2⟩
  have houtput := hf.2 E b o RC hinput
  let FK := (F l E b o q c).obj K
  have hinterval (n : ℕ) :
      (∀ i : ℤ, (i < v ∨ w + 2 * (d : ℤ) < i) → IsZero
        ((DerivedCategory.homologyFunctor _ i).obj
          ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj FK))) ∧
      HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
        ((spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj FK)
        v (w + 2 * (d : ℤ)) := by
    let e : (SpTowerShriek.Ev l E Y n).obj
        ((SpTowerShriek.F l E b o c).obj RC) ≅
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj FK :=
      (SpTowerShriek.Ev l E Y n).mapIso
        ((realization l E b Y (q.abelian Y)).counitIso.app
          ((SpTowerShriek.F l E b o c).obj RC)).symm ≪≫
        (levelComparison l E b q Y n).app FK
    exact ⟨fun i hi ↦ ((houtput n).2 i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso e).symm,
      tor_of_iso Y _ e (houtput n).1⟩
  constructor
  · intro n
    have hnil : (l : SpTowerShriek.R l E n) ^ (n + 1) = 0 := by
      change (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)))
        ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_mem_pow (Ideal.subset_span (by simp)) (n + 1))
    have hfinite := (hf.1 (SpTowerShriek.R l E n)
      ⟨n + 1, Nat.succ_pos n, hnil⟩
      ((SpTowerShriek.Ev l E X n).obj RC) (hinput n).1 (hinput n).2).1
    let A := SpTowerShriek.R l E n
    let adj := Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback A c.i)
    let adj' := (sfIntrinsicOpenAdjunction A c.i).ofNatIsoRight
      (openSquarePullbackModel A c.i).symm
    let eopen : proEtaleRingOpenExtension c.i (proEtaleConstantRing c.Z A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison c.i A) ≅
        sfIntrinsicExtensionByZero c.i A := adj.leftAdjointUniq adj'
    let eo := (Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso eopen)
      (proEtaleConstantRingPushforward A c.g).rightDerivedFunctor).app
        ((SpTowerShriek.Ev l E X n).obj RC)
    let ei := (SpTowerShriek.Fcomparison l E b o c n).app RC ≪≫ eo.symm
    let et : (SpTowerShriek.Ev l E Y n).obj
        ((SpTowerShriek.F l E b o c).obj RC) ≅
        (spDerivedCoefficientEvaluation l E Y (q.abelian Y) n).obj FK :=
      (SpTowerShriek.Ev l E Y n).mapIso
        ((realization l E b Y (q.abelian Y)).counitIso.app
          ((SpTowerShriek.F l E b o c).obj RC)).symm ≪≫
        (levelComparison l E b q Y n).app FK
    exact finite_of_iso Y _ (ei.symm ≪≫ et) hfinite
  · exact ⟨v, w + 2 * (d : ℤ), v, w + 2 * (d : ℤ), by omega, by omega, hinterval⟩

end AlgebraicGeometry.ProEtale.SpTowerCalculus
