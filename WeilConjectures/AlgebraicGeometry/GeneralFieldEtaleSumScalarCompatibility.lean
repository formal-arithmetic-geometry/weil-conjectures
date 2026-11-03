/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralFieldCompactScalarSiteSquare
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility2
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# Graph and counit compatibility of transported scalar balancing

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts.
(blueprint: lem-pur-general-field-etale-sum-scalar-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The specified transported balancing preserves graph normalization and evaluation.
Source: latest blueprint, exceptional-reduction proof, Charts, scalar/site transport
(blueprint: lem-pur-general-field-etale-sum-scalar-compatibility).

Proof: on a finite-ctf etale origin substitute the proper/open scalar/site square and
both graph normalizations. Naturality cancels inverse site and compact-support factors.
The remaining ordinary graph equation is ordinaryChartSumNormalization. This identifies
the specified intrinsic compact-support map with the composite of three isomorphisms,
so it is invertible. Essential surjectivity and naturality extend the equation to every
intrinsic input. For evaluation, insert both counit_normalization formulas and the
constructed origin balancing. The canonical scalar/pullback square is the mate of the
restriction square. Pasting its comparison with the scalar/site mate identifies the
remaining factors with the ordinary sum/evaluation scalar equation. Apply that equation
and cancel the inverse comparison factors. Essential surjectivity on V and naturality
extend the counit equation to every intrinsic input. No coefficient flatness is used:
all comparisons are the actual derived tensor mates. -/
theorem generalFieldEtaleSumScalarCompatibility
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {U V : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (e : U ⟶ V) [e.IsOver (Spec (.of k))]
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (c : Compactification e)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (n : ℕ) (hn : 1 ≤ n) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0) (φ : A →+* B)
    [IsNoetherian U] [IsNoetherian V]
    (hFA : ∀ M : spFiniteConstructibleTorCategory U A,
        spFiniteConstructibleTor V A ((reductionCompactSupport A c.i c.g).obj M.obj))
      (hFB : ∀ M : spFiniteConstructibleTorCategory U B,
        spFiniteConstructibleTor V B ((reductionCompactSupport B c.i c.g).obj M.obj))
      (hTU : ∀ M : spFiniteConstructibleTorCategory U A,
        spFiniteConstructibleTor U B ((scalarExtensionFunctor φ U).obj M.obj))
      (hTV : ∀ K : spFiniteConstructibleTorCategory V A,
        spFiniteConstructibleTor V B ((scalarExtensionFunctor φ V).obj K.obj))
      (hTeU : ∀ L : generalFieldEtaleCtf U A,
        Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U
          ((OrdinaryScalarSite.scalar U.smallEtaleTopology
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj L.obj))
    (DA : GeneralFieldEtaleSumRealization A e c hFA)
    (DB : GeneralFieldEtaleSumRealization B e c hFB) :
        (∀ M : spFiniteConstructibleTorCategory U A,
          IsIso ((reductionDirectImageComparison φ c.i c.g).app M.obj) ∧
          (reductionDirectImageComparison φ c.i c.g).app M.obj ≫
              (DB.graph.hom.app ((reductionCtfScalar φ U hTU).obj M)).hom =
            (scalarExtensionFunctor φ V).map (DA.graph.hom.app M).hom ≫
              ((generalFieldEtaleSumScalarIso φ e c hFA hFB hTU hTV hTeU DA DB).hom.app M).hom) ∧
        (∀ K : spFiniteConstructibleTorCategory V A,
          ((generalFieldEtaleSumScalarIso φ e c hFA hFB hTU hTV hTeU DA DB).hom.app
              ((generalFieldCtfPullback A e DA.pullback_preserves).obj K)).hom ≫
              (DB.sum.map (ObjectProperty.homMk
                (X := (reductionCtfScalar φ U hTU).obj
                  ((generalFieldCtfPullback A e DA.pullback_preserves).obj K))
                (Y := (generalFieldCtfPullback B e DB.pullback_preserves).obj
                  ((reductionCtfScalar φ V hTV).obj K))
                ((directImageScalarPullbackIso φ e).inv.app K.obj))).hom ≫
              (DB.adjunction.counit.app ((reductionCtfScalar φ V hTV).obj K)).hom =
            (scalarExtensionFunctor φ V).map (DA.adjunction.counit.app K).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
