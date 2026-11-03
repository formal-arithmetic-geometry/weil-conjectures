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
import WeilConjectures.AlgebraicGeometry.GeneralFieldChartAdjunctionRealization
import all WeilConjectures.AlgebraicGeometry.FiniteAffineRightScalarNormalForm
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionCtfFunctors
import all WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
import all WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
import all WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionData
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import all WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import all WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import all WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Trace
import all Mathlib.AlgebraicGeometry.AffineSpace
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.GeneralFieldEtaleSumRealizationExistence
import WeilConjectures.AlgebraicGeometry.GeneralFieldEtaleSumScalarCompatibility

/-!
# General-field etale/pro-etale summation counit

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts (lines 20-35):
integral summation, graph
normalization and finite-site transport
(blueprint: lem-pur-general-field-etale-proetale-counit).

The transport record retains the actual sum/evaluation counit and characterizes
its graph comparison on every etale origin.  The coefficient comparison is
likewise characterized by the ordinary summandwise balancing, rather than chosen
as an unspecified isomorphism.  No data is selected from the existence theorem.
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

set_option maxRecDepth 4096 in
private theorem generalFieldEtaleCounit_domains
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hpell : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {U V : Scheme.{u}}
    [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (e : U ⟶ V) [e.IsOver (Spec (.of k))]
    (c : Compactification e)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (n : ℕ) (hn : 1 ≤ n) (hA : ((ell ^ n : ℕ) : A) = 0)
    (hB : ((ell ^ n : ℕ) : B) = 0) (φ : A →+* B) :
    (∀ M : spFiniteConstructibleTorCategory U A,
        spFiniteConstructibleTor V A ((reductionCompactSupport A c.i c.g).obj M.obj)) ∧
    (∀ M : spFiniteConstructibleTorCategory U B,
        spFiniteConstructibleTor V B ((reductionCompactSupport B c.i c.g).obj M.obj)) ∧
    (∀ M : spFiniteConstructibleTorCategory U A,
        spFiniteConstructibleTor U B ((scalarExtensionFunctor φ U).obj M.obj)) ∧
    (∀ K : spFiniteConstructibleTorCategory V A,
        spFiniteConstructibleTor V B ((scalarExtensionFunctor φ V).obj K.obj)) ∧
    (∀ L : generalFieldEtaleCtf U A,
        Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) U
          ((OrdinaryScalarSite.scalar U.smallEtaleTopology
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj L.obj)) := by
  let : c.Z.Over (Spec (.of k)) := ⟨c.g ≫ (V ↘ Spec (.of k))⟩
  have : c.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : c.i.IsOver (Spec (.of k)) := ⟨by
    change c.i ≫ c.g ≫ (V ↘ Spec (.of k)) = U ↘ Spec (.of k)
    rw [← Category.assoc, ← c.comm, comp_over]⟩
  have : LocallyOfFiniteType (c.Z ↘ Spec (.of k)) :=
    show LocallyOfFiniteType (c.g ≫ (V ↘ Spec (.of k))) from inferInstance
  have : QuasiCompact (c.Z ↘ Spec (.of k)) :=
    show QuasiCompact (c.g ≫ (V ↘ Spec (.of k))) from inferInstance
  have : IsSeparated (c.Z ↘ Spec (.of k)) :=
    show IsSeparated (c.g ≫ (V ↘ Spec (.of k))) from inferInstance
  have hd := GeneralFieldChart.generalFieldChartDomains ell p
    (Fact.out : p.Prime).pos hpell k c.i c.g φ n hn hA hB
  exact ⟨(hd.1 A hA).2.1, (hd.1 B hB).2.1, hd.2.1, hd.2.2.1, hd.2.2.2.1⟩

set_option maxRecDepth 4096 in
/-- General-field etale/pro-etale counit and graph-normalized coefficient square.
Source: blueprint latest, reduction-exceptional proof, Charts: integral summation,
graph normalization and finite-site transport
(blueprint: lem-pur-general-field-etale-proetale-counit).

Proof: (1) use generalFieldChartAdjunctionRealization to restrict the comparison to
finite-ctf objects, transport ordinary summation with its evaluation adjunction, and
identify the graph comparison by canonicalEtaleCompactSupportNormalization.
(2) On an etale origin insert the compact-support site formula of
generalFieldCompactScalarSiteSquare, expressed in ordinary scalar coordinates. Naturality cancels
the compact-support and scalar/site factors.  The remaining etale identity follows from
Etale.etaleSumCounitScalar by uniqueness of mates for the sum and compact-support
adjunctions and their counit-preserving graph comparison.  Essential surjectivity
then gives the first displayed equation for every intrinsic M.
(3) Transport the ordinary evaluation scalar equation through the two comparison
equivalences.  The counit normalization and naturality of the ordinary scalar/site mate identify its
factors with the specified intrinsic scalar/pullback map, giving the second
equation for every K.  (4) Empty fibres give zero sums; arbitrary sheet sets use
the existing finite-support direct sum.  Identity coefficients and nonflat
Z/ell^2 to Z/ell are covered by the same derived tensor and mate calculations.
No flatness hypothesis occurs. -/
theorem generalFieldEtaleProEtaleCounit
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
    (hB : ((ell ^ n : ℕ) : B) = 0) (φ : A →+* B) :
    ∃ (hNU : IsNoetherian U) (hNV : IsNoetherian V),
    ∃ (hFA : ∀ M : spFiniteConstructibleTorCategory U A,
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
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj L.obj)),
      Nonempty (GeneralFieldEtaleSumRealization A e c hFA) ∧
      Nonempty (GeneralFieldEtaleSumRealization B e c hFB) ∧
      ∀ (DA : GeneralFieldEtaleSumRealization A e c hFA)
        (DB : GeneralFieldEtaleSumRealization B e c hFB),
      ∃ (σ : DA.sum ⋙ reductionCtfScalar φ V hTV ≅
          reductionCtfScalar φ U hTU ⋙ DB.sum),
        (∀ L : generalFieldEtaleCtf U A,
          (σ.hom.app ((reductionSiteCtf U A).obj L)).hom ≫
            (DB.sum.map (ObjectProperty.homMk
              (X := (reductionCtfScalar φ U hTU).obj ((reductionSiteCtf U A).obj L))
              (Y := (reductionSiteCtf U B).obj ((generalFieldEtaleCtfScalar φ U hTeU).obj L))
              ((generalFieldOrdinarySiteScalarIso φ U).hom.app L.obj))).hom ≫
            DB.sumSite.hom.app ((generalFieldEtaleCtfScalar φ U hTeU).obj L) =
          (scalarExtensionFunctor φ V).map (DA.sumSite.hom.app L) ≫
            (generalFieldOrdinarySiteScalarIso φ V).hom.app
              ((Etale.etaleLowerShriek
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) e inferInstance).mapDerivedCategory.obj
                L.obj) ≫
            (reductionSite B V).map
              ((CoefficientCompatibility.sumScalar
                (RingHom.ulift.{u + 1, u + 1, u, u} φ) e).hom.app L.obj)) ∧
        (∀ M : spFiniteConstructibleTorCategory U A,
          IsIso ((reductionDirectImageComparison φ c.i c.g).app M.obj) ∧
          (reductionDirectImageComparison φ c.i c.g).app M.obj ≫
              (DB.graph.hom.app ((reductionCtfScalar φ U hTU).obj M)).hom =
            (scalarExtensionFunctor φ V).map (DA.graph.hom.app M).hom ≫
              (σ.hom.app M).hom) ∧
        (∀ K : spFiniteConstructibleTorCategory V A,
          (σ.hom.app ((generalFieldCtfPullback A e DA.pullback_preserves).obj K)).hom ≫
              (DB.sum.map (ObjectProperty.homMk
                (X := (reductionCtfScalar φ U hTU).obj
                  ((generalFieldCtfPullback A e DA.pullback_preserves).obj K))
                (Y := (generalFieldCtfPullback B e DB.pullback_preserves).obj
                  ((reductionCtfScalar φ V hTV).obj K))
                ((directImageScalarPullbackIso φ e).inv.app K.obj))).hom ≫
              (DB.adjunction.counit.app ((reductionCtfScalar φ V hTV).obj K)).hom =
            (scalarExtensionFunctor φ V).map (DA.adjunction.counit.app K).hom) := by
  classical
  have hNU : IsNoetherian U := isNoetherian_of_locallyOfFiniteType (U ↘ Spec (.of k))
  have hNV : IsNoetherian V := isNoetherian_of_locallyOfFiniteType (V ↘ Spec (.of k))
  obtain ⟨hFA, hFB, hTU, hTV, hTeU⟩ :=
    generalFieldEtaleCounit_domains p ell hpell k e c n hn hA hB φ
  refine ⟨hNU, hNV, hFA, hFB, hTU, hTV, hTeU,
    generalFieldEtaleSumRealization_exists p ell hpell k e c A n hn hA hFA,
    generalFieldEtaleSumRealization_exists p ell hpell k e c B n hn hB hFB, ?_⟩
  intro DA DB
  refine ⟨generalFieldEtaleSumScalarIso φ e c hFA hFB hTU hTV hTeU DA DB, ?_, ?_⟩
  · intro L
    exact generalFieldEtaleSumScalarIso_normalization φ e c hFA hFB hTU hTV hTeU DA DB L
  · exact generalFieldEtaleSumScalarCompatibility p ell hpell k e c n hn hA hB φ
      hFA hFB hTU hTV hTeU DA DB

end AlgebraicGeometry.ProEtale
