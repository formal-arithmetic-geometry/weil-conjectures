/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnData
import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnTransportComparison
import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnLocalSpectra
import WeilConjectures.ConstructibleSheaf.Devissage
import Mathlib.CategoryTheory.Subobject.MonoOver

/-! # Sheet return and its local weight filtrations

Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152, and (1.2.6), p. 154
(blueprint: lem-zl-constant-extension-return-local-operators).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem returnPureIso
    (D' : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl' : l ≠ D'.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y : Over (Spec (.of D'.k₀))) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (iota : Ω ≃+* ℂ) (w : ℝ)
    {A B : sfCommonStageWeilSheaf D' l hl' Y Ω} (e : A ≅ B)
    (h : SfIsPunctuallyPureOfWeight D' l hl' Ω Y iota A w) :
    SfIsPunctuallyPureOfWeight D' l hl' Ω Y iota B w := by
  intro y α hα
  obtain ⟨L, K, ⟨a⟩, rest⟩ := hα
  exact h y α ⟨L, K, ⟨(ObjectProperty.ι _).mapIso e ≪≫ a⟩, rest⟩

private theorem returnMixedMap
    (D₁ D₂ : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl₁ : l ≠ D₁.p) (hl₂ : l ≠ D₂.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Y₁ : Over (Spec (.of D₁.k₀))) [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom]
    (Y₂ : Over (Spec (.of D₂.k₀))) [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom]
    (iota : Ω ≃+* ℂ)
    (T : sfCommonStageWeilSheaf D₁ l hl₁ Y₁ Ω ⥤ sfCommonStageWeilSheaf D₂ l hl₂ Y₂ Ω)
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (hp : ∀ N w, SfIsPunctuallyPureOfWeight D₁ l hl₁ Ω Y₁ iota N w →
      SfIsPunctuallyPureOfWeight D₂ l hl₂ Ω Y₂ iota (T.obj N) w)
    (N : sfCommonStageWeilSheaf D₁ l hl₁ Y₁ Ω) (w : ℝ)
    (h : SfIsMixedOfWeightsAtMost D₁ l hl₁ Ω Y₁ iota N w) :
    SfIsMixedOfWeightsAtMost D₂ l hl₂ Ω Y₂ iota (T.obj N) w := by
  have : T.Additive := Functor.additive_of_preserves_binary_products T
  obtain ⟨n, G, φ, h0, ⟨last⟩, hm, hq⟩ := h
  refine ⟨n, fun i ↦ T.obj (G i), fun i ↦ T.map (φ i),
    T.map_isZero h0, ⟨T.mapIso last⟩, ?_, ?_⟩
  · intro i
    let := hm i
    infer_instance
  · intro i
    obtain ⟨v, hv, hq⟩ := hq i
    exact ⟨v, hv, returnPureIso D₂ l hl₂ Ω Y₂ iota v
      (PreservesCokernel.iso T (φ i)) (hp _ _ hq)⟩

private theorem returnSubobjects {C : Type a} [Category.{b} C]
    {B : Type c} [Category.{d} B] [Abelian C] [Abelian B]
    (T : C ⥤ B) [T.IsEquivalence] (N : C) :
    ∃ e : Subobject N ≃o Subobject (T.obj N),
      (∀ U, e U = Subobject.mk (T.map U.arrow)) ∧
      (∀ (U V : Subobject N) (h : U ≤ V),
        Nonempty (T.obj (cokernel (Subobject.ofLE U V h)) ≅
          cokernel (Subobject.ofLE (e U) (e V) (e.monotone h)))) := by
  let e := (Subobject.lowerEquivalence (MonoOver.congr (X := N) T.asEquivalence)).toOrderIso
  have he (U : Subobject N) : e U = Subobject.mk (T.map U.arrow) := by
    change (Subobject.lower _).obj U = _
    conv_lhs => rw [← Subobject.thinSkeleton_mk_representative_eq_self U]
    rfl
  refine ⟨e, he, ?_⟩
  intro U V h
  suffices ∀ (U' V' : Subobject (T.obj N)),
      U' = Subobject.mk (T.map U.arrow) → V' = Subobject.mk (T.map V.arrow) →
      ∀ h' : U' ≤ V', Nonempty (T.obj (cokernel (Subobject.ofLE U V h)) ≅
        cokernel (Subobject.ofLE U' V' h')) from
    this (e U) (e V) (he U) (he V) (e.monotone h)
  intro U' V' hU hV h'
  subst U'
  subst V'
  have eqn : T.map U.arrow =
      (𝟙 (T.obj (U : C))) ≫ T.map (Subobject.ofLE U V h) ≫ T.map V.arrow := by
    rw [Category.id_comp, ← T.map_comp, Subobject.ofLE_arrow]
  have q := Subobject.cokernelOfLEMkIso (T.map U.arrow) (T.map V.arrow)
    (Iso.refl _) (T.map (Subobject.ofLE U V h)) eqn h'
  have q' := (PreservesCokernel.iso T (Subobject.ofLE U V h)) ≪≫ q.symm
  exact ⟨q'⟩

/-- Sheet return has the same local operator, ordered transports and pure-weight filtrations.
Source: Deligne, Weil II (1.1.7)--(1.1.10), pp. 150--152, and (1.2.6), p. 154
(blueprint: lem-zl-constant-extension-return-local-operators).

Proof plan, following the eleven DAG steps:
1. Apply sheet-heart coordinates and cyclicReturnExactEquivalence. The return sends a
cycle to its first carrier with the ordered product of its transitions; on arrows it
is restriction to sheet zero. Both categories are the recorded constructible hearts.
2. At a closed point, the tower law gives degree mr over k_0 and r over k_m.
A residue-field basis gives cardinality (q^m)^r=q^(mr).
3. Expand the return Weil map inductively using the normalized compositors. The r
blocks concatenate to the same ordered mr factors, with none interchanged.
4. Apply point_transport_composition on each finite input and each successive pullback.
This identifies the finite block recursion with the actual mr-transition transport.
5. Do the same in the derived category of whole towers using
integralPointTransportTowerPowers. Apply its zeta and nu realization identities,
not merely the separate finite evaluations; no Tor-amplitude hypothesis is used.
6. The canonical stalk comparison identifies the transport, return square and iterated
Weil-map factors separately. Their composites intertwine. All maps are natural.
7. Scalar localization preserves the equations on every rational arrow. The iterated
return scalar calculus gives compatibility with finite extensions, including identities
and towers. Every common-stage object and finite diagram descends to one finite field.
8. Change residue embeddings using localFrobeniusConjugacyClass at that common stage;
compose its conjugacies with the comparison. The new operators are still intertwined.
9. Conjugacy preserves eigenvalues, and both absolute residue sizes are q^(mr).
Hence the punctual-purity equations agree for each real weight, including zero stalks.
10. Exactness preserves adjacent cokernel sequences in any finite subobject filtration;
apply the previous step to its quotients without changing their weight labels.
11. The cyclic-return subobject order isomorphism lifts every finite filtration uniquely.
It preserves zero, total objects and quotients. Repeated terms and length zero are allowed;
m=1 and the empty scheme require no exceptional argument. -/
theorem constantExtensionReturnLocalOperators (iota : Ω ≃+* ℂ) :
    ∃ R : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionSheetSpec D m hm X₀ l hl Ω R ∧
      ∃ hR : PreservesFiniteLimits R,
      PreservesFiniteColimits R ∧
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
        [FiniteDimensional (Padic l) E],
        SheetReturn.TransportLaws D l E hl m ∧
          SheetReturnRationalOperators D m hm X₀ l hl E ∧
          SheetReturnStalkNaturality D m hm X₀ l hl E ∧
          SheetReturnScalarCompatibility D m hm X₀ l hl E) ∧
      @SheetReturnFiltrations.{u, v} D m hm X₀ _ _ _ l _ hl Ω _ _ _ iota R hR ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω) (w : ℝ),
        (SfIsPunctuallyPureOfWeight D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) iota N w ↔
          SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (R.obj N) w)) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω) (w : ℝ),
        SfIsMixedOfWeightsAtMost D l hl Ω (constantExtensionOriginalModel D m hm X₀)
            iota N w ↔
          SfIsMixedOfWeightsAtMost (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota (R.obj N) w) ∧
      (∀ (z : {z : (constantExtensionModel D m hm X₀).left //
          z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
        localClosedPointDegree D (constantExtensionOriginalModel D m hm X₀) z =
          m * localClosedPointDegree (constantExtensionDatum D m hm)
            (constantExtensionModel D m hm X₀) z ∧
        Nat.card ((constantExtensionModel D m hm X₀).left.residueField z.val) =
          D.q ^ (m * localClosedPointDegree (constantExtensionDatum D m hm)
            (constantExtensionModel D m hm X₀) z)) ∧
      (∀ (N : sfCommonStageWeilSheaf D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω)
        (z : {z : (constantExtensionModel D m hm X₀).left //
          z ∈ closedPoints (constantExtensionModel D m hm X₀).left}),
        ConstantExtensionLocalConjugacy D m hm X₀ l hl Ω
          (constantExtensionOriginalModel D m hm X₀) N (R.obj N) z z 1) := by
  obtain ⟨R, hspec, heq⟩ := sheetReturnExactFunctor D m hm X₀ l hl Ω
  let := heq
  have hlim : PreservesFiniteLimits R := inferInstance
  have hcolim : PreservesFiniteColimits R := inferInstance
  have hops (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E] :=
    sheetReturnTransportComparison D m hm X₀ l hl E
  obtain ⟨hspectrum, hdegree, hconj⟩ :=
    sheetReturnLocalSpectra D m hm X₀ l hl Ω R hspec
      (fun E _ _ _ ↦ ⟨(hops E).2.1, (hops E).2.2.2⟩)
  have hp (N : sfCommonStageWeilSheaf D l hl
      (constantExtensionOriginalModel D m hm X₀) Ω) (w : ℝ) :
      SfIsPunctuallyPureOfWeight D l hl Ω
          (constantExtensionOriginalModel D m hm X₀) iota N w ↔
        SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) iota (R.obj N) w := by
    constructor
    · intro h z α hα
      exact h z α ((hspectrum N z α).mpr hα)
    · intro h z α hα
      exact h z α ((hspectrum N z α).mp hα)
  refine ⟨R, hspec, hlim, hcolim, hops, ?_, hp, ?_, hdegree, hconj⟩
  · intro N
    obtain ⟨e, he, hq⟩ := returnSubobjects R N
    refine ⟨e, he, ?_, ?_⟩
    · intro U V h
      obtain ⟨q⟩ := hq U V h
      refine ⟨⟨q⟩, ?_⟩
      intro w
      constructor
      · intro hpure
        exact returnPureIso (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) iota w q ((hp _ w).mp hpure)
      · intro hpure
        exact (hp _ w).mpr
          (returnPureIso (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota w q.symm hpure)
    · intro t
      let eF := (OrderIso.arrowCongr (OrderIso.refl (Fin (t + 1))) e).toEquiv
      refine ⟨eF, (fun _ _ ↦ rfl), ?_⟩
      intro s
      change (s 0 = ⊥ ∧ s (Fin.last t) = ⊤) ↔
        (e (s 0) = ⊥ ∧ e (s (Fin.last t)) = ⊤)
      rw [← e.map_bot, ← e.map_top, e.injective.eq_iff, e.injective.eq_iff]
  · intro N w
    constructor
    · exact returnMixedMap D (constantExtensionDatum D m hm) l hl hl Ω
        (constantExtensionOriginalModel D m hm X₀) (constantExtensionModel D m hm X₀)
        iota R (fun N w ↦ (hp N w).mp) N w
    · intro h
      have hpinv (K : sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω) (v : ℝ)
          (hK : SfIsPunctuallyPureOfWeight (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀) iota K v) :
          SfIsPunctuallyPureOfWeight D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) iota (R.inv.obj K) v :=
        (hp _ v).mpr (returnPureIso (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀) iota v
          (R.asEquivalence.counitIso.app K).symm hK)
      have h' := returnMixedMap (constantExtensionDatum D m hm) D l hl hl Ω
        (constantExtensionModel D m hm X₀) (constantExtensionOriginalModel D m hm X₀)
        iota R.inv hpinv (R.obj N) w h
      obtain ⟨n, G, φ, h0, ⟨last⟩, hm, hq⟩ := h'
      exact ⟨n, G, φ, h0, ⟨last ≪≫ (R.asEquivalence.unitIso.app N).symm⟩, hm, hq⟩

end WeilConjectures
