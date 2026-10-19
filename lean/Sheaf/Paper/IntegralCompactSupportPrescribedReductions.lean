/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q131
-/
module

public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Compactification.BoundaryPreparation
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.Paper.CompactSupportFiniteAction
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-!
# Integral compact supports have the prescribed reductions

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
order 2135 (blueprint: lem-coef-integral-compact-support).

The integral value is specified by a Roos triangle of the very tower used in
`sfIntegralCompactSupportValue`. Specifying its projection retains the data needed
for the canonical coefficient maps, which are their tensor/restriction adjoints.
The result applies to every realization of that defining derived limit, including
its chosen value, and imposes no extra condition on the input. Natural index n
always denotes the positive exponent n+1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem coefTor_of_iso {T : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) {a b : ℤ}
    (h : HasProEtaleTorAmplitude T A K a b) : HasProEtaleTorAmplitude T A L a b := by
  refine ⟨h.1, ?_⟩
  intro C P hC f hf hP N i hi
  obtain ⟨eC⟩ := hC
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP N i hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def coefIntrinsicSupportComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfAmbientCompactSupportCandidate A c ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor := by
  let eo : (sfIntrinsicModuleEquivalence X A).functor ⋙ sfIntrinsicExtensionByZero c.i A ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i ⋙
        (sfIntrinsicModuleEquivalence c.Z A).functor :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence X A).unitIso.symm _ ≪≫
      Functor.leftUnitor _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso eo ≪≫ Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefSupport_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      X K) :
    Nonempty ((sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) c).obj K ≅
      (sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) d).obj K) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ
    (Nat.zero_le n))
  let F := (sfIntrinsicDerivedEquivalence X A).functor
  obtain ⟨a, ha⟩ := hK.1.bddBelow
  obtain ⟨b, hb⟩ := hK.1.bddAbove
  have hz (q : ℤ) (hq : q < min a b ∨ max a b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K) := by
    by_contra h
    rcases hq with hq | hq
    · exact (not_lt_of_ge (ha h)) (lt_of_lt_of_le hq (min_le_left _ _))
    · exact (not_lt_of_ge (hb h)) (lt_of_le_of_lt (le_max_right _ _) hq)
  obtain ⟨G₀, ⟨eG⟩⟩ := (finiteRing_constructibleDerived_origin X A).2.2.1 K |>.mpr
    ⟨hK.2, min a b, max a b, min_le_max, hz⟩
  let G := G₀.obj
  have hG : DerivedCategory.TStructure.t.plus G := by
    obtain ⟨r, s, _, hv⟩ := G₀.property.2
    exact ⟨r, (DerivedCategory.isGE_iff G r).mpr (fun i hi ↦ hv i (Or.inl hi))⟩
  let ν :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
  let eK : F.obj (ν.obj G) ≅ K :=
    ((Functor.mapDerivedCategoryCompIso _ _).app G).symm ≪≫ eG
  let comparison (c : Compactification f) :
      (sfAmbientCompactSupportCandidate A c).obj K ≅
        (sfIntrinsicDerivedEquivalence Y A).functor.obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.obj
              ((Etale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj G)) :=
    (sfAmbientCompactSupportCandidate A c).mapIso eK.symm ≪≫
      (coefIntrinsicSupportComparison A c).app (ν.obj G) ≪≫
      (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
        ((ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app ⟨G, hG⟩)
  exact ⟨comparison c ≪≫ (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
          (ULift.{u + 1, u} A) c d).app ⟨G, hG⟩)) ≪≫ (comparison d).symm⟩

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- Countable products for the defining compact-support tower, obtained from the
recorded completed-coefficient derived products, with no extra existence assumption.
Source: blueprint order 2135, Proof paragraph 2; Stacks Tag 07KC
(blueprint: lem-coef-integral-compact-support). -/
noncomputable instance coefCompactSupportHasProduct
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    HasProduct (sfCompactSupportTerm l E c K) := by
  let : HasCountableProducts (DerivedCategory (scalarReductionSource.{u, u} l E Y)) :=
    integralOperationsDerivedCountableProducts l E Y
  infer_instance

/-- The finite-level compact-support transition before restricting to completed
coefficients. Apply the higher-level functor to the actual quotient-induced reduction
map, then the normalized compact-support restriction comparison. Its restriction,
followed by the composite-restriction identification, is `sfCompactSupportTransition`.
Source: blueprint order 2135, Proof paragraph 2
(blueprint: lem-coef-integral-compact-support). -/
noncomputable def coefCompactSupportFiniteTransition
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :=
  (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 2)) c).map
      (sfCompactSupportReductionTransition l E X K n) ≫
    (sfCompactSupportRestriction c
      (Padic.coefficientExtensionTransition l E (n + 1))).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)

/-- The canonical compact-support coefficient comparison: the tensor/restriction
adjoint of the n-th projection of the specified defining Roos triangle. The adjunction
is the recorded one normalized by the tensor unit on K-flat representatives.
No isomorphism or unrelated map is chosen here.
Source: blueprint order 2135, Proof paragraph 2, counit comparison
(blueprint: lem-coef-integral-compact-support). -/
noncomputable def coefIntegralCompactSupportComparison
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E Y n).obj M ⟶
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) :=
  ((derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose.homEquiv M _).symm
    (p ≫ Pi.π _ n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integral compact support is constructible, has its prescribed canonical finite
reductions, and has uniform reduction Tor interval [a,b+2d]. The coefficient comparisons
commute with successive quotient reductions. M, p and delta specify the defining
Roos triangle of Rf_!K, rather than an additional assumption on f or K.
Source: blueprint order 2135, lem-coef-integral-compact-support
(blueprint: lem-coef-integral-compact-support).

Proof:
1. Characteristic p makes l invertible in the fixed base field. The existing integral
compact-support constructibility theorem applies to the specified Roos realization M.
2. Complete identity maps on the two product vertices to a morphism from its triangle
into the chosen limit triangle. Two invertible components make the first component v
invertible, and its first square says v followed by the chosen projection equals p.
Adjunction naturality transports the existing chosen-reduction isomorphisms to M.
3. For the numerical bound, pass to the dense refinement of c. Its ambient scheme is
finite type over the base field and has dimension equal to dim X. Open extension
preserves [a,b], and the finite-coefficient proper direct-image theorem gives [a,b+2d].
4. The finite-ring origin theorem lifts each bounded constructible reduction to etale
coefficients. Transport etale compactification independence through the canonical
realization equivalence and the compact-support site comparison. This carries the bound
back to c; the inverse of the projection adjunct carries it to the reduction of M.
5. The first two arrows of the Roos triangle compose to zero. Projecting the equation
p followed by (1 - shift) equals zero gives the adjacent projection equation. Apply the
higher adjunction to the desired compatibility, use naturality of composite restriction
and the lower adjunction unit formula, and finish with that projection equation.
-/
theorem integralCompactSupport_prescribedReductions
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (_hK : sfIntegralConstructible l E X K)
    (_hTor : ∀ n : ℕ,
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) a b)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n)
    (δ : (∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) ⟶ M⟦(1 : ℤ)⟧)
    (_hc : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) M p δ) :
    sfIntegralConstructible l E Y M ∧
      (∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n)) ∧
      (∀ n : ℕ,
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension.{u, u} l E Y n).obj M) a (b + 2 * (d : ℤ))) ∧
      (∀ n : ℕ,
        coefIntegralCompactSupportComparison l E c K M p (n + 1) ≫
            coefCompactSupportFiniteTransition l E c K n =
          sfCompactSupportReductionTransition l E Y M n ≫
            (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory.map
              (coefIntegralCompactSupportComparison l E c K M p n)) := by
  classical
  have hl : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have hu : IsUnit (l : D.k₀) :=
      (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : l.Prime) _hl.symm).isUnit
    simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)
  have hM : sfIntegralConstructible l E Y M :=
    sfIntegralCompactSupport_constructible l E c D.k hl K _hK M ⟨p, δ, _hc⟩
  let K' : sfIntegralConstructibleCategory l E X := ⟨K, _hK⟩
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K) (sfCompactSupportTransition l E c K)).1
  let N := Classical.choose h
  have hN : IsDerivedLimit (sfCompactSupportTransition l E c K) N :=
    Classical.choose_spec h
  let q := Classical.choose hN
  let ε := Classical.choose hN.choose_spec
  have hN' : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) N q ε :=
    Classical.choose_spec hN.choose_spec
  let T := Pretriangulated.Triangle.mk p (towerTransitionEndomorphism
    (sfCompactSupportTransition l E c K)) δ
  let T' := Pretriangulated.Triangle.mk q (towerTransitionEndomorphism
    (sfCompactSupportTransition l E c K)) ε
  obtain ⟨v, hv, hvδ⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
    T T' _hc hN' (𝟙 _) (𝟙 _) (by simp [T, T'])
  let φ : T ⟶ T' :=
    { hom₁ := v, hom₂ := 𝟙 _, hom₃ := 𝟙 _,
      comm₁ := hv, comm₂ := by simp [T, T'], comm₃ := hvδ }
  have hvIso : IsIso v := Pretriangulated.isIso₁_of_isIso₂₃ φ _hc hN'
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)
  have hvq : v ≫ q = p := by simpa [T, T'] using hv.symm
  have hIso : ∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n) := by
    intro n
    have hn := sfCompactSupportChosenReduction_isIso l D.k hl c E K' n
    have he : coefIntegralCompactSupportComparison l E c K M p n =
        (scalarReductionDerivedExtension l E Y n).map v ≫
          sfCompactSupportChosenReduction l D.k hl c E K' n := by
      change _ = (scalarReductionDerivedExtension l E Y n).map v ≫
        coefIntegralCompactSupportComparison l E c K N q n
      dsimp only [coefIntegralCompactSupportComparison]
      erw [← Adjunction.homEquiv_naturality_left_symm, ← Category.assoc, hvq]
      rfl
    rw [he]
    infer_instance
  refine ⟨hM, hIso, ?_, ?_⟩
  · intro n
    have hn := (_hK.2.choose_spec.choose_spec.2 n).1
    let cd := c.denseRefinement
    let : cd.Z.Over (Spec (.of D.k)) := ⟨cd.g ≫ (Y ↘ Spec (.of D.k))⟩
    have : LocallyOfFiniteType (cd.Z ↘ Spec (.of D.k)) :=
      inferInstanceAs (LocallyOfFiniteType (cd.g ≫ (Y ↘ Spec (.of D.k))))
    have : QuasiCompact (cd.Z ↘ Spec (.of D.k)) :=
      inferInstanceAs (QuasiCompact (cd.g ≫ (Y ↘ Spec (.of D.k))))
    have : cd.g.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    have : cd.i.IsOver (Spec (.of D.k)) := ⟨by
      change cd.i ≫ (cd.g ≫ (Y ↘ Spec (.of D.k))) = _
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g ↦ g ≫ (Y ↘ Spec (.of D.k))) cd.comm.symm).trans (comp_over f _))⟩
    have : QuasiCompact cd.i := cd.quasiCompact_openImmersion ‹_›
    have : IsSchemeTheoreticallyDominant cd.i :=
      c.isSchemeTheoreticallyDominant_denseRefinement_i
    have hdim : topologicalKrullDim cd.Z ≤ (d : WithBot ℕ∞) := by
      rw [← (topologicalKrullDim_fieldExtension_and_denseOpen
        (K := D.k) (X := cd.Z)).2 X cd.i cd.i.denseRange]
      exact _hd
    have hext := finiteStageDerivedExtensionByZero_constructibleFiniteTor D l _hl E
      (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) cd.i
      ((scalarReductionDerivedExtension l E X n).obj K) hn ⟨a, b, _hTor n⟩
    have : LocallyOfFiniteType (Over.mk (cd.Z ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (cd.Z ↘ Spec (.of D.k)))
    have : QuasiCompact (Over.mk (cd.Z ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (QuasiCompact (cd.Z ↘ Spec (.of D.k)))
    have : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
    have : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
    let g : Over.mk (cd.Z ↘ Spec (.of D.k)) ⟶ Over.mk (Y ↘ Spec (.of D.k)) :=
      Over.homMk cd.g (comp_over cd.g (Spec (.of D.k)))
    have : IsSeparated g.left := inferInstanceAs (IsSeparated cd.g)
    have : LocallyOfFiniteType g.left := inferInstanceAs (LocallyOfFiniteType cd.g)
    have : QuasiCompact g.left := inferInstanceAs (QuasiCompact cd.g)
    have hout := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l _hl E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Over.mk (cd.Z ↘ Spec (.of D.k))) (Over.mk (Y ↘ Spec (.of D.k)))
      g d hdim a b hext.1 (hext.2.2 a b (_hTor n))
    obtain ⟨ec⟩ := coefSupport_iso l E n cd c
      ((scalarReductionDerivedExtension l E X n).obj K) hn
    have hbnd := coefTor_of_iso ec hout.2
    have := hIso n
    exact coefTor_of_iso (asIso (coefIntegralCompactSupportComparison l E c K M p n)).symm
      hbnd
  · intro n
    let adj₁ := (derivedScalarExtensionRestrictionAdjunction l E Y (n + 1)).choose
    let adj₀ := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    let e := sfCompactSupportDerivedRestrictionComp l E Y n
    let A₀ := (sfAmbientCompactSupportCandidate
      (Padic.coefficientExtensionRing l E (n + 1)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K)
    have hp : p ≫ Pi.π _ (n + 1) ≫ sfCompactSupportTransition l E c K n =
        p ≫ Pi.π _ n := by
      have hz : p ≫ towerTransitionEndomorphism
          (sfCompactSupportTransition l E c K) = 0 :=
        Pretriangulated.comp_distTriang_mor_zero₁₂ T _hc
      change p ≫ (𝟙 _ - towerProductShift
        (sfCompactSupportTransition l E c K)) = 0 at hz
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hz
      have hn := congrArg (fun z ↦ z ≫ Pi.π (sfCompactSupportTerm l E c K) n) hz
      simpa [towerProductShift, Category.assoc] using hn.symm
    apply (adj₁.homEquiv M _).injective
    change (adj₁.homEquiv M _)
      ((adj₁.homEquiv M _).symm (p ≫ Pi.π _ (n + 1)) ≫ _) =
      (adj₁.homEquiv M _)
        ((adj₁.homEquiv M _).symm
          (adj₀.unit.app M ≫ e.inv.app _) ≫ _)
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have he := e.inv.naturality (coefIntegralCompactSupportComparison l E c K M p n)
    dsimp only [Functor.comp_map] at he
    simp only [Category.assoc]
    erw [← he]
    have hu := adj₀.homEquiv_unit
      (f := coefIntegralCompactSupportComparison l E c K M p n)
    have hu' : p ≫ Pi.π _ n = adj₀.unit.app M ≫
        (scalarReductionDerivedRestriction l E Y n).map
          (coefIntegralCompactSupportComparison l E c K M p n) := by
      simpa only [adj₀, coefIntegralCompactSupportComparison, Equiv.apply_symm_apply] using hu
    have hu'' := congrArg (fun z ↦ z ≫ e.inv.app A₀) hu'
    refine Eq.trans ?_ (by simpa only [Category.assoc] using hu'')
    apply (cancel_mono (e.hom.app A₀)).mp
    simpa [e, A₀, sfCompactSupportTransition, coefCompactSupportFiniteTransition,
      Category.assoc] using hp

end WeilConjectures
