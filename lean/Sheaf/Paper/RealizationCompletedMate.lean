module

public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.CompletedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.CompletedExchangeUnit
import Sheaf.Paper.IntegralPadicLocalPerfectCriterion
import Sheaf.Paper.CompletedConstructiblePreservation
import Sheaf.Paper.CompletedTargetAugmentationNormalization
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import all Sheaf.Paper.ExtensionZeroPerfectModelTransport

/-! # The ordered completed exchange and the ordinary ambient mate

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15; the strict augmentation
refinement of Stacks Tags 07A7, 0A07 and 0943.
(blueprint: lem-weil-pbc-realization-completed-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem padic_residue_prime_zero
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (l : Padic.coefficientExtensionIntegers l E ⧸
      (pbcPadicCoefficientDatum l E).ideal) = 0 := by
  let H := Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))
  have hm := H.choose_spec.choose_spec.2.1
  have hgen := H.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hl : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  change Ideal.Quotient.mk _ (l : Padic.coefficientExtensionIntegers l E) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change (l : H.choose) ∈ Ideal.span {H.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose}
  rw [hgen]
  exact (hm _).mpr hl

-- These interfaces are used through their comparison lemmas, without unfolding
-- the selected derived functors or the valuation-ring datum during unification.
attribute [local irreducible] pbcPadicCoefficientDatum integralConstantDerived
  cbcDatumOrdinaryTransport pbcActualDerivedPullCompIso
  integralConstantDerivedPullIso

private theorem proper_geometric_dimension_bound
    {S T : Scheme.{u}} (f : S ⟶ T) [IsProper f] [CompactSpace T] :
    ∃ e : ℕ, ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ T),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
  obtain ⟨e, he⟩ := AlgebraicGeometry.exists_fibre_dimension_bound f
  refine ⟨e, ?_⟩
  intro Ω _ y
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω T).symm.surjective y
  calc
    topologicalKrullDim (pullback f (Spec.map a ≫ T.fromSpecResidueField t) : Scheme)
        = topologicalKrullDim
            (pullback (pullback.snd f (T.fromSpecResidueField t)) (Spec.map a) : Scheme) :=
      (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso f
        (T.fromSpecResidueField t) (Spec.map a)).hom.homeomorph.isHomeomorph).symm
    _ = topologicalKrullDim (f.fiber t) := by
      let : (f.fiber t).Over (Spec (T.residueField t)) := ⟨f.fiberToSpecResidueField t⟩
      let : Algebra (T.residueField t) Ω := a.hom.toAlgebra
      let : LocallyOfFiniteType (f.fiber t ↘ Spec (.of (T.residueField t))) := by
        change LocallyOfFiniteType (pullback.snd f (T.fromSpecResidueField t))
        infer_instance
      let : QuasiCompact (f.fiber t ↘ Spec (.of (T.residueField t))) := by
        change QuasiCompact (pullback.snd f (T.fromSpecResidueField t))
        infer_instance
      exact (AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen
        (K := T.residueField t) (X := f.fiber t)).1 Ω
    _ ≤ (e : WithBot ℕ∞) := he t

private theorem prime_global_unit (T : Scheme.{u}) (l : ℕ)
    (hl : ∀ x : T, IsUnit (l : T.presheaf.stalk x)) : IsUnit (l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using hl x

/-- Local perfect models pull back along the base-changed strata and covers. -/
private theorem ordinaryPull_mem
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (hS : ∃ n : ℕ, topologicalKrullDim S ≤ n)
    (hT : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (hlS : IsUnit (l : Γ(S, ⊤))) (hlT : IsUnit (l : Γ(T, ⊤)))
    (h : S ⟶ T) (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K) :
    PbcIsBoundedConstructibleComplete S (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).pull h).obj K) := by
  let d := pbcPadicCoefficientDatum l E
  obtain ⟨s, hs⟩ := (integralPadicLocalPerfectCriterion T l E hT hlT K).mp hK
  let s' : FiniteLocallyClosedStratification S := {
    n := s.n
    stratum := fun i ↦ h.base ⁻¹' s.stratum i
    isLocallyClosed_stratum := fun i ↦ (s.isLocallyClosed_stratum i).preimage h.continuous
    iUnion_stratum_eq_univ := by
      rw [← Set.preimage_iUnion, s.iUnion_stratum_eq_univ, Set.preimage_univ]
    pairwise_disjoint_stratum := fun _ _ hij ↦
      (s.pairwise_disjoint_stratum hij).preimage _
    domain := fun i ↦ pullback (s.immersion i) h
    immersion := fun i ↦ pullback.snd (s.immersion i) h
    isImmersion := fun i ↦ by
      let := s.isImmersion i
      infer_instance
    range_immersion := fun i ↦ by rw [Pullback.range_snd, s.range_immersion] }
  apply (integralPadicLocalPerfectCriterion S l E hS hlS _).mpr
  refine ⟨s', fun i ↦ ?_⟩
  obtain ⟨V, hV, hmodels⟩ := hs i
  let v : s'.domain i ⟶ s.domain i := pullback.fst (s.immersion i) h
  let F := proEtaleBaseChange v
  let e : F.obj (⊤_ (s.domain i).ProEt) ≅ ⊤_ (s'.domain i).ProEt :=
    (isLimitOfHasTerminalOfPreservesLimit F).uniqueUpToIso terminalIsTerminal
  refine ⟨(V.functorPushforward F).pullback e.inv,
    (ProEt.topology _).pullback_stable e.inv
      ((proEtaleBaseChangeCoverPreserving v).cover_preserve hV), ?_⟩
  intro W a ha
  obtain ⟨U, q, b, hq, _⟩ := ha
  obtain ⟨P, c, t, hc, ht, hfin, ⟨em⟩⟩ := hmodels U q hq
  refine ⟨P, c, t, hc, ht, hfin, ⟨?_⟩⟩
  let z : W.left ⟶ U.left := b.left ≫ pullback.fst U.hom v
  have hb : b.left ≫ pullback.snd U.hom v = W.hom := b.w
  have hz : (W.hom ≫ s'.immersion i) ≫ h = z ≫ (U.hom ≫ s.immersion i) := by
    calc
      (W.hom ≫ s'.immersion i) ≫ h = W.hom ≫ (v ≫ s.immersion i) := by
        rw [Category.assoc]
        exact congrArg (fun m ↦ W.hom ≫ m) pullback.condition.symm
      _ = (b.left ≫ pullback.snd U.hom v) ≫ (v ≫ s.immersion i) := by rw [hb]
      _ = z ≫ (U.hom ≫ s.immersion i) := by
        dsimp only [z]
        simp only [Category.assoc, pullback.condition_assoc]
  exact ((pbcActualDerivedPull (W.hom ≫ s'.immersion i) d).mapIso
      ((cbcDatumOrdinaryTransport d h).symm.app K)) ≪≫
    ((pbcActualDerivedPullCompIso (W.hom ≫ s'.immersion i) h d).symm.app K) ≪≫
    eqToIso (congrArg (fun m ↦ (pbcActualDerivedPull m d).obj K) hz) ≪≫
    ((pbcActualDerivedPullCompIso z (U.hom ≫ s.immersion i) d).app K) ≪≫
    (pbcActualDerivedPull z d).mapIso em ≪≫
    ((cbcDatumOrdinaryTransport d z).app _) ≪≫
    ((integralConstantDerivedPullIso d z).app _)

/-- The specified unit is invertible if its ordinary pullback is complete. -/
private theorem unit_isIso_of_mem
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {S T : Scheme.{u}} (h : S ⟶ T) (K : d.derived T)
    (hK : PbcIsBoundedConstructibleComplete T d K)
    (hP : PbcIsBoundedConstructibleComplete S d ((d.pull h).obj K)) :
    IsIso (d.ordinaryToCompleted h K) := by
  have hC := pbcIntrinsicComplete_towerComplete d S _ hP.1
  have he := (completedTargetAugmentationNormalization d h (𝟙 S) K
    (pbcIntrinsicComplete_towerComplete d T K hK.1)).1
  have : IsIso (d.ordinaryToCompleted h K ≫
      (completedRlim S (d.completedRing S)).map
        ((d.reductionTowerPullbackIso h).hom.app K)) := by
    rw [he]
    exact hC
  exact IsIso.of_isIso_comp_right (d.ordinaryToCompleted h K)
    ((completedRlim S (d.completedRing S)).map
      ((d.reductionTowerPullbackIso h).hom.app K))

private theorem padic_unit_isIso
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (hS : ∃ n : ℕ, topologicalKrullDim S ≤ n)
    (hT : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (hlS : IsUnit (l : Γ(S, ⊤))) (hlT : IsUnit (l : Γ(T, ⊤)))
    (h : S ⟶ T) (K : PbcCompletedDerived T (pbcPadicCoefficientDatum l E))
    (hK : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) K) :
    IsIso ((pbcPadicCoefficientDatum l E).ordinaryToCompleted h K) :=
  unit_isIso_of_mem (pbcPadicCoefficientDatum l E) h K hK
    (ordinaryPull_mem l E hS hT hlS hlT h K hK)

private theorem properPush_mem
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hX' : ∃ n : ℕ, topologicalKrullDim X' ≤ n)
    (hY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ n)
    (hlX : IsUnit (l : Γ(X, ⊤))) (hlY : IsUnit (l : Γ(Y, ⊤)))
    (hlX' : IsUnit (l : Γ(X', ⊤))) (hlY' : IsUnit (l : Γ(Y', ⊤)))
    [IsProper f] (K : PbcCompletedDerived X (pbcPadicCoefficientDatum l E))
    (hK : PbcIsBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E) K) :
    PbcIsBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).push f).obj K) := by
  let : IsProper f' := by
    rw [← sq.hom_snd]
    infer_instance
  obtain ⟨e, he⟩ := proper_geometric_dimension_bound f
  exact ((pbcPadicCoefficientDatum l E).constructible_preservation sq hX hY hX' hY'
    l (Fact.out : l.Prime).pos (padic_residue_prime_zero l E) hlX hlY hlX' hlY'
    e (fun Ω _ _ y ↦ he Ω y) K hK).1

attribute [local irreducible] AdicCoefficientDatum.ordinaryToCompleted
  AdicCoefficientDatum.completedExchange

private theorem exchange_conjugation
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    (K : d.derived X)
    [IsIso (d.ordinaryToCompleted g ((d.push f).obj K))]
    [IsIso (d.ordinaryToCompleted g' K)] :
    ∃ (γ : (d.pull g).obj
          ((d.push f).obj K) ≅
        (d.completedPull g).obj
          ((d.push f).obj K))
      (γ' : (d.pull g').obj K ≅
        (d.completedPull g').obj K),
      γ.hom = d.ordinaryToCompleted g
          ((d.push f).obj K) ∧
      γ'.hom = d.ordinaryToCompleted g' K ∧
      d.completedExchange sq K =
        γ.inv ≫ (d.integralExchange sq).app K ≫
          (d.push f').map γ'.hom := by
  refine ⟨asIso (d.ordinaryToCompleted g ((d.push f).obj K)),
    asIso (d.ordinaryToCompleted g' K), rfl, rfl, ?_⟩
  apply (cancel_epi (d.ordinaryToCompleted g ((d.push f).obj K))).1
  simpa only [asIso_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc] using
    d.completedExchange_unit sq K

/-- The two specified completion units are invertible, and their conjugate of the
ordinary unit-square-counit mate is precisely the ordered strict-tower exchange.
The existential isomorphisms below have their homs fixed to the actual units;
no exchange map is asserted invertible.
Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15, with the strict
augmentation comparison of Stacks Tags 07A7, 0A07, 0943 and Equation 0B56
(blueprint: lem-weil-pbc-realization-completed-mate).
Proof:
1. The prime lies in the uniformizer ideal. Global units follow from the stalkwise
   hypotheses. Proper base change of f and the geometric fibre dimension bound
   allow actual-coefficient constructible preservation to give Rf_*K in the category.
2. Pull back the finite strata and the covering sieves of the actual local perfect
   criterion. Composition of ordinary pullbacks and constant-model transport give
   the same bounded finite-projective scalar complex on every new chart. Thus the
   ordinary pullbacks of K and Rf_*K remain in the category.
3. Intrinsic completeness gives tower completeness. The first target-augmentation
   identity identifies each specified unit, followed by an isomorphism, with the
   completion unit of the ordinary pullback. Hence the specified units are invertible.
4. The generic completed-exchange-unit identity fixes exchange composed with the
   source unit. Cancel that unit to obtain the required ordered conjugation. -/
theorem realizationCompletedMate
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y X' Y' : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    [IsNoetherian X.left] [IsNoetherian Y.left]
    [IsNoetherian X'.left] [IsNoetherian Y'.left]
    (_hXdim : ∃ n : ℕ, topologicalKrullDim X.left ≤ n)
    (_hYdim : ∃ n : ℕ, topologicalKrullDim Y.left ≤ n)
    (_hX'dim : ∃ n : ℕ, topologicalKrullDim X'.left ≤ n)
    (_hY'dim : ∃ n : ℕ, topologicalKrullDim Y'.left ≤ n)
    (_hXinv : ∀ x : X.left, IsUnit (l : X.left.presheaf.stalk x))
    (_hYinv : ∀ x : Y.left, IsUnit (l : Y.left.presheaf.stalk x))
    (_hX'inv : ∀ x : X'.left, IsUnit (l : X'.left.presheaf.stalk x))
    (_hY'inv : ∀ x : Y'.left, IsUnit (l : Y'.left.presheaf.stalk x))
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (sq : ChosenCartesianSquare g'.left f'.left f.left g.left) [IsProper f.left]
    (K : PbcBoundedConstructibleComplete X.left (pbcPadicCoefficientDatum l E)) :
    ∃ (γ : ((pbcPadicCoefficientDatum l E).pull g.left).obj
          (((pbcPadicCoefficientDatum l E).push f.left).obj K.obj) ≅
        ((pbcPadicCoefficientDatum l E).completedPull g.left).obj
          (((pbcPadicCoefficientDatum l E).push f.left).obj K.obj))
      (γ' : ((pbcPadicCoefficientDatum l E).pull g'.left).obj K.obj ≅
        ((pbcPadicCoefficientDatum l E).completedPull g'.left).obj K.obj),
      γ.hom = (pbcPadicCoefficientDatum l E).ordinaryToCompleted g.left
          (((pbcPadicCoefficientDatum l E).push f.left).obj K.obj) ∧
      γ'.hom = (pbcPadicCoefficientDatum l E).ordinaryToCompleted g'.left K.obj ∧
      (pbcPadicCoefficientDatum l E).completedExchange sq K.obj =
        γ.inv ≫ ((pbcPadicCoefficientDatum l E).integralExchange sq).app K.obj ≫
          ((pbcPadicCoefficientDatum l E).push f'.left).map γ'.hom := by
  let d := pbcPadicCoefficientDatum l E
  have hX := prime_global_unit X.left l _hXinv
  have hY := prime_global_unit Y.left l _hYinv
  have hX' := prime_global_unit X'.left l _hX'inv
  have hY' := prime_global_unit Y'.left l _hY'inv
  have hC := properPush_mem l E sq _hXdim _hYdim _hX'dim _hY'dim
    hX hY hX' hY' K.obj K.property
  have : IsIso (d.ordinaryToCompleted g.left ((d.push f.left).obj K.obj)) :=
    padic_unit_isIso l E _hY'dim _hYdim hY' hY g.left _ hC
  have : IsIso (d.ordinaryToCompleted g'.left K.obj) :=
    padic_unit_isIso l E _hX'dim _hXdim hX' hX g'.left K.obj K.property
  exact exchange_conjugation d sq K.obj

end AlgebraicGeometry.Scheme
