/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.SbcCompletedOperations
public import WeilConjectures.AlgebraicGeometry.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.AdicSmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.ExchangeFunctoriality
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.CompleteProetale
import all WeilConjectures.AlgebraicGeometry.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.SfBaseChangeGeometryHypotheses
import WeilConjectures.AlgebraicGeometry.CompletedConstructiblePreservation
import WeilConjectures.AlgebraicGeometry.PbcUniformCompleteTriangulated
import Mathlib.GroupTheory.PGroup
import WeilConjectures.AlgebraicGeometry.SfCompletedExchangeTransport

/-! # Completed ordinary exchange and its constructible domain

Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package,
clause (4); Stacks Tags 09C9, 09AL, 099N and 0EYU
(blueprint: lem-sf-bc-completed-mate-domain).

The exchange is the published unit/comparison/counit mate. Its ordered strict-limit
realization is compared using the canonical resolving-counit transports. Positive
quotient level n+1 is represented by n : ℕ throughout.

The finite-cohomology, completed-presentation transport and chosen-square transpose
are the existing constructions recorded by def-sf-adic-finite-cohomology,
def-sf-completed-pullback-presentation-transport and
def-sf-chosen-cartesian-square-transpose, respectively.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local instance 2000]
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

/-- The direct-image presentation comparison comes from equality of the completed
coefficient structure maps, fixed by every finite quotient projection.
Source: clause (4), canonical direct-image comparison; Stacks 099N
(blueprint: lem-sf-bc-completed-mate-domain). -/
def sfCompletedMatePushComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {V W : Scheme.{u}} (f : V ⟶ W) :
    sbcAmbientPush l E f ≅ (pbcIntegralDatum l E).push f :=
  eqToIso (congrArg (proEtaleRingDerivedDirectImage f
    (pbcAdicCompletion W (pbcIntegralDatum l E))
    (pbcAdicCompletion V (pbcIntegralDatum l E)))
    (Iso.ext (cbcDatumCoefficient_eq (pbcIntegralDatum l E) f)))

/-- Constructible cohomology in a specified interval, in the canonical finite
constant-coefficient presentation. No bound or constructibility assumption is built in.
Source: clause (4), the four finite outputs in the smooth landing clause; Stacks 09AJ
(blueprint: lem-sf-bc-completed-mate-domain). -/
def sfCompletedFiniteProfile (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u}) (n : ℕ)
    (J : @DerivedCategory
      (AlgebraicGeometry.Scheme.pbcModules W
        ((pbcAdicRings W (pbcIntegralDatum l E)).obj (op n))) _ _
      (HasDerivedCategory.standard _)) (a b : ℤ) : Prop :=
  ∀ i : ℤ,
    IsConstructibleProEtaleCoefficientModuleSheaf W
      (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
      (sbcAdicFiniteCohomology l E W n J i) ∧
    ((i < a ∨ b < i) → IsZero (sbcAdicFiniteCohomology l E W n J i))

private theorem sfIntegralPrime_mem (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (l : PbcIntegralRing l E) ∈ (pbcIntegralDatum l E).ideal := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Ideal.span {Padic.coefficientExtensionUniformizer l E} := by
    rw [hgen]
    apply (h.2.1 _).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  change (l : PbcIntegralRing l E) ∈ Ideal.span {pbcUniformizer l E}
  rw [Ideal.mem_span_singleton] at hm ⊢
  exact map_dvd ULift.ringEquiv.symm hm

private theorem sfQuotientOrderUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {R : Type*} [CommRing R] (hl : IsUnit (l : R)) (n : ℕ) :
    IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : R) := by
  let Q := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
  have hz : (l : Q) ^ (n + 1) = 0 := by
    change (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1))
      (l : PbcIntegralRing l E)) ^ (n + 1) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (sfIntegralPrime_mem l E) (n + 1)
  have hp : IsPGroup l (Multiplicative Q) := by
    intro x
    refine ⟨n + 1, ?_⟩
    change (l ^ (n + 1)) • Multiplicative.toAdd x = 0
    rw [nsmul_eq_mul, Nat.cast_pow, hz, zero_mul]
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcard : Nat.card Q = l ^ k := hk
  rw [hcard, Nat.cast_pow]
  exact hl.pow k

private theorem sfBoundedOrigins (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X] (K : PbcIntegralConstructible l E X) (n : ℕ) :
    ∃ L : Etale.BoundedConstructibleDerivedCategory
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) X,
      Nonempty ((pbcDerivedFunctionRealization X (pbcIntegralDatum l E) n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
          X).mapDerivedCategory.obj L.obj) ≅ (sbcReduction l E X n).obj K.obj) := by
  let d := pbcIntegralDatum l E
  have hp := (pbcUniformReductionCriterion l E X K.obj).mp
    ⟨K.property.2.1, K.property.2.2⟩
  have hlevel := (uniformProfile_localEffectivity X d K.obj hp).1 n
  obtain ⟨C, hC, ⟨eC⟩⟩ := hlevel
  obtain ⟨L, hL, ⟨eL⟩⟩ := hC
  have hLP : Etale.DerivedCategory.isBoundedConstructible (ProEtale.PbcQuotient d n) X L := by
    refine ⟨?_, hL.2⟩
    intro i
    obtain ⟨S, _, hS⟩ := hL.1 i
    exact ⟨S, hS⟩
  let R := ProEtale.finiteCoefficientRealization X (ProEtale.PbcQuotient d n)
  let G : ProEtale.FiniteCoefficientModules X (ProEtale.PbcQuotient d n) ⥤
      pbcModules X ((pbcAdicRings X d).obj (op n)) :=
    SheafOfModules.restrictScalars.{u + 1}
    (AdicCoefficients.finiteRingComparison X (ProEtale.PbcQuotient d n)).hom
  let U := SheafOfModules.toSheaf
    ((adicLisseForget X).obj ((pbcAdicRings X d).obj (op n)))
  have : PreservesFiniteLimits (G ⋙ U) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf (ProEtale.finiteCoefficientRingSheaf X
        (ProEtale.PbcQuotient d n))))
  have : PreservesFiniteColimits (G ⋙ U) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf (ProEtale.finiteCoefficientRingSheaf X
        (ProEtale.PbcQuotient d n))))
  have : PreservesFiniteLimits G := preservesFiniteLimits_of_reflects_of_preserves G U
  have : PreservesFiniteColimits G := preservesFiniteColimits_of_reflects_of_preserves G U
  let := pbcFunctionRealization_additive X d n
  let := pbcFunctionRealization_limits X d n
  let := pbcFunctionRealization_colimits X d n
  let c : R.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      pbcDerivedFunctionRealization X d n :=
    (Functor.mapDerivedCategoryCompIso R G).symm ≪≫
      Functor.mapDerivedCategoryNatIso (functionRealizationComparison.{u} X d n)
  let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ProEtale.PbcQuotient d n)) X
  refine ⟨⟨L, hLP⟩, ⟨?_⟩⟩
  exact (c.app (F.mapDerivedCategory.obj L)).symm ≪≫
    G.mapDerivedCategory.mapIso ((Functor.mapDerivedCategoryCompIso F R).app L).symm ≪≫
    G.mapDerivedCategory.mapIso eL ≪≫ G.mapDerivedCategoryFactors.app C ≪≫ eC

/-- Proper and smooth base change for the specified completed ordinary mate, with
its canonical finite-reduction and ordered derived-limit normalizations, and the
precise constructible landing clauses.
Source: blueprint sec-six-functors/sk-thm-sf-package, prop-functor-package, clause (4);
Stacks 09C9, 09AL, 099N and 0EYU
(blueprint: lem-sf-bc-completed-mate-domain).

Proof:
1. The package geometry theorem gives Noetherian corners, dimensions, prime units,
   proper base change and one geometric fibre bound. The coefficient prime lies in
   the uniformizer ideal; every finite quotient has prime-power order.
2. The existing completed-operation theorem supplies the finite-reduction and strict
   derived-limit equations. sfCompletedExchange_transport is the separate canonical
   comparison with the ordered proper-base-change presentation.
3. Complete pro-etale proper base change makes that ordered arrow invertible.
   Rewriting by step 2 gives invertibility of the specified completed mate.
4. Apply actual-coefficient constructible preservation to the same published datum.
   Transport membership along the canonical source and target comparisons. The full
   subcategory reflects invertibility of the same arrow.
5. The uniform cohomological criterion and its normalized local-effectivity argument
   supply bounded constructible etale sources. The exact realization and its canonical
   scalar-presentation comparison identify their images with the canonical reductions.
6. Apply adic smooth base change on the transposed square. The given four finite
   profiles give exactly its optional common-interval hypothesis by rearranging the
   universal quantifiers; its conclusion retains the same full-subcategory arrow.
-/
theorem sfCompletedMateDomain
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hlp : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y X' Y' : Scheme.{u}}
    (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    (aX' : X' ⟶ Spec (.of D.k)) (aY' : Y' ⟶ Spec (.of D.k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [IsSeparated aX'] [LocallyOfFiniteType aX'] [QuasiCompact aX']
    [IsSeparated aY'] [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (_hf : f ≫ aY = aX) (_hg : g ≫ aY = aY')
    (_hg' : g' ≫ aX = aX') (_hf' : f' ≫ aY' = aX')
    (sq : ChosenCartesianSquare g' f' f g) :
    (IsProper f → ∀ K : PbcComplete l E X,
      PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum l E) K.obj →
      IsIso (sbcExchangeApp l E (exchangeTransposeSquare sq) K) ∧
      (∀ n : ℕ,
        (sbcReduction l E Y' n).map (sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom ≫
            sbcPushReduction l E f' n ((sbcPull l E g').obj K) ≫
            (sbcFinitePush l E f' n).map (sbcPullReduction l E g' n K) =
          sbcPullReduction l E g n ((sbcPush l E f).obj K) ≫
            (sbcFinitePull l E g n).map (sbcPushReduction l E f n K) ≫
            sbcFiniteExchangeApp l E (exchangeTransposeSquare sq) n
              ((sbcReduction l E X n).obj K.obj)) ∧
      ((sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom =
        (sbcStrictSourceComparison l E (exchangeTransposeSquare sq) K).hom ≫
          (completedTowerRlim (pbcIntegralDatum l E) Y').map
            (sbcStrictExchange l E (exchangeTransposeSquare sq) K) ≫
          (sbcStrictTargetComparison l E (exchangeTransposeSquare sq) K).hom) ∧
      ((sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom =
        (cbcDatumCompletedTransport (pbcIntegralDatum l E) g).hom.app
            ((sbcPush l E f).obj K).obj ≫
          ((pbcIntegralDatum l E).completedPull g).map
            ((sfCompletedMatePushComparison l E f).hom.app K.obj) ≫
          (pbcIntegralDatum l E).completedExchange sq K.obj ≫
          ((pbcIntegralDatum l E).push f').map
            ((cbcDatumCompletedTransport (pbcIntegralDatum l E) g').inv.app K.obj) ≫
          (sfCompletedMatePushComparison l E f').inv.app ((sbcPull l E g').obj K).obj) ∧
      (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) K.obj →
        ∃ (hS : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
          ((sbcPull l E g).obj ((sbcPush l E f).obj K)).obj)
        (hT : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
          ((sbcPush l E f').obj ((sbcPull l E g').obj K)).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E))
          (X := ⟨((sbcPull l E g).obj ((sbcPush l E f).obj K)).obj, hS⟩)
          (Y := ⟨((sbcPush l E f').obj ((sbcPull l E g').obj K)).obj, hT⟩)
          (sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom))) ∧
    (Smooth g → ∀ K : PbcIntegralConstructible l E X,
      (∀ n : ℕ, ∃ L : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) X,
        Nonempty ((pbcDerivedFunctionRealization X (pbcIntegralDatum l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
            X).mapDerivedCategory.obj L.obj) ≅ (sbcReduction l E X n).obj K.obj)) ∧
      IsIso (sbcExchangeApp l E (exchangeTransposeSquare sq)
        ((pbcConstructibleInclusion l E X).obj K)) ∧
      ((∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ,
        sfCompletedFiniteProfile l E Y n
          ((sbcFinitePush l E f n).obj ((sbcReduction l E X n).obj K.obj)) a b ∧
        sfCompletedFiniteProfile l E Y' n
          ((sbcFinitePull l E g n).obj
            ((sbcFinitePush l E f n).obj ((sbcReduction l E X n).obj K.obj))) a b ∧
        sfCompletedFiniteProfile l E X' n
          ((sbcFinitePull l E g' n).obj ((sbcReduction l E X n).obj K.obj)) a b ∧
        sfCompletedFiniteProfile l E Y' n
          ((sbcFinitePush l E f' n).obj
            ((sbcFinitePull l E g' n).obj ((sbcReduction l E X n).obj K.obj))) a b) →
        ∃ (hS : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
          ((sbcPull l E g).obj ((sbcPush l E f).obj ((pbcConstructibleInclusion l E X).obj K))).obj)
        (hT : PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E)
          ((sbcPush l E f').obj
            ((sbcPull l E g').obj ((pbcConstructibleInclusion l E X).obj K))).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete Y' (pbcIntegralDatum l E))
          (X := ⟨((sbcPull l E g).obj
            ((sbcPush l E f).obj ((pbcConstructibleInclusion l E X).obj K))).obj, hS⟩)
          (Y := ⟨((sbcPush l E f').obj
            ((sbcPull l E g').obj ((pbcConstructibleInclusion l E X).obj K))).obj, hT⟩)
          (sbcExchangeApp l E (exchangeTransposeSquare sq)
            ((pbcConstructibleInclusion l E X).obj K)).hom))) := by
  classical
  let d := pbcIntegralDatum l E
  let : X.Over (Spec (.of D.k)) := ⟨aX⟩
  let : Y.Over (Spec (.of D.k)) := ⟨aY⟩
  let : X'.Over (Spec (.of D.k)) := ⟨aX'⟩
  let : Y'.Over (Spec (.of D.k)) := ⟨aY'⟩
  have : IsSeparated (X ↘ Spec (.of D.k)) := by
    change IsSeparated aX
    infer_instance
  have : LocallyOfFiniteType (X ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType aX
    infer_instance
  have : QuasiCompact (X ↘ Spec (.of D.k)) := by
    change QuasiCompact aX
    infer_instance
  have : IsSeparated (Y ↘ Spec (.of D.k)) := by
    change IsSeparated aY
    infer_instance
  have : LocallyOfFiniteType (Y ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType aY
    infer_instance
  have : QuasiCompact (Y ↘ Spec (.of D.k)) := by
    change QuasiCompact aY
    infer_instance
  have : IsSeparated (X' ↘ Spec (.of D.k)) := by
    change IsSeparated aX'
    infer_instance
  have : LocallyOfFiniteType (X' ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType aX'
    infer_instance
  have : QuasiCompact (X' ↘ Spec (.of D.k)) := by
    change QuasiCompact aX'
    infer_instance
  have : IsSeparated (Y' ↘ Spec (.of D.k)) := by
    change IsSeparated aY'
    infer_instance
  have : LocallyOfFiniteType (Y' ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType aY'
    infer_instance
  have : QuasiCompact (Y' ↘ Spec (.of D.k)) := by
    change QuasiCompact aY'
    infer_instance
  have : f.IsOver (Spec (.of D.k)) := ⟨_hf⟩
  have : g.IsOver (Spec (.of D.k)) := ⟨_hg⟩
  have : g'.IsOver (Spec (.of D.k)) := ⟨_hg'⟩
  have : f'.IsOver (Spec (.of D.k)) := ⟨_hf'⟩
  have hgeom := sf_baseChange_geometry_hypotheses D l (Fact.out : l.Prime) _hlp
    (X := X) (Y := Y) (X' := X') (Y' := Y') g' f' f g sq
  have hX := hgeom.1 X (.inl rfl)
  have hY := hgeom.1 Y (.inr (.inl rfl))
  have hX' := hgeom.1 X' (.inr (.inr (.inl rfl)))
  have hY' := hgeom.1 Y' (.inr (.inr (.inr rfl)))
  have : IsNoetherian X := hX.1
  have : IsNoetherian Y := hY.1
  have : IsNoetherian X' := hX'.1
  have : IsNoetherian Y' := hY'.1
  have hu (W : Scheme.{u}) (h : ∀ w : W, IsUnit (l : W.presheaf.stalk w)) :
      IsUnit (l : Γ(W, ⊤)) := by
    apply W.toRingedSpace.isUnit_of_isUnit_germ
    intro w _
    simpa only [map_natCast] using h w
  have hlX := hu X hX.2.2.2.2
  have hlY := hu Y hY.2.2.2.2
  have hlX' := hu X' hX'.2.2.2.2
  have hlY' := hu Y' hY'.2.2.2.2
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (PbcIsBoundedConstructibleComplete Y' d) :=
    (pbcIntegralUniformComplete_isTriangulated l E Y' hY'.2.2.2.1 hY'.2.2.2.2).1
  have hmap (K : PbcComplete l E X) := sfCompletedExchange_transport l E sq K
  constructor
  · intro hf K horigin
    have : IsProper f := hf
    have : IsProper f' := hgeom.2.2.2.2.2.2.1 hf
    have hproper : IsIso (d.completedExchange sq K.obj) :=
      completeProetale_isIso d sq K.obj K.property horigin
    have hiso : IsIso (sbcExchangeApp l E (exchangeTransposeSquare sq) K).hom := by
      rw [hmap K]
      infer_instance
    have hiso' : IsIso (sbcExchangeApp l E (exchangeTransposeSquare sq) K) :=
      (ObjectProperty.isIso_hom_iff _).1 hiso
    refine ⟨hiso', fun n ↦ sbcCompletedOperations_linear_natural_exchange l E
      (exchangeTransposeSquare sq) K n,
      sbcCompletedExchange_strictLimit l E (exchangeTransposeSquare sq) K, hmap K, ?_⟩
    intro hK
    obtain ⟨e, he⟩ := hgeom.2.2.2.2.2.1
    have hp := d.constructible_preservation sq hX.2.2.2.1 hY.2.2.2.1
      hX'.2.2.2.1 hY'.2.2.2.1 l (Fact.out : l.Prime).pos
      ((Ideal.Quotient.eq_zero_iff_mem).2 (sfIntegralPrime_mem l E))
      hlX hlY hlX' hlY' e (fun Ω _ _ y ↦ (he Ω y).1) K.obj hK
    let sourceIso := ((cbcDatumCompletedTransport d g).app
        ((sbcPush l E f).obj K).obj) ≪≫
      (d.completedPull g).mapIso ((sfCompletedMatePushComparison l E f).app K.obj)
    let targetIso := (d.push f').mapIso ((cbcDatumCompletedTransport d g').app K.obj).symm ≪≫
      ((sfCompletedMatePushComparison l E f').app ((sbcPull l E g').obj K).obj).symm
    have hS := ObjectProperty.prop_of_iso _ sourceIso.symm hp.2.1
    have hT := ObjectProperty.prop_of_iso _ targetIso hp.2.2.2
    refine ⟨hS, hT, ?_⟩
    exact (ObjectProperty.isIso_hom_iff _).1 hiso
  · intro hg K
    have : Smooth g := hg
    have : QuasiSeparated f := inferInstance
    have horigin := sfBoundedOrigins l E X K
    have hs := adicSmoothBaseChange l E (exchangeTransposeSquare sq)
      hX.2.2.2.1 hlY (fun n ↦
        ⟨sfQuotientOrderUnit l E hlY n, sfQuotientOrderUnit l E hlY' n,
          sfQuotientOrderUnit l E hlX n, sfQuotientOrderUnit l E hlX' n⟩) K horigin
    refine ⟨horigin, hs.1, ?_⟩
    rintro ⟨a, b, hab, hprofile⟩
    apply hs.2 hY'.2.2.2.1
    exact ⟨a, b, hab, fun n i ↦
      ⟨(hprofile n).1 i, (hprofile n).2.1 i,
        (hprofile n).2.2.1 i, (hprofile n).2.2.2 i⟩⟩

end WeilConjectures
