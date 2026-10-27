/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.IntegralPullbackStrictRoosNormalization
public import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.IntegralRoosChainRepresentatives
import Sheaf.Paper.IntegralRoosResolvingCounits
import Sheaf.Paper.IntegralRoosAugmentationLocalization
import Sheaf.Paper.IntegralRoosCompletionIsomorphisms

/-! # Derived interpretation of the integral quotient Roos augmentation

Source: main-20261015, det-lem-int-tensor-pullback, first paragraph and
Comparison with the Stacks Project; Stacks proetale.tex, Tags 099M and 099N (2),(5).
(blueprint: lem-sfb-integral-roos-derived-pullback-unit).

The strict towers, quotient augmentations and normalized cone coordinates are reused
from their existing owning module. Index n is the positive quotient exponent n+1.
The two completion isomorphisms are natural on the full category of flat-term
K-flat representatives, and their target categories retain the distinct coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] CategoryTheory.catToReflQuiver
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.pbcIntegralDatum AlgebraicGeometry.Scheme.completedAdicChangeData

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralPullbackStrictRoos
attribute [local irreducible] completedModulePullback completedReductionModuleTowerFunctor
  OrderedExchange.reductionModule OrderedExchange.reductionData OrderedExchange.reduction


-- Keep the dependent logical assembly abstract to avoid expanding concrete functors
-- repeatedly while the kernel checks the existential eliminations.
private theorem assembleRoos
    {D A E AT AU AV EP KR JR KC JC ER EC P : Type*}
    {W1 W2 W3 W4 W5 W6 W7 W8 : D → A → E → AT → AU → AV → EP → KR → JR → KC → JC → Prop}
    {N : D → A → E → AV → KC → Prop} {Q : P → Prop}
    {I1 I2 I3 I4 I5 I6 I7 : P → Prop}
    {UR : AU → ER → ∀ p, Q p → Prop}
    {UC : AV → EC → ∀ p, Q p → Prop}
    {T : AT → KR → ∀ p, Q p → Prop}
    (chain : ∃ d a e alpha_t au av ep kr jr kc jc, W1 d a e alpha_t au av ep kr jr kc jc ∧
      W2 d a e alpha_t au av ep kr jr kc jc ∧
      W3 d a e alpha_t au av ep kr jr kc jc ∧
      W4 d a e alpha_t au av ep kr jr kc jc ∧
      W5 d a e alpha_t au av ep kr jr kc jc ∧
      W6 d a e alpha_t au av ep kr jr kc jc ∧
      W7 d a e alpha_t au av ep kr jr kc jc ∧
      W8 d a e alpha_t au av ep kr jr kc jc)
    (localize : ∀ d a e alpha_t au av ep kr jr kc jc, W1 d a e alpha_t au av ep kr jr kc jc ∧
      W2 d a e alpha_t au av ep kr jr kc jc ∧
      W3 d a e alpha_t au av ep kr jr kc jc ∧
      W4 d a e alpha_t au av ep kr jr kc jc ∧
      W5 d a e alpha_t au av ep kr jr kc jc ∧
      W6 d a e alpha_t au av ep kr jr kc jc ∧
      W7 d a e alpha_t au av ep kr jr kc jc ∧
      W8 d a e alpha_t au av ep kr jr kc jc →
      N d a e av kc ∧ (∀ p h, T alpha_t kr p h))
    (resolve : ∀ p, Q p → I1 p ∧ I2 p ∧ I3 p ∧ I4 p ∧ I5 p ∧ I6 p ∧ I7 p)
    (complete : ∀ d a e alpha_t au av ep kr jr kc jc, W1 d a e alpha_t au av ep kr jr kc jc ∧
      W2 d a e alpha_t au av ep kr jr kc jc ∧
      W3 d a e alpha_t au av ep kr jr kc jc ∧
      W4 d a e alpha_t au av ep kr jr kc jc ∧
      W5 d a e alpha_t au av ep kr jr kc jc ∧
      W6 d a e alpha_t au av ep kr jr kc jc ∧
      W7 d a e alpha_t au av ep kr jr kc jc ∧
      W8 d a e alpha_t au av ep kr jr kc jc →
      ∃ er ec, ∀ p h, UR au er p h ∧ UC av ec p h) :
    ∃ d a e alpha_t au av ep kr jr kc jc er ec, W1 d a e alpha_t au av ep kr jr kc jc ∧
      W2 d a e alpha_t au av ep kr jr kc jc ∧
      W3 d a e alpha_t au av ep kr jr kc jc ∧
      W4 d a e alpha_t au av ep kr jr kc jc ∧
      W5 d a e alpha_t au av ep kr jr kc jc ∧
      W6 d a e alpha_t au av ep kr jr kc jc ∧
      W7 d a e alpha_t au av ep kr jr kc jc ∧
      W8 d a e alpha_t au av ep kr jr kc jc ∧
      N d a e av kc ∧
      ∀ p h, I1 p ∧
      I2 p ∧
      I3 p ∧
      I4 p ∧
      I5 p ∧
      I6 p ∧
      I7 p ∧
      UR au er p h ∧
      UC av ec p h ∧
      T alpha_t kr p h := by
  obtain ⟨d, a, e, alpha_t, au, av, ep, kr, jr, kc, jc, hw⟩ := chain
  obtain ⟨hn, ht⟩ := localize d a e alpha_t au av ep kr jr kc jc hw
  obtain ⟨er, ec, hu⟩ := complete d a e alpha_t au av ep kr jr kc jc hw
  refine ⟨d, a, e, alpha_t, au, av, ep, kr, jr, kc, jc, er, ec,
    hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
    hw.2.2.2.2.2.1, hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2, hn, ?_⟩
  intro p h
  have hi := resolve p h
  exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1,
    hi.2.2.2.2.2.1, hi.2.2.2.2.2.2, (hu p h).1, (hu p h).2, ht p h⟩

/-- The pulled quotient tower computes derived pullback, and its normalized Roos
augmentation is the actual completion unit. The isomorphisms eR and eC are in the
respective unbounded derived categories, natural in every flat-term K-flat input.
The final identity identifies the pulled augmentation with the existing strict-tower
completed-pullback comparison. No input completeness or boundedness is assumed.

Source: main-20261015, det-lem-int-tensor-pullback, first and comparison paragraphs;
Stacks proetale.tex, Tags 099M and 099N (2),(5).
(blueprint: lem-sfb-integral-roos-derived-pullback-unit).

Proof plan:
1. The integer ring is a DVR, hence Noetherian. Its finite positive quotients have
length-one finite free resolutions. Identify the completed coefficients with their
quotient limit by det-prop-sfb-qlbar-colimit-x-integral-limit.
2. Naturality of the Cartesian coefficient identification at each quotient gives
its finite projections. The limit universal property identifies it with c_g.
Only completed-coefficient inverse image needs the Cartesian exactness assertion.
3. Constant-completion-equivalence makes R flat over C. Flat-scalar-restriction-kflat
and ringed-topos-kflat-pullback therefore give flat-term K-flat Q, g_R^*P and g_C^*Q.
4. Strict quotient completion and kflat-scalar-tower-realization compute the entire
reduction towers, their transitions and the tensor-insertion augmentations.
5. Exactness of g_R^* makes termwise tower pullback preserve quasi-isomorphisms.
Apply diagram-kflat-replacements to the augmented source tower; its counit to T is
invertible, without claiming the individual quotient complexes are K-flat over R.
6. Integral-augmented-quotient-towers gives the balanced natural comparisons to U
and the constant reduction tower, including the augmentations and transitions.
7. Pro-etale-countable-products-exact and strict-roos-comparison identify the cone
with derived limit, normalized on K-injective towers by z mapping to (0,(z_n)).
The compatibility equation (1-s)b=0 gives D(0,bz)=(0,bdz).
8. Constant-completion-equivalence identifies these derived reduction limits with
completion, preserving their units, on arbitrary inputs. This gives eR and eC.
9. Apply naturality of the normalized Roos comparison to the strict balanced tower
isomorphism. Its diagonal product map preserves (0,bz), giving the displayed
completed-pullback unit equation and its interpretation on complete inputs.
10. Apply augmented-scalar-roos-resolution to the strict restricted augmentation.
Its identity-on-tuples product comparison preserves the normalized derived map.
Thus the scalar-restricted formula is constant-coefficient completed inverse image
on complete inputs and ordinary inverse image followed by completion otherwise.
All formulas are natural; the two ambient coefficient categories stay distinct. -/
theorem integralRoosDerivedPullbackUnit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    completedCoefficientMap g (datum l E) = ((datum l E).integralRingIso g).hom ∧
    (∀ n : ℕ, ((datum l E).integralRingIso g).hom ≫ (datum l E).projection X n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
          ((datum l E).projection Y n) ≫ ((datum l E).finiteRingIso g n).hom) ∧
    ∃ (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
      (a : T l E g ≅ U l E g)
      (e : T l E g ⋙ towerRes l E X ≅ V l E g)
      (αT : alphaTType l E g) (αU : alphaUType l E g) (αV : alphaVType l E g)
      (ε : EType l E g)
      (κR : kappaType X (R l E X)) (jR : inclusionType X (R l E X))
      (κC : kappaType X (C l E X)) (jC : inclusionType X (C l E X))
      (eR : ObjectProperty.ι (GoodR l E Y) ⋙ cxU l E g ⋙ roosF ⋙ DerivedCategory.Q ≅
        ObjectProperty.ι (GoodR l E Y) ⋙ cxPullR l E g ⋙ DerivedCategory.Q ⋙
          pbcActualCompletion (datum l E) X)
      (eC : ObjectProperty.ι (GoodR l E Y) ⋙ cxV l E g ⋙ roosF ⋙ DerivedCategory.Q ≅
        ObjectProperty.ι (GoodR l E Y) ⋙ cxRes l E Y ⋙ cxPullC l E g ⋙
          DerivedCategory.Q ⋙ OrderedExchange.completion (datum l E) X),
      PulledReduction.IsOrdinaryNormalized (datum l E) g d.inv ∧
      IsLambdaNormalized l E g a ∧
      (∀ (M : ModR l E Y) (n : ℕ), (e.hom.app M).app (op n) =
        d.hom.app (((redR l E Y).obj M).obj (op n)) ≫
          (pullC l E g).map
            (((OrderedExchange.ordinaryRho (datum l E) Y).inv.app M).app (op n))) ∧
      IsAugmentationNormalized l E g αT αU αV ∧
      IsENormalized l E g e ε ∧
      (∀ P : complexesR l E Y,
        (cxRes l E X).map (αT P) ≫ (ε P).hom =
          (dComplex l E g d).hom.app P ≫ αV P) ∧
      IsUnitNormalized X (R l E X) κR jR ∧ IsUnitNormalized X (C l E X) κC jC ∧
      IsConstantUnitNormalized l E g d a e αV κC ∧
      (∀ (P : complexesR l E Y) (hP : GoodR l E Y P),
        GoodR l E X ((cxPullR l E g).obj P) ∧
        GoodC l E Y ((cxRes l E Y).obj P) ∧
        GoodC l E X ((cxPullC l E g).obj ((cxRes l E Y).obj P)) ∧
        IsIso (towerCounit l E g P) ∧
        IsIso (completedOrdinaryPullbackComplexCounit g (datum l E) P) ∧
        IsIso (completedReductionTowerComplexCounit X (datum l E)
          ((cxPullR l E g).obj P)) ∧
        IsIso (OrderedExchange.reductionComplexCounit (datum l E) X
          (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P)) ∧
        DerivedCategory.Q.map (αU P) ≫ eR.hom.app ⟨P, hP⟩ =
          (pbcActualCompletionUnit (datum l E) X).app
            (DerivedCategory.Q.obj ((cxPullR l E g).obj P)) ∧
        DerivedCategory.Q.map (αV P) ≫ eC.hom.app ⟨P, hP⟩ =
          (OrderedExchange.unit (datum l E) X).app
            (DerivedCategory.Q.obj ((cxPullC l E g).obj ((cxRes l E Y).obj P))) ∧
        completedOrdinaryPullbackComplexCounit g (datum l E) P ≫
            DerivedCategory.Q.map (αT P) ≫ κR.hom.app ((cxT l E g).obj P) =
          completedPullbackComparison g (datum l E) (DerivedCategory.Q.obj P) ≫
            (completedRlim X (R l E X)).map (towerCounit l E g P)) := by
  classical
  have hcoeff : completedCoefficientMap g (datum l E) =
      ((datum l E).integralRingIso g).hom := by
    apply limit.hom_ext
    intro n
    change completedCoefficientMap g (datum l E) ≫ (datum l E).projection X n.unop =
      ((datum l E).integralRingIso g).hom ≫ (datum l E).projection X n.unop
    calc
      _ = completedCoefficientComponent g (datum l E) n.unop := limit.lift_π _ n
      _ = _ := by rw [(datum l E).projection_comm]; rfl
  refine ⟨hcoeff, (datum l E).projection_comm g, ?_⟩
  apply assembleRoos
  · obtain ⟨w, hw⟩ := integralRoosChainRepresentatives l E g k
    exact ⟨w.d, w.a, w.e, w.αT, w.αU, w.αV, w.ε, w.κR, w.jR, w.κC, w.jC, hw⟩
  · intro d a e αT αU αV ε κR jR κC jC hw
    obtain ⟨hU, hT, hV⟩ := integralRoosAugmentationLocalization l E g k
      d a e αT αU αV ε κR jR κC jC hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
      hw.2.2.2.2.1 hw.2.2.2.2.2.1 hw.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2
    exact ⟨hV, hT⟩
  · intro P hP
    have h := integralRoosResolvingCounits l E g k P hP
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro d a e αT αU αV ε κR jR κC jC hw
    obtain ⟨hU, hT, hV⟩ := integralRoosAugmentationLocalization l E g k
      d a e αT αU αV ε κR jR κC jC hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1
      hw.2.2.2.2.1 hw.2.2.2.2.2.1 hw.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2
    exact integralRoosCompletionIsomorphisms l E g k d a e αU αV κR κC
      (fun P hP ↦ (integralRoosResolvingCounits l E g k P hP).2.2.2.1)
      (fun P hP ↦ (integralRoosResolvingCounits l E g k P hP).2.2.2.2) hU hV

end WeilConjectures.IntegralPullbackStrictRoos
