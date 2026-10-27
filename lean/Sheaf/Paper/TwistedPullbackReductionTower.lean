/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.TwistedPullbackReductionData
public import Sheaf.Paper.SmoothPurityNormalizedEquivalence
public import Sheaf.Paper.SmoothPurityTowerBound
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.IntegralLineReductionRestriction
public import Sheaf.Paper.IntegralPullbackSystemComparison
public import Sheaf.Paper.PurReductionLimitShiftAdjunction
public import Sheaf.Paper.SignedLineScalarTensorTower
public import Sheaf.Paper.IntegralStrictReductionModel
public import Sheaf.Paper.AdicPuritySourceReduction
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.TwistedPullbackCofinalModels
import Sheaf.Paper.TwistedPullbackTateReduction
import Sheaf.Paper.TwistedPullbackLineMembership
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Coherent reduction of twisted completed pullback

Source: latest blueprint, sec-smooth-purity, integral-adjunction-bijection proof,
Purity paragraph (blueprint: lem-sp-twisted-pullback-reduction-tower).

Every natural-number index denotes the positive exponent n+1. The target is an
ordinary derived category of strict semilinear systems, including every quotient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]


attribute [local irreducible] reduction
  CofinalGeometry.derived nativeComparison cofinalSourceComparison realizationMap
  spCompletedReduction spCompletedTotalLimit spTowerShriekRealization
  integralDerivedPullback

private theorem coefficientPrimeUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have hc : Fintype.card D.k₀ = D.q := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (hc.trans D.cardinality_eq)
  let _ : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  apply isUnit_iff_ne_zero.mpr
  intro h
  have hdvd : D.p ∣ l := (CharP.cast_eq_zero_iff D.k D.p l).mp h
  obtain h | h := (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd
  · exact D.prime.ne_one h
  · exact hl h.symm

private def mappedTensorPairIso {A B C D E F : Type*} [Category A] [Category B]
    [Category C] [Category D] [Category E] [Category F]
    (G : A ⥤ B) (L : C) (H : B ⥤ D) (I : C ⥤ E) (G' : A ⥤ D)
    {L' : E} (a : G ⋙ H ≅ G') (b : I.obj L ≅ L') (T : D × E ⥤ F) :
    G ⋙ Prod.sectL B L ⋙ H.prod I ⋙ T ≅ G' ⋙ Prod.sectL D L' ⋙ T :=
  NatIso.ofComponents (fun X ↦ T.mapIso (Iso.prod (a.app X) b)) (by
    intro X Y z
    change T.map (Prod.mkHom (H.map (G.map z)) (I.map (𝟙 L))) ≫
        T.map (Prod.mkHom (a.hom.app Y) b.hom) =
      T.map (Prod.mkHom (a.hom.app X) b.hom) ≫
        T.map (Prod.mkHom (G'.map z) (𝟙 L'))
    rw [I.map_id, ← T.map_comp, ← T.map_comp]
    congr 1
    ext
    · exact a.hom.naturality z
    · simp)

private theorem leftIso_app {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) {G H : B ⥤ C} (a : G ≅ H) (X : A) :
    (isoWhiskerLeft F a).app X = a.app (F.obj X) := rfl

private theorem rightIso_app {A B C : Type*} [Category A] [Category B] [Category C]
    {F G : A ⥤ B} (a : F ≅ G) (H : B ⥤ C) (X : A) :
    (isoWhiskerRight a H).app X = H.mapIso (a.app X) := rfl

private theorem mappedTensorPairIso_app {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (G : A ⥤ B) (L : C) (H : B ⥤ D) (I : C ⥤ E) (G' : A ⥤ D)
    {L' : E} (a : G ⋙ H ≅ G') (b : I.obj L ≅ L') (T : D × E ⥤ F) (X : A) :
    (mappedTensorPairIso G L H I G' a b T).app X =
      T.mapIso (Iso.prod (a.app X) b) := rfl

private theorem equivalenceRealization {A B C D : Type*} [Category A] [Category B]
    [Category C] [Category D] (P : A ⥤ B) (R : B ⥤ C) (L : C ⥤ B)
    (N : A ⥤ C) (H : C ≌ D) (η : 𝟭 B ⟶ R ⋙ L)
    (e : P ⋙ R ⋙ H.functor ≅ N ⋙ H.functor)
    (hη : ∀ X : A, IsIso (η.app (P.obj X))) :
    (∀ X : A, IsIso (η.app (P.obj X) ≫ L.map
      (H.unitIso.hom.app (R.obj (P.obj X)) ≫ H.inverse.map (e.hom.app X) ≫
        H.unitIso.inv.app (N.obj X)))) ∧
    ∀ (X Y : A) (z : X ⟶ Y),
      P.map z ≫ (η.app (P.obj Y) ≫ L.map
        (H.unitIso.hom.app (R.obj (P.obj Y)) ≫ H.inverse.map (e.hom.app Y) ≫
          H.unitIso.inv.app (N.obj Y))) =
      (η.app (P.obj X) ≫ L.map
        (H.unitIso.hom.app (R.obj (P.obj X)) ≫ H.inverse.map (e.hom.app X) ≫
          H.unitIso.inv.app (N.obj X))) ≫ L.map (N.map z) := by
  let w : P ⋙ R ≅ N := isoWhiskerLeft (P ⋙ R) H.unitIso ≪≫
    isoWhiskerRight e H.inverse ≪≫ isoWhiskerLeft N H.unitIso.symm
  let r : P ⟶ N ⋙ L := Functor.whiskerLeft P η ≫ Functor.whiskerRight w.hom L
  have hr (X : A) : η.app (P.obj X) ≫ L.map
      (H.unitIso.hom.app (R.obj (P.obj X)) ≫ H.inverse.map (e.hom.app X) ≫
        H.unitIso.inv.app (N.obj X)) = r.app X := rfl
  constructor
  · intro X
    have := hη X
    rw [hr X]
    dsimp only [r, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    infer_instance
  · intro X Y z
    rw [hr X, hr Y]
    exact r.naturality z


private def nativeNat {X Y : Scheme.{u}} (f : X ⟶ Y) (m s : ℤ)
    (h : PurReductionLimitShiftData l E X
      (coefficientDerivedSystemEvaluationCalculus l E X).choose)
    (a : (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f ⋙
        (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ≅
      integralSystemReduction l E Y ⋙ finiteSystemDerivedPullback
        (integralSystemRings l E) (integralSystemTransition l E) f) :
    source l E f m s ⋙ (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ≅
      nativeFiniteSource l E f m s := by
  let S := (coefficientDerivedSystemEvaluationCalculus l E X).choose
  let B := (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f
  let L := (DerivedCategory.singleFunctor _ 0).obj (integralTwistLine l E X m)
  let := h.reduction_shift
  exact isoWhiskerLeft (B ⋙ Prod.sectL _ L ⋙ S.integralClosed.tensor)
      (S.reduction.commShiftIso s) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft (B ⋙ Prod.sectL _ L) S.reductionTensor ≪≫
        mappedTensorPairIso B L S.reduction S.reduction _ a
          (Iso.refl (S.reduction.obj L)) S.systemClosed.tensor)
      (shiftFunctor _ s)


private theorem nativeNat_app {X Y : Scheme.{u}} (f : X ⟶ Y) (m s : ℤ)
    (h : PurReductionLimitShiftData l E X
      (coefficientDerivedSystemEvaluationCalculus l E X).choose)
    (a : (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E f ⋙
        (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction ≅
      integralSystemReduction l E Y ⋙ finiteSystemDerivedPullback
        (integralSystemRings l E) (integralSystemTransition l E) f)
    (K : sfIntegralConstructibleCategory l E Y) :
    (nativeNat l E f m s h a).app K = nativeComparison l E f m s h a K := by
  simp only [nativeNat, NatIso.trans_app, leftIso_app, rightIso_app,
    mappedTensorPairIso_app]
  unfold nativeComparison
  rfl

attribute [local irreducible] nativeNat

set_option linter.unusedVariables false in
/-- Coherent twisted pullback reduction, including its strict cofinal normalization
and the actual reconstruction unit.

Source: latest blueprint, sec-smooth-purity, integral-adjunction-bijection proof,
Purity paragraph; Stacks 07A4, 099N(5), 0941; Bhatt--Scholze 3.5.7, 6.5.9.
(blueprint: lem-sp-twisted-pullback-reduction-tower).

Proof: write ell=u*pi^e in the DVR. Restrict strict systems to the positive levels
 e(n+1); the quotient identifications are induced by the identity on O_E, so every
transition and local scalar generator is retained and changing the generator of
an ideal changes no map. The resolving-class construction supplies the strict
reduction models and their counit-normalized cofinal comparison. Exact inverse
image commutes with this restriction: its comparison is the mate of the identity
on direct-image sections. The same restriction commutes with total tensor by the
identity on every selected tensor generator and total-degree summand. This fixes
its derived class on K-flat complexes, before finite evaluation.

The completed pullback comparison is the adjoint of the actual Roos projection
on any flat-term K-flat representative. Use integralPullbackSystemComparison for
its whole-system form. Tensor with the signed Tate line using reductionTensor.
Its simultaneous representative normalization is the balanced map, and the
signed-line PowerFormula fixes zero powers by the coefficient unitor, positive
powers by tensor reassociation, and negative powers by dual evaluation with both
quotient scalars. The reduction shift comparison is the identity on shifted
terms, with differential (-1)^s d. Thus nativeComparison is precisely the
specified composite. Transport by the strict cofinal comparisons gives q and
its equation below; naturality is inherited from the three functor comparisons.
All quotient squares, including equal indices, hold before localization.

Pullback preserves the integral constructible category. Signed line tensor
preserves completeness and the same common reduction interval; integer shift
translates that interval. This proves membership of P for every K. Its actual
reconstruction unit is therefore invertible. For any C and v, the stated map is
that unit followed by total limit of q and v, with the section presentation's
unit inserted. Functors preserve isomorphisms, so this composite is invertible;
naturality follows by composing the unit, q and v naturality squares. -/
theorem twistedPullbackReductionTower
    (D₀ : FiniteFieldDatum.{u}) (_hlp : l ≠ D₀.p)
    (X Y : Over (Spec (CommRingCat.of D₀.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f.left)
    (DX : SpCoefficientTowersAbelian l E X.left) (RX : SpReductionTower l E X.left DX)
    (NX : SpNormalizedEquivalence l E X.left DX RX)
    (DY : SpCoefficientTowersAbelian l E Y.left) (RY : SpReductionTower l E Y.left DY)
    (m s : ℤ) :
    (∀ K : sfIntegralConstructibleCategory l E Y.left,
      sfIntegralConstructible l E X.left ((source l E f.left m s).obj K)) ∧
    ∃ (hX : ∀ x : X.left, Invertible (l : X.left.residueField x))
      (hY : ∀ y : Y.left, Invertible (l : Y.left.residueField y)),
    letI := hX
    letI := hY
    ∃ (AX : IntegralStrictReductionModel l E X.left)
      (AY : IntegralStrictReductionModel l E Y.left)
      (FX : CofinalModel l E b X.left) (FY : CofinalModel l E b Y.left)
      (cX : CofinalReduction l E b X.left DX RX AX FX)
      (cY : CofinalReduction l E b Y.left DY RY AY FY)
      (G : CofinalGeometry l E b f.left g FX FY)
      (T : CofinalTensor l E b X.left FX)
      (tate : TateReduction l E X.left)
      (h : PurReductionLimitShiftData l E X.left
        (coefficientDerivedSystemEvaluationCalculus l E X.left).choose)
      (a : (sfIntegralConstructible l E Y.left).ι ⋙ integralDerivedPullback l E f.left ⋙
          (coefficientDerivedSystemEvaluationCalculus l E X.left).choose.reduction ≅
        integralSystemReduction l E Y.left ⋙ finiteSystemDerivedPullback
          (integralSystemRings l E) (integralSystemTransition l E) f.left)
      (q : source l E f.left m s ⋙ reduction l E b X.left DX RX ≅
        finiteSource l E b f.left g DX RX DY RY m s),
      (∀ (K : sfIntegralConstructibleCategory l E Y.left)
        (P : (integralOperationsGoodComplex l E Y.left).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (n : ℕ),
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X.left n).map (a.hom.app K) ≫
          (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
            (integralSystemTransition l E) f.left n).hom.app
              ((integralSystemReduction l E Y.left).obj K) ≫
          (Scheme.proEtaleConstantRingDerivedPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f.left).map
              ((integralSystemReductionEvaluation l E Y.left n).hom.app K) =
        (((coefficientDerivedSystemEvaluationCalculus l E X.left).choose.reductionEvaluation
          n).hom.app ((integralDerivedPullback l E f.left).obj K.obj)) ≫
            (integralSystemPullbackReductionIso l E f.left K P e n).hom) ∧
      (∀ K : sfIntegralConstructibleCategory l E Y.left,
        q.app K = (cX.derived.app ((source l E f.left m s).obj K)).symm ≪≫
          FX.ordinary.mapDerivedCategory.mapIso
            (nativeComparison l E f.left m s h a K) ≪≫
          cofinalSourceComparison l E b f.left g DX RX DY RY AX AY FX FY cX cY G T m s K) ∧
      (∀ C : sfIntegralConstructibleCategory l E Y.left ⥤
          spNormalizedConstructibleTorTowerCategory l E X.left DX,
        ∀ v : finiteSource l E b f.left g DX RX DY RY m s ≅
          C ⋙ (spNormalizedConstructibleTorTowers l E X.left DX).ι ⋙
            (spTowerShriekRealization l E b X.left DX).functor,
          (∀ K : sfIntegralConstructibleCategory l E Y.left,
            IsIso (realizationMap l E b f.left g DX RX NX DY RY m s q C v K)) ∧
          ∀ (K K' : sfIntegralConstructibleCategory l E Y.left) (z : K ⟶ K'),
            letI := NX.forgetAdditive
            letI := NX.forgetLimits
            letI := NX.forgetColimits
            (source l E f.left m s).map z ≫
                realizationMap l E b f.left g DX RX NX DY RY m s q C v K' =
              realizationMap l E b f.left g DX RX NX DY RY m s q C v K ≫
                (spCompletedTotalLimit l E X.left DX).map (C.map z).hom) := by
  let hX : ∀ x : X.left, Invertible (l : X.left.residueField x) := fun x ↦ by
    let φ : D₀.k →+* X.left.residueField x :=
      (X.left.evaluation ⊤ x (by trivial)).hom.comp
        (X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of D₀.k)).inv.hom)
    exact (show IsUnit (l : X.left.residueField x) from by
      simpa only [map_natCast] using (coefficientPrimeUnit D₀ l _hlp).map φ).invertible
  let hY : ∀ y : Y.left, Invertible (l : Y.left.residueField y) := fun y ↦ by
    let φ : D₀.k →+* Y.left.residueField y :=
      (Y.left.evaluation ⊤ y (by trivial)).hom.comp
        (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of D₀.k)).inv.hom)
    exact (show IsUnit (l : Y.left.residueField y) from by
      simpa only [map_natCast] using (coefficientPrimeUnit D₀ l _hlp).map φ).invertible
  have hm : ∀ K : sfIntegralConstructibleCategory l E Y.left,
      sfIntegralConstructible l E X.left ((source l E f.left m s).obj K) := by
    intro K
    have hM := ((integralOperations_preserve_constructible l E f.left).1 K.obj K.property).1
    have hL := twistedPullbackLineMembership l E X.left m ⟨_, hM⟩
    simpa only [source, Functor.comp_obj, Prod.sectL_obj, ObjectProperty.shift,
      ObjectProperty.ι_obj] using
      (sfIntegralConstructible l E X.left).le_shift s _ hL
  refine ⟨hm, hX, hY, ?_⟩
  obtain ⟨AX, AY, FX, FY, cX, cY, G, T, transport⟩ :=
    twistedPullbackCofinalModels l E f.left b g DX RX DY RY
  obtain ⟨tate⟩ := twistedPullbackTateReduction l E X.left
  obtain ⟨h⟩ := purReductionLimitShiftAdjunction l E X.left
    (coefficientDerivedSystemEvaluationCalculus l E X.left).choose
    (coefficientDerivedSystemEvaluationCalculus l E X.left).choose_spec.some
  obtain ⟨β, hβ⟩ := integralPullbackSystemComparison l E
  let a : (sfIntegralConstructible l E Y.left).ι ⋙ integralDerivedPullback l E f.left ⋙
        (coefficientDerivedSystemEvaluationCalculus l E X.left).choose.reduction ≅
      integralSystemReduction l E Y.left ⋙ finiteSystemDerivedPullback
        (integralSystemRings l E) (integralSystemTransition l E) f.left := β f.left
  let F : coefficientSequenceDerived l E X.left ⥤ SpTowerShriek.D l E X.left :=
    FX.ordinary.mapDerivedCategory
  let n := nativeNat l E f.left m s h a
  obtain ⟨c, hc⟩ := transport m s
  let q : source l E f.left m s ⋙ reduction l E b X.left DX RX ≅
      finiteSource l E b f.left g DX RX DY RY m s :=
    isoWhiskerLeft (source l E f.left m s) cX.derived.symm ≪≫
      isoWhiskerRight n F ≪≫ c
  refine ⟨AX, AY, FX, FY, cX, cY, G, T, tate, h, a, q, ?_, ?_, ?_⟩
  · intro K P e n
    exact hβ f.left K P e n
  · intro K
    have hn : n.app K = nativeComparison l E f.left m s h a K :=
      nativeNat_app l E f.left m s h a K
    change (cX.derived.app _).symm ≪≫ F.mapIso (n.app K) ≪≫ c.app K = _
    rw [hn, hc K]
  · intro C v
    let := NX.forgetAdditive
    let := NX.forgetLimits
    let := NX.forgetColimits
    unfold realizationMap
    unfold reduction at q
    apply equivalenceRealization (source l E f.left m s)
      (spCompletedReduction l E X.left DX RX) (spCompletedTotalLimit l E X.left DX)
      (C ⋙ (spNormalizedConstructibleTorTowers l E X.left DX).ι)
      (spTowerShriekRealization l E b X.left DX) NX.adjunction.unit (q ≪≫ v)
    intro K
    have hc : IntegralOnSlice.IsComplete l E X.left none
        ((source l E f.left m s).obj K) := by
      obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
      let : Fact p.Prime := ⟨hprime⟩
      let D : FiniteFieldDatum.{0} :=
        { p := p
          a := 1
          q := p
          prime := hprime
          exponent_pos := by decide
          cardinality_eq := by simp
          k₀ := ZMod p
          card_base := by simp [Nat.card_eq_fintype_card]
          k := AlgebraicClosure (ZMod p) }
      have hl : l ≠ D.p := by change l ≠ p; omega
      exact ⟨D, hl, (sfDerivedComplete_iff_legacy l E X.left D hl _).mp (hm K).1⟩
    exact NX.unit_isIso _ hc

end WeilConjectures.SpTwistedPullback
