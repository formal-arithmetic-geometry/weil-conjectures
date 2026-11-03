/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
public import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
import WeilConjectures.AlgebraicGeometry.VectorTranslationTraceUnitFamily
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteBundleSectionAdjointBaseChange
import all WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.AlgebraicGeometry.Section.SectionPullbackCoefficientNaturality
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteUnitCoordinateIdentifications

/-! # Translation of the diagonal to the zero section

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/
sk-prop-sp-orientation/sk-prop-sp-orientation-vector-bundle.proof.md.
(blueprint: lem-pur-general-field-diagonal-translation-adjoint).

The comparison here concerns only the integration adjunct and the Cartesian pair.
It does not assert a formula for normalized specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local implicit_reducible] Scheme.Modules vectorIntegrationCoefficient
  CategoryTheory.catToReflQuiver ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  sectionInvariant dualizingComplex
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13
set_option synthInstance.maxSize 2048

-- Restriction of a mate square, followed by cancellation of its coefficient comparison.
private theorem restrict_mate_square
    {C D : Type*} [Category C] [Category D]
    (R Q : C ⥤ D) (Z : D ⥤ C)
    (sr : 𝟭 C ⟶ R ⋙ Z) (sq : 𝟭 C ⟶ Q ⋙ Z)
    {K L W : C} {E : D} (c : K ≅ W)
    (b : K ⟶ L) (b' : Q.obj W ⟶ E)
    (a : R.obj K ⟶ Q.obj W) (B : R.obj L ⟶ E)
    (hm : R.map b ≫ B = a ≫ b')
    (hc : sr.app K ≫ Z.map a = c.hom ≫ sq.app W) :
    (c.inv ≫ b) ≫ (sr.app L ≫ Z.map B) = sq.app W ≫ Z.map b' := by
  have hn := sr.naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [Category.assoc, reassoc_of% hn, ← Z.map_comp, hm, Z.map_comp]
  rw [reassoc_of% hc]
  simp only [← Category.assoc, c.inv_hom_id, Category.id_comp]

-- Both retractions of z give the same restriction of a coefficient pulled back from S.
private theorem two_retractions
    (A : Type (u + 1)) [CommRing A]
    {S V U : Scheme.{u}} (p : V ⟶ S) (r q : U ⟶ V) (z : V ⟶ U)
    (hp : r ≫ p = q ≫ p) (hr : z ≫ r = 𝟙 V) (hq : z ≫ q = 𝟙 V)
    (K : DerivedCategoryModule A S) :
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z r hr).inv.app
        ((ordinaryFinitePullback A p).obj K) ≫
      (ordinaryFinitePullback A z).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r p).inv.app K ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p (r ≫ p) hp).hom.app K) =
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z q hq).inv.app
      ((ordinaryFinitePullback A p).obj K) := by
  have h₁ := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) z r p (𝟙 V) (r ≫ p) p hr.symm rfl
    (Category.id_comp p).symm K
  have h₂ := leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) z q p (𝟙 V) (r ≫ p) p hq.symm hp
    (Category.id_comp p).symm K
  have h :
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z r hr).inv.app
          ((ordinaryFinitePullback A p).obj K) ≫
        (ordinaryFinitePullback A z).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r p).inv.app K) =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z q hq).inv.app
          ((ordinaryFinitePullback A p).obj K) ≫
        (ordinaryFinitePullback A z).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) q p (r ≫ p) hp).inv.app K) := by
    dsimp only [ordinaryFinitePullback] at h₁ h₂ ⊢
    simp only [leftDerivedUpperStarCompSectionIso, Iso.trans_inv,
      Iso.symm_inv, NatTrans.comp_app, Category.assoc]
    rw [h₁, h₂]
  rw [Functor.map_comp, ← Category.assoc, h, Category.assoc, ← Functor.map_comp]
  dsimp only [ordinaryFinitePullback]
  simp only [Iso.inv_hom_id_app]
  exact (congrArg (fun f ↦
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z q hq).inv.app
      ((ordinaryFinitePullback A p).obj K) ≫ f)
    ((ordinaryFinitePullback A z).map_id _)).trans (Category.comp_id _)

-- Paste the two exceptional squares, then restrict along their compatible sections.
private theorem diagonal_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S V U : Scheme.{u}} [IsNoetherian S] [IsNoetherian V] [IsNoetherian U]
    (p : V ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [IsNoetherian (pullback p p)]
    (q : U ⟶ V) [HasCompactification q] [QuasiCompact q]
    (e : U ⟶ pullback p p) (sq : IsPullback e q (pullback.fst p p) (𝟙 V))
    (z : V ⟶ U) (hz : z ≫ e = (𝟙 V) ≫ pullback.diagonal p)
    (hr : z ≫ (e ≫ pullback.snd p p) = 𝟙 V)
    (outer : IsPullback (e ≫ pullback.snd p p) q p p) :
    finiteSmoothDiagonalFactor A p ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) V).inv.app _ ≫
        NoetherianSectionSpecialization.sectionMap A (pullback.fst p p) q (𝟙 V)
          e sq (pullback.diagonal p) z hz =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z
        (e ≫ pullback.snd p p) hr).inv.app _ ≫
          (ordinaryFinitePullback A z).map (dualizingComplexBaseChangeMap A outer) := by
  let r := e ≫ pullback.snd p p
  let D := dualizingComplex A p
  let I := leftDerivedUpperStarId (ModuleCat.{u + 1} A) V
  let B := dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback p p).flip
  have hpaste : dualizingComplexBaseChangeMap A outer =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e (pullback.snd p p)).hom.app D ≫
        (ordinaryFinitePullback A e).map B ≫ dualizingComplexBaseChangeMap A sq := by
    exact WeilConjectures.cube_dualizing_base_comp_chosen A
      (IsPullback.of_hasPullback p p).flip sq
      (e ≫ pullback.snd p p) p rfl (Category.id_comp p).symm outer
  have hcomm : e ≫ pullback.snd p p = r ≫ 𝟙 V := (Category.comp_id r).symm
  have ha : (ordinaryFinitePullback A e).map B ≫ dualizingComplexBaseChangeMap A sq =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) e (pullback.snd p p)).inv.app D ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r (𝟙 V)
          (e ≫ pullback.snd p p) hcomm).hom.app D ≫
        (ordinaryFinitePullback A r).map (I.hom.app D) ≫
        dualizingComplexBaseChangeMap A outer := by
    have hu :
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r (𝟙 V)
          (e ≫ pullback.snd p p) hcomm).hom.app D ≫
          (ordinaryFinitePullback A r).map (I.hom.app D) = 𝟙 _ := by
      exact leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) r D
    rw [← Category.assoc _ ((ordinaryFinitePullback A r).map _) _, hu]
    simp only [Category.id_comp]
    rw [hpaste]
    simp only [Iso.inv_hom_id_app_assoc]
  have h := sectionPullback_coefficient_naturality A (𝟙 V) (pullback.snd p p) r e
    (pullback.diagonal p) z hcomm hz (pullback.diagonal_snd p) hr D D
    (dualizingComplex A (pullback.fst p p)) (dualizingComplex A q) (I.hom.app D)
    B (dualizingComplexBaseChangeMap A outer) (dualizingComplexBaseChangeMap A sq) ha
  change (ordinaryFinitePullback A (𝟙 V)).map (finiteSmoothDiagonalFactor A p) ≫
      NoetherianSectionSpecialization.sectionMap A (pullback.fst p p) q (𝟙 V)
        e sq (pullback.diagonal p) z hz =
      I.hom.app D ≫
        (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z r hr).inv.app D ≫
          (ordinaryFinitePullback A z).map (dualizingComplexBaseChangeMap A outer) at h
  have hn := I.inv.naturality (finiteSmoothDiagonalFactor A p)
  dsimp only [Functor.id_map, I, sectionInvariant] at hn
  dsimp only [I, D, r, ordinaryFinitePullback] at h ⊢
  rw [← Category.assoc, hn, Category.assoc, h]
  simp only [Iso.inv_hom_id_app_assoc]

/-- The addition presentation of the self-product carries the diagonal integration
adjunct to the zero-section integration adjunct on the pulled-back bundle.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/
sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 1 and the base-change part of Step 3.
(blueprint: lem-pur-general-field-diagonal-translation-adjoint).

Proof: put V=Spec Sym(M), U=Spec Sym(p^*M). Minus translation on U acts on
the trace line by a locally constant unit equal to one along the zero section.
Its identity locus is clopen; frame charts identify fibres with connected affine
spaces, so the unit is one everywhere. Full faithfulness in degree zero gives the
identity of the actual compact-support action. Minus translation followed by the
addition presentation gives the canonical bundle base-change map; pasting the
exchange and Tate comparisons therefore gives integration compatibility for addition.
Uniqueness of normalized finite Tate transport identifies the supplied comparison.
Transpose this trace square under the exceptional adjunctions. Pasting exceptional
base-change maps and naturality of section compositors identify its zero-section
restriction with the diagonal and identity-base transport. The two retractions of
zero give the same restriction of coefficients pulled back from S. Naturality and
cancellation of the coefficient isomorphism give bundleSectionAdjoint. The formulas
also apply at rank zero, n=0, and over the empty base. -/
theorem generalFieldDiagonalTranslationAdjoint
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (S : Scheme.{u}) [IsNoetherian S] (aS : S ⟶ Spec (.of k))
    [IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]
    (n : ℕ) (d : ℕ) (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))) :
    let A := coefficient.{u} ell n
    let N := ell ^ n
    let hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
    let hA : (N : A) = 0 := CharP.cast_eq_zero _ _
    let V := VectorBundleZeroSection.scheme S d M
    let p := VectorBundleZeroSection.π S d M
    letI := (vectorIntegration_geometry S d M).1
    letI := (vectorIntegration_geometry S d M).2.1
    letI := (vectorIntegration_geometry S d M).2.2
    let F := (Scheme.Modules.tensorPullback p).obj M
    let q := VectorBundleZeroSection.π V d F
    let z := VectorBundleZeroSection.zero V d F
    letI := (vectorIntegration_geometry V d F).1
    letI := (vectorIntegration_geometry V d F).2.1
    letI := (vectorIntegration_geometry V d F).2.2
    let hV : IsUnit (N : Γ(V, ⊤)) := by
      simpa only [map_natCast] using hS.map p.appTop.hom
    ∀ (t : OrdinaryFiniteTwistTransport A N hA),
    ∃ (hz : z ≫ (VectorTraceGeometry.diagonalAdditionPresentation S d M).hom =
        (𝟙 V) ≫ pullback.diagonal p),
    let e := VectorTraceGeometry.diagonalAdditionPresentation S d M
    let sq : IsPullback e.hom q (pullback.fst p p) (𝟙 V) :=
      IsPullback.of_horiz_isIso ⟨by
        simpa only [Category.comp_id] using
          VectorTraceGeometry.diagonalAdditionPresentation_first S d M⟩
    ((vectorIntegrationBaseCoefficientPullback A N hA t p hS d).inv ≫
        FiniteRingSectionDeformation.bundleAdjoint N hN A hA S hS d M) ≫
      finiteSmoothDiagonalFactor A p ≫
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) V).inv.app _ ≫
      NoetherianSectionSpecialization.sectionMap A (pullback.fst p p) q (𝟙 V)
        e.hom sq (pullback.diagonal p) z hz =
      FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA V hV d F := by
  dsimp only
  let A := coefficient.{u} ell n
  let N := ell ^ n
  have hN : 0 < N := pow_pos (Fact.out : ell.Prime).pos n
  have hA : (N : A) = 0 := CharP.cast_eq_zero _ _
  let V := VectorBundleZeroSection.scheme S d M
  let p := VectorBundleZeroSection.π S d M
  let := (vectorIntegration_geometry S d M).1
  let := (vectorIntegration_geometry S d M).2.1
  let := (vectorIntegration_geometry S d M).2.2
  let F := (Scheme.Modules.tensorPullback p).obj M
  let q := VectorBundleZeroSection.π V d F
  let z := VectorBundleZeroSection.zero V d F
  let := (vectorIntegration_geometry V d F).1
  let := (vectorIntegration_geometry V d F).2.1
  let := (vectorIntegration_geometry V d F).2.2
  have hV : IsUnit (N : Γ(V, ⊤)) := by
    simpa only [map_natCast] using hS.map p.appTop.hom
  intro t
  let e := VectorTraceGeometry.diagonalAdditionPresentation S d M
  have hz : z ≫ e.hom = (𝟙 V) ≫ pullback.diagonal p := by
    simpa only [Category.id_comp] using
      VectorTraceGeometry.diagonalAdditionPresentation_zero S d M
  refine ⟨hz, ?_⟩
  let sq : IsPullback e.hom q (pullback.fst p p) (𝟙 V) :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using
      VectorTraceGeometry.diagonalAdditionPresentation_first S d M⟩
  let r := e.hom ≫ pullback.snd p p
  have hr : z ≫ r = 𝟙 V := by
    dsimp only [r]
    rw [← Category.assoc, hz, Category.id_comp, pullback.diagonal_snd]
  have hq : z ≫ q = 𝟙 V := (VectorBundleZeroSection.zero_spec V d F).1
  have outer : IsPullback r q p p := by
    simpa only [Category.id_comp] using
      sq.paste_horiz (IsPullback.of_hasPullback p p).flip
  have hp : r ≫ p = q ≫ p := outer.w
  have ht := ordinaryFiniteTwistTransport_unique A N hA t
    (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA)
  cases ht
  let c := vectorIntegrationBaseCoefficientPullback A N hA
    (WeilConjectures.PurityFiniteSetting.purityTwistTransport A N hN hA) p hS d
  let a := (WeilConjectures.PurityFiniteSetting.purityPullbackSquare A outer
    (affineLinearBaseCoefficient A N hA S d) ≪≫
      (ordinaryFinitePullback A q).mapIso c).hom
  let adj := vectorBundlePurityAdjunction A S d M
  let adj' := vectorBundlePurityAdjunction A V d F
  let trace := vectorBundleIntegration N hN A hA S hS d M
  let trace' := vectorBundleIntegration N hN A hA V hV d F
  have htrace := vectorTranslationAdditionTrace N hN A hA S hS d M outer
  have := isIso_rightDerivedLowerShriekBaseChangeMap A outer
  let ex := asIso (rightDerivedLowerShriekBaseChangeMap A outer)
  have he : ex.hom.app _ ≫ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q).map a ≫
      trace' = (ordinaryFinitePullback A p).map trace ≫
        (ordinaryFiniteUnitPullback A p).hom := by
    dsimp only [ex, a, trace, trace', c,
      WeilConjectures.PurityFiniteSetting.RfPullback,
      WeilConjectures.PurityFiniteSetting.RfShriek, vectorIntegrationCoefficient] at htrace ⊢
    simpa only [asIso_hom, Functor.map_comp, Category.assoc] using htrace
  have hm := FiniteRingSectionDeformation.integration_mate_square adj adj'
    (ordinaryFinitePullback A r) (ordinaryFinitePullback A p) ex a trace trace'
    (ordinaryFiniteUnitPullback A p).hom he
  rw [ordinaryFiniteUnitPullback_eq_unitCoordinates] at hm
  change (ordinaryFinitePullback A r).map
      (FiniteRingSectionDeformation.bundleAdjoint N hN A hA S hS d M) ≫
        dualizingComplexBaseChangeMap A outer =
      a ≫ FiniteRingSectionDeformation.bundleAdjoint N hN A hA V hV d F at hm
  have hD := diagonal_transport A p q e.hom sq z hz hr outer
  have hcoeff :
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z r hr).inv.app
          (vectorIntegrationCoefficient A N hA S d M) ≫
        (ordinaryFinitePullback A z).map a =
      c.hom ≫ (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z q hq).inv.app
        (affineLinearBaseCoefficient A N hA V d) := by
    have hc := two_retractions A p r q z hp hr hq
      (affineLinearBaseCoefficient A N hA S d)
    dsimp only [a, WeilConjectures.PurityFiniteSetting.purityPullbackSquare,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
    dsimp only [vectorIntegrationCoefficient, ordinaryFinitePullback] at hc ⊢
    simp only [Functor.map_comp, Category.assoc] at hc ⊢
    rw [reassoc_of% hc]
    have hn := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
      z q hq).inv.naturality c.hom
    dsimp only [Functor.comp_map, Functor.id_map, ordinaryFinitePullback, p, V] at hn ⊢
    exact hn.symm
  have hfinal := restrict_mate_square
    (ordinaryFinitePullback A r) (ordinaryFinitePullback A q)
    (ordinaryFinitePullback A z)
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z r hr).inv
    (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) z q hq).inv
    c (FiniteRingSectionDeformation.bundleAdjoint N hN A hA S hS d M)
    (FiniteRingSectionDeformation.bundleAdjoint N hN A hA V hV d F)
    a (dualizingComplexBaseChangeMap A outer) hm hcoeff
  change (c.inv ≫ FiniteRingSectionDeformation.bundleAdjoint N hN A hA S hS d M) ≫
      (finiteSmoothDiagonalFactor A p ≫
        (leftDerivedUpperStarId (ModuleCat.{u + 1} A) V).inv.app _ ≫
        NoetherianSectionSpecialization.sectionMap A (pullback.fst p p) q (𝟙 V)
          e.hom sq (pullback.diagonal p) z hz) = _
  exact (congrArg (fun f ↦
    (c.inv ≫ FiniteRingSectionDeformation.bundleAdjoint N hN A hA S hS d M) ≫ f)
    hD).trans hfinal

end AlgebraicGeometry.Etale.FiniteSmoothPurity
