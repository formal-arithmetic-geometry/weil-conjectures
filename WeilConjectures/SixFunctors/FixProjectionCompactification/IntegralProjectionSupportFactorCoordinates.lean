/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionMiddleMap
public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionLocalFactors
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionDirectFactorEvaluation
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralProjectionOpenFactorEvaluation
import WeilConjectures.SixFunctors.FixProjectionCompactification.FiniteSupportFactorRealization
import WeilConjectures.SixFunctors.FixProjectionCompactification.IntegralSupportAdjunctFiniteCoordinates
import WeilConjectures.SixFunctors.Integral.IntegralReductionJointFaithfulness

/-! # One-input proper/open support coordinates

Source: prop-sf-pf-coherence.proof.md, compatibility with counits and open extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus scalarReductionDerivedExtension scalarReductionDerivedRestriction

attribute [local implicit_reducible] identitySquare sixFunctorIntegralReduction
  coefficientFiniteDerivedExtension sixFunctorFiniteSupport sfIntrinsicCompactSupport
  Over.homMk CostructuredArrow.homMk scalarReductionSourceDerived
  scalarReductionTargetDerived integralCoefficientSheaf integralCoefficientCommRingSheaf
  integralOperationsCommHasDerivedCategory integralCompletedRingHasDerivedCategory
  integralTowerHasDerivedCategory coefficientFiniteHasDerived reductionModulesHasDerivedCategory
  SemilinearSections.moduleAbelian sixFunctorFactorCompactification
  SixFunctorCompactifiedSquare.compactification

private theorem adjunct_factor
    {B N : Type*} [Category B] [Category N] {R : B ⥤ N} {L : N ⥤ B}
    (adj : R ⊣ L) {P U : B} {V : N} (e : L.obj V ≅ U) (s : R.obj P ⟶ V) :
    R.map ((adj.homEquiv _ _) s ≫ e.hom) ≫
        (adj.homEquiv _ _).symm e.inv = s := by
  rw [← adj.homEquiv_naturality_left_symm, Category.assoc,
    e.hom_inv_id, Category.comp_id, Equiv.symm_apply_apply]

private theorem finite_reflection
    {B N F : Type*} [Category B] [Category N] [Category F]
    (R : B ⥤ N) (ev : N ⥤ F) (red : B ⥤ F) (rho : R ⋙ ev ≅ red)
    {P U : B} {V : N} {W : F}
    (s : R.obj P ⟶ V) (d : R.obj U ⟶ V) (a r : P ⟶ U)
    (q : ev.obj V ≅ W) (b : red.obj U ≅ W)
    (ha : R.map a ≫ d = s)
    (hd : ev.map d ≫ q.hom = rho.hom.app U ≫ b.hom)
    (hs : ev.map s ≫ q.hom = rho.hom.app P ≫ red.map r ≫ b.hom) :
    red.map a = red.map r := by
  apply (cancel_mono b.hom).mp
  apply (cancel_epi (rho.hom.app P)).mp
  calc
    rho.hom.app P ≫ red.map a ≫ b.hom =
        ev.map (R.map a) ≫ rho.hom.app U ≫ b.hom := by
      rw [← Category.assoc, ← rho.hom.naturality a]
      simp only [Functor.comp_map, Category.assoc]
    _ = ev.map (R.map a) ≫ ev.map d ≫ q.hom := by rw [hd]
    _ = ev.map s ≫ q.hom := by rw [← ev.map_comp_assoc, ha]
    _ = rho.hom.app P ≫ red.map r ≫ b.hom := hs

private theorem iso_inv_app_heq
    {B N : Type*} [Category B] [Category N]
    {F G F' G' : B ⥤ N} (hF : F = F') (hG : G = G')
    (e : F ≅ G) (e' : F' ≅ G') (he : HEq e e') (K : B) :
    HEq (e.inv.app K) (e'.inv.app K) := by
  subst F'
  subst G'
  cases eq_of_heq he
  rfl

private theorem transport_hom_eq
    {B : Type*} [Category B] {X Y X' Y' : B}
    (hX : X = X') (hY : Y = Y')
    (v : X' ⟶ Y') (w : X ⟶ Y) (h : HEq v w) :
    eqToHom hX ≫ v ≫ eqToHom hY.symm = w := by
  subst X'
  subst Y'
  simpa using eq_of_heq h

private theorem full_eqToHom
    {B : Type*} [Category B] {P : ObjectProperty B}
    {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst Y
  rfl

private theorem supportMap_normalized
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type*}
    [∀ X, Category (B X)] {S : SixFunctorPushStage D B}
    {T : ∀ X, B X ⥤ B X ⥤ B X} {Q : SixFunctorCompactifiedSquare D}
    (A : SixFunctorExchangeData S T Q) (K : B Q.X) :
    ProjectionFactors.supportMap A K =
      eqToHom (by rw [A.properPush, A.openExtension]; rfl) ≫
        (sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
          Q.f Q.factorization).inv.app K := by
  let sigma := sixFunctorFactoredSupportIdentification S Q.i Q.p Q.open_i Q.proper_p
    Q.f Q.factorization
  have hi := iso_inv_app_heq A.compactSupport
    (congrArg₂ (· ⋙ ·) A.openExtension A.properPush)
    A.stage.compactSupportIdentification sigma A.compactSupportNormalization K
  have ht := transport_hom_eq
    (congrArg (fun F ↦ F.obj K) (congrArg₂ (· ⋙ ·) A.openExtension A.properPush))
    (congrArg (fun F ↦ F.obj K) A.compactSupport)
    (sigma.inv.app K) (A.stage.compactSupportIdentification.inv.app K) hi.symm
  unfold ProjectionFactors.supportMap
  rw [← ht]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

private theorem factoredSupport_preserved
    {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category (B X)]
    {B' : SixFunctorSpace D → Type*} [∀ X, Category (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {V : ∀ X, B X ⥤ B' X} (beta : SixFunctorCoefficientComparison S S' V)
    {X Y Z : SixFunctorSpace D} (i : X ⟶ Z) (p : Z ⟶ Y)
    (hi : IsOpenImmersion i.hom.left) (hp : IsProper p.hom.left)
    (f : X ⟶ Y) (h : f = i ≫ p) (K : B X) :
    (V Y).map ((sixFunctorFactoredSupportIdentification S i p hi hp f h).inv.app K) ≫
        (beta.supportAdjunction f (sixFunctorFactorCompactification i p hi hp f h)).left.hom.app
          K =
      (beta.directAdjunction p).right.hom.app ((S.openExtension i hi).obj K) ≫
        (S'.direct p).map ((beta.openExtension i hi).hom.app K) ≫
        (sixFunctorFactoredSupportIdentification S' i p hi hp f h).inv.app ((V X).obj K) := by
  have hh :
      (V Y).map ((sixFunctorFactoredSupportIdentification S i p hi hp f h).hom.app K) ≫
          (beta.directAdjunction p).right.hom.app ((S.openExtension i hi).obj K) ≫
          (S'.direct p).map ((beta.openExtension i hi).hom.app K) =
        (beta.supportAdjunction f (sixFunctorFactorCompactification i p hi hp f h)).left.hom.app
            K ≫
          (sixFunctorFactoredSupportIdentification S' i p hi hp f h).hom.app
            ((V X).obj K) := by
    subst f
    let : IsProper p.hom.left := hp
    simp only [sixFunctorFactoredSupportIdentification, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [reassoc_of% (beta.properIdentity p ((S.openExtension i hi).obj K))]
    rw [← (S'.properIdentity p).hom.naturality]
    have hn := (beta.supportAdjunction p (.ofIsProper p.hom.left)).left.hom.naturality
      ((S.openIdentification i hi).hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [reassoc_of% hn]
    rw [← Functor.map_comp_assoc, beta.openIdentification]
    rw [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (beta.composition i p (sixFunctorOpenCompactification i hi)
      (.ofIsProper p.hom.left) (sixFunctorFactorCompactification i p hi hp (i ≫ p) rfl) K)]
    rfl
  apply (cancel_epi
    ((V Y).map ((sixFunctorFactoredSupportIdentification S i p hi hp f h).hom.app K))).mp
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, (V Y).map_id, Category.id_comp]
  have hc := congrArg (fun t ↦ t ≫
    (sixFunctorFactoredSupportIdentification S' i p hi hp f h).inv.app ((V X).obj K)) hh
  simp only [Category.assoc, Iso.hom_inv_id_app] at hc
  exact (Category.comp_id _).symm.trans hc.symm

private theorem map_relation
    {B N : Type*} [Category B] [Category N] (F : B ⥤ N)
    {W X Y Z T : B} {r : W ⟶ X} {s : X ⟶ T}
    {a : W ⟶ Y} {b : Y ⟶ Z} {e : Z ⟶ T}
    (h : r ≫ s = a ≫ b ≫ e) :
    F.map r ≫ F.map s = F.map a ≫ F.map b ≫ F.map e := by
  simpa only [F.map_comp] using congrArg F.map h

private theorem map_composite_two
    {B N : Type*} [Category B] [Category N] (F : B ⥤ N)
    {W X : N} {Y Z T : B} (a : W ⟶ X) (b : X ⟶ F.obj Y)
    (c : Y ⟶ Z) (d : Z ⟶ T) :
    (a ≫ b) ≫ F.map (c ≫ d) = a ≫ b ≫ F.map c ≫ F.map d := by
  rw [F.map_comp, Category.assoc]

private theorem coordinate_paste
    {B : Type*} [Category B] {W A B₁ C D T U R : B}
    (a : W ⟶ A) (b : A ⟶ B₁) (c : B₁ ⟶ C) (d : C ⟶ U)
    (b' : A ⟶ D) (c' : D ⟶ C) (e : D ⟶ T) (v : T ⟶ U)
    (r : W ⟶ R) (s : R ⟶ T)
    (h₁ : b' ≫ c' = b ≫ c) (h₂ : e ≫ v = c' ≫ d)
    (h₃ : r ≫ s = a ≫ b' ≫ e) :
    a ≫ b ≫ c ≫ d = r ≫ s ≫ v := by
  calc
    a ≫ b ≫ c ≫ d = a ≫ b' ≫ c' ≫ d := by rw [← reassoc_of% h₁]
    _ = a ≫ b' ≫ e ≫ v := by rw [← h₂]
    _ = r ≫ s ≫ v := by
      simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ v) h₃.symm

private theorem naturality_paste
    {B : Type*} [Category B] {W X Y Z T U V : B}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T)
    (p : Y ⟶ U) (q : X ⟶ V) (r : V ⟶ U) (s : U ⟶ T)
    (h₁ : b ≫ p = q ≫ r) (h₂ : p ≫ s = c ≫ d) :
    a ≫ b ≫ c ≫ d = a ≫ q ≫ r ≫ s := by
  rw [← h₂, reassoc_of% h₁]

private theorem finite_factor
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) (m : ℕ)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    let A := S.higher.integralExchange (identitySquare f c)
    (scalarReductionDerivedExtension C.l E Y.obj.left m).map
        (ProjectionFactors.supportMap A K).hom ≫
      (FactorEvaluation.support D C E n hn S f c m K).hom =
    (FactorEvaluation.direct D C E n hn S f c m (A.stage.openExtension.obj K)).hom ≫
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (FactorEvaluation.extension D C E n hn S f c m K).hom := by
  let Q := identitySquare f c
  let A := S.higher.integralExchange Q
  let beta := S.integralNormalization.reduction m
  let F := S.integralNormalization.finiteLevels m
  let I := (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.le_add_left 1 m) Y.obj.left).ι
  let RY := scalarReductionDerivedExtension C.l E Y.obj.left m
  let RZ := scalarReductionDerivedExtension C.l E c.Z m
  let P := proEtaleConstantDerivedDirectImage c.g
    (Padic.coefficientExtensionRing C.l E (m + 1))
  let M := A.stage.openExtension.obj K
  let M' := (S.higher.integral.openExtension Q.i Q.open_i).obj K
  let Kn := (sixFunctorIntegralReduction D C E m X).obj K
  let e : M ≅ M' := eqToIso (congrArg (fun F ↦ F.obj K) A.openExtension)
  let v : A.stage.properPush.obj M ≅ (S.higher.integral.direct Q.p).obj M :=
    eqToIso (congrArg (fun F ↦ F.obj M) A.properPush)
  let d := FactorEvaluation.directIso D C E n hn S f c m
  let j := FactorEvaluation.extensionIso D C E n hn S f c m
  let sigma := sixFunctorFactoredSupportIdentification S.higher.integral
    Q.i Q.p Q.open_i Q.proper_p Q.f Q.factorization
  let sigma' := sixFunctorFactoredSupportIdentification F.finite
    Q.i Q.p Q.open_i Q.proper_p Q.f Q.factorization
  have hd := d.hom.naturality e.hom
  dsimp only [Functor.comp_map] at hd
  have hf := finiteSupportFactorRealization D C E (m + 1)
    (Nat.le_add_left 1 m) F f c Kn
  have hnat := (F.finiteDirectImage Q.p).hom.naturality
    ((beta.openExtension Q.i Q.open_i).hom.app K)
  dsimp only [Functor.comp_map] at hnat
  have hcanonical :
      d.hom.app M' ≫ P.map (j.hom.app K) =
        RY.map (sigma.inv.app K).hom ≫
          (FactorEvaluation.support D C E n hn S f c m K).hom := by
    have hcoeff := map_relation I
      (factoredSupport_preserved beta Q.i Q.p Q.open_i Q.proper_p Q.f Q.factorization K)
    exact (map_composite_two P
      (I.map ((beta.directAdjunction Q.p).right.hom.app M'))
      ((F.finiteDirectImage Q.p).hom.app ((sixFunctorIntegralReduction D C E m Q.Z).obj M'))
      ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
        (Nat.le_add_left 1 m) c.Z).ι.map ((beta.openExtension Q.i Q.open_i).hom.app K))
      ((F.finiteOpenExtension Q.i Q.open_i).hom.app Kn)).trans
      (coordinate_paste
        (I.map ((beta.directAdjunction Q.p).right.hom.app M'))
        ((F.finiteDirectImage Q.p).hom.app ((sixFunctorIntegralReduction D C E m Q.Z).obj M'))
        (P.map ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
          (Nat.le_add_left 1 m) c.Z).ι.map ((beta.openExtension Q.i Q.open_i).hom.app K)))
        (P.map ((F.finiteOpenExtension Q.i Q.open_i).hom.app Kn))
        (I.map ((F.finite.direct Q.p).map ((beta.openExtension Q.i Q.open_i).hom.app K)))
        ((F.finiteDirectImage Q.p).hom.app ((F.finite.openExtension Q.i Q.open_i).obj Kn))
        (I.map (sigma'.inv.app Kn)) ((F.finiteSupport f c).hom.app Kn)
        (RY.map (sigma.inv.app K).hom)
        (I.map ((beta.supportAdjunction f c).left.hom.app K)) hnat hf hcoeff)
  have hv : (FactorEvaluation.direct D C E n hn S f c m M).hom =
      RY.map v.hom.hom ≫ d.hom.app M := by
    simp only [FactorEvaluation.direct, v, d, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, eqToIso.hom, full_eqToHom]
    rfl
  have he : (FactorEvaluation.extension D C E n hn S f c m K).hom =
      RZ.map e.hom.hom ≫ j.hom.app K := by
    simp only [FactorEvaluation.extension, e, j, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, eqToIso.hom, full_eqToHom]
    rfl
  have ht : (eqToHom (congrArg (fun F ↦ F.obj K)
        (congrArg₂ (· ⋙ ·) A.openExtension A.properPush)) :
        A.stage.properPush.obj M ⟶ (S.higher.integral.direct Q.p).obj M') =
      v.hom ≫ (S.higher.integral.direct Q.p).map e.hom := by
    simp only [v, e, eqToIso.hom, eqToHom_map, eqToHom_trans]
  change RY.map (ProjectionFactors.supportMap A K).hom ≫ _ = _
  rw [supportMap_normalized, ht, hv, he, P.map_comp]
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
  exact naturality_paste (RY.map v.hom.hom)
    (RY.map ((S.higher.integral.direct Q.p).map e.hom).hom)
    (RY.map (sigma.inv.app K).hom)
    (FactorEvaluation.support D C E n hn S f c m K).hom
    (d.hom.app M') (d.hom.app M) (P.map (RZ.map e.hom.hom))
    (P.map (j.hom.app K)) hd hcanonical

private theorem evaluation_paste
    {B₀ B₁ B₂ N₀ N₁ N₂ : Type*}
    [Category B₀] [Category B₁] [Category B₂]
    [Category N₀] [Category N₁] [Category N₂]
    (ev₀ : N₀ ⥤ B₀) (ev₁ : N₁ ⥤ B₁) (ev₂ : N₂ ⥤ B₂)
    (P : N₁ ⥤ N₂) (J : N₀ ⥤ N₁) (Pf : B₁ ⥤ B₂) (Jf : B₀ ⥤ B₁)
    (p : P ⋙ ev₂ ≅ ev₁ ⋙ Pf) (j : J ⋙ ev₁ ≅ ev₀ ⋙ Jf)
    {K : N₀} {M : N₁} {U : N₂} {Kf : B₀} {Mf : B₁} {Uf : B₂}
    (rhoK : ev₀.obj K ⟶ Kf) (rhoM : ev₁.obj M ⟶ Mf) (rhoU : ev₂.obj U ⟶ Uf)
    (d : U ⟶ P.obj M) (e : M ⟶ J.obj K)
    (df : Uf ⟶ Pf.obj Mf) (ef : Mf ⟶ Jf.obj Kf)
    (hd : ev₂.map d ≫ p.hom.app M ≫ Pf.map rhoM = rhoU ≫ df)
    (he : ev₁.map e ≫ j.hom.app K ≫ Jf.map rhoK = rhoM ≫ ef) :
    ev₂.map (d ≫ P.map e) ≫ p.hom.app (J.obj K) ≫
        Pf.map (j.hom.app K ≫ Jf.map rhoK) = rhoU ≫ df ≫ Pf.map ef := by
  have hnat := p.hom.naturality e
  dsimp only [Functor.comp_map] at hnat
  rw [ev₂.map_comp, Category.assoc, reassoc_of% hnat]
  rw [← Pf.map_comp, he, Pf.map_comp]
  simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ Pf.map ef) hd

/-- The support coefficient map is the paste of the proper direct-image mate
and the open coefficient map. This is a one-input statement with no tensor,
projection formula, or pullback compositor.

Source: prop-sf-pf-coherence.proof.md, compatibility with counits and j_!;
proof step 2 of lem-sf-integral-projection-open-factor-reduction, support sentence.
(blueprint: lem-sf-integral-projection-support-factor-coordinates).

Proof: transpose the proper/open composite through reduction/limit and then through
supportValue to get an actual integral morphism a between constructible objects. The
adjunction naturality identity proves reduction(a) followed by supportReduction is the
original composite. At each finite quotient, evaluate its proper and open factors
separately and paste by naturality of direct-image evaluation. The coefficient comparison
composition, properIdentity and openIdentification equations preserve the canonical
factored-support identification; finiteSupportFactorRealization gives its ambient finite
coordinates. integralSupportAdjunctFiniteCoordinates gives the same coordinates for
supportReduction. Cancel the coordinate isomorphisms to see that a and supportMap have
equal finite reductions. The proved Milnor joint-faithfulness theorem on constructible
integral objects gives their equality. Substitute it into the adjunction identity.
No faithfulness of evaluation on arbitrary derived systems is used. Identity factors,
empty opens and zero inputs satisfy the same naturality and adjunction identities. -/
theorem integralProjectionSupportFactorCoordinates
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    let A := S.higher.integralExchange (identitySquare f c)
    let r := ProjectionFactors.supportMap A K
    ProjectionFactors.directReduction D C E n hn S hl o z f c
        (A.stage.openExtension.obj K) ≫
      (Operations.push C.l E o c.g).map
        (ProjectionFactors.openReduction D C E n hn S hl o z f c K) =
      (calculus C.l E Y.obj.left).reduction.map r.hom ≫
        Coordinates.supportReduction D C E S.higher hl o z f c K := by
  let A := S.higher.integralExchange (identitySquare f c)
  let M := A.stage.openExtension.obj K
  let P := A.stage.properPush.obj M
  let U := (S.higher.integral.support f c).obj K
  let R := (calculus C.l E Y.obj.left).reduction
  let d := ProjectionFactors.directReduction D C E n hn S hl o z f c M
  let e := ProjectionFactors.openReduction D C E n hn S hl o z f c K
  let s := d ≫ (Operations.push C.l E o c.g).map e
  let V := Coordinates.supportValue D C E S.higher hl o z f c K
  let a : P ⟶ U := ObjectProperty.homMk
    (((calculus C.l E Y.obj.left).adjunction.homEquiv _ _) s ≫ V.hom)
  let r := ProjectionFactors.supportMap A K
  have ha : R.map a.hom ≫
      Coordinates.supportReduction D C E S.higher hl o z f c K = s :=
    adjunct_factor (calculus C.l E Y.obj.left).adjunction V s
  have har : a = r := by
    apply integral_reductions_jointly_faithful S Y
    intro m
    apply (intrinsicFiniteTorsionConstructible C.l E (m + 1)
      (Nat.le_add_left 1 m) Y.obj.left).ι.map_injective
    change (scalarReductionDerivedExtension C.l E Y.obj.left m).map a.hom =
      (scalarReductionDerivedExtension C.l E Y.obj.left m).map r.hom
    let ev := coefficientSequenceDerivedEvaluation C.l E Y.obj.left m
    let red := scalarReductionDerivedExtension C.l E Y.obj.left m
    let rho := (calculus C.l E Y.obj.left).reductionEvaluation m
    let Pf := proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing C.l E (m + 1))
    let Jf := (sfIntrinsicExtensionByZero c.i
      (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategory
    let q := (supportEvaluation C.l E o c m).app
        ((calculus C.l E X.obj.left).reduction.obj K.obj) ≪≫
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).mapIso
        (((calculus C.l E X.obj.left).reductionEvaluation m).app K.obj)
    let b := FactorEvaluation.support D C E n hn S f c m K
    apply finite_reflection R ev red rho s
      (Coordinates.supportReduction D C E S.higher hl o z f c K)
      a.hom r.hom q b ha
    · simpa only [q, b, FactorEvaluation.support, Iso.trans_hom, Functor.mapIso_hom,
        Iso.app_hom, Functor.mapIso_hom, Category.assoc, ObjectProperty.ι_map] using
        integralSupportAdjunctFiniteCoordinates D C E n hn S hl o z f c K m
    · have hp := evaluation_paste
        (coefficientSequenceDerivedEvaluation C.l E X.obj.left m)
        (coefficientSequenceDerivedEvaluation C.l E c.Z m) ev
        (Operations.push C.l E o c.g) (Operations.shriek C.l E o c.i) Pf Jf
        ((o.evaluation c.g).evaluation m) ((o.openEvaluation c.i).evaluation m)
        (((calculus C.l E X.obj.left).reductionEvaluation m).hom.app K.obj)
        (((calculus C.l E c.Z).reductionEvaluation m).hom.app M.obj)
        (rho.hom.app P.obj) d e
        (FactorEvaluation.direct D C E n hn S f c m M).hom
        (FactorEvaluation.extension D C E n hn S f c m K).hom
        (integralProjectionDirectFactorEvaluation D C E n hn S hl o z f c m M)
        (integralProjectionOpenFactorEvaluation D C E n hn S hl o z f c m K)
      have hf := finite_factor D C E n hn S f c m K
      rw [← Category.assoc, ← hf] at hp
      simpa only [q, s, supportEvaluation, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
        Functor.mapIso_hom, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
        Pf, Jf, sixFunctorFiniteSupport, sfIntrinsicCompactSupport,
        Functor.comp_map, Functor.map_comp, Category.assoc] using hp
  change s = R.map r.hom ≫ _
  rw [← har]
  exact ha.symm

end WeilConjectures.FixProjectionCompactification
