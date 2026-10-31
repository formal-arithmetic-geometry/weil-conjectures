/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationPresentationIso
import WeilConjectures.AlgebraicGeometry.Vector.VectorTraceGeometricDescent
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitPullback

/-! # Integration traces in arbitrary Cartesian bundle presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Modules
  Etale.vectorIntegrationCoefficient Etale.vectorIntegrationSource
  Etale.ordinaryFiniteSingleFunctor Etale.ordinaryFiniteDegreeZero
  CategoryTheory.constantSheaf

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  Etale.ordinaryFinitePullback._proof_1
  Etale.ordinaryFinitePullback._proof_2
  Etale.ordinaryFinitePullback._proof_3
  Etale.ordinaryFinitePullback._proof_4
  Etale.ordinaryFinitePullback._proof_5
  Etale.ordinaryFinitePullback._proof_6
  Etale.ordinaryFinitePullback._proof_7
  Etale.ordinaryFinitePullback._proof_8
  Etale.ordinaryFinitePullback._proof_9
  Etale.ordinaryFinitePullback._proof_10
  Etale.ordinaryFinitePullback._proof_11
  Etale.ordinaryFinitePullback._proof_12
  Etale.ordinaryFinitePullback._proof_13

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions Etale.upperStar Etale.lowerStar
  Etale.vectorBundleIntegration Etale.rightDerivedLowerShriek
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  DerivedCategory.singleFunctors HasDerivedCategory.ofIsGrothendieckAbelian
  VectorBundleZeroSection.scheme VectorBundleZeroSection.π VectorBundleZeroSection.over
  VectorBundleZeroSection.antiEquivalence Etale.leftDerivedUpperStarIsoMapDerivedCategory

private theorem comp_transport (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (w : h = f ≫ g) (K : Etale.DerivedCategoryModule A Z) :
    (eqToIso (congrArg (Etale.ordinaryFinitePullback A) w)).app K ≪≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).app K =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g h w).app K := by
  subst h
  apply Iso.ext
  exact Category.id_comp _

private theorem coefficient_paste (A : Type (u + 1)) [CommRing A]
    {X X' X'' S T : Scheme.{u}}
    {p : X ⟶ S} {q : X' ⟶ T} {r : X'' ⟶ T}
    {a : X' ⟶ X} {b : X'' ⟶ X'} {g : T ⟶ S} {z : X'' ⟶ X}
    (sq : IsPullback a q p g) (sz : IsPullback z r p g)
    (hb : b ≫ q = r) (hz : b ≫ a = z)
    (K : Etale.DerivedCategoryModule A S) (L : Etale.DerivedCategoryModule A T)
    (c : (RfPullback A g).obj K ≅ L) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b a z hz.symm).hom.app
        ((RfPullback A p).obj K) ≫
      (RfPullback A b).map
        (purityPullbackSquare A sq K ≪≫ (RfPullback A q).mapIso c).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b q r hb.symm).inv.app L =
    (purityPullbackSquare A sz K ≪≫ (RfPullback A r).mapIso c).hom := by
  have h₁ := Etale.leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} A) b a p z (a ≫ p) (z ≫ p) hz.symm rfl rfl K
  have h₂ := Etale.leftDerivedUpperStarComp_assoc'_app (ModuleCat.{u + 1} A)
    b q g r (a ≫ p) (z ≫ p) hb.symm sq.w sz.w K
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b q r hb.symm).inv.naturality
    c.hom
  simp only [Functor.comp_map] at hn
  simp only [purityPullbackSquare, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  dsimp only [RfPullback, Etale.ordinaryFinitePullback] at hn ⊢
  rw [hn, reassoc_of% h₁, reassoc_of% h₂]
  simp only [Iso.hom_inv_id_app_assoc]

private theorem exchange_paste_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {p'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (sq₁ : IsPullback v' p' p v) (sq₂ : IsPullback w' p'' p' w)
    (z : X'' ⟶ X) (c : Y'' ⟶ Y) (hz : z = w' ≫ v') (hc : c = w ≫ v)
    (sq : IsPullback z p'' p c) (K : Etale.DerivedCategoryModule A X) :
    (RfPullback A w).map ((Etale.rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (Etale.rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((RfPullback A v').obj K) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v c hc).inv.app _ ≫
        (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (RfShriek A p'').map
          ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hc
  exact Etale.affineLinearExchange_paste A sq₁ sq₂ K

private theorem trace_of_exchange_paste
    {C D E : Type*} [Category C] [Category D] [Category E]
    {H : C ⥤ D} {Q : C ⥤ E} {R : D ⥤ E} {J : E ⥤ E}
    (I : J ≅ 𝟭 E) (β : Q ⋙ J ⟶ H ⋙ R)
    {K L : C} {M N : D} {U V : E}
    (c : K ⟶ L) (c' : M ⟶ N) (a : M ⟶ H.obj K) (b : H.obj L ⟶ N)
    (x : U ⟶ Q.obj K) (y : U ⟶ R.obj M)
    (t : Q.obj L ⟶ V) (t' : R.obj N ⟶ V)
    (hp : J.map x ≫ β.app K = I.hom.app U ≫ y ≫ R.map a)
    (hc : a ≫ H.map c ≫ b = c')
    (ht : I.inv.app (Q.obj L) ≫ β.app L ≫ R.map b ≫ t' = t) :
    y ≫ R.map c' ≫ t' = x ≫ Q.map c ≫ t := by
  have hn := I.inv.naturality (Q.map c)
  have hx := I.inv.naturality x
  have hb := β.naturality c
  dsimp only [Functor.id_map] at hn hx
  dsimp only [Functor.comp_map] at hb
  rw [← ht]
  rw [reassoc_of% hn, reassoc_of% hb, reassoc_of% hx, reassoc_of% hp]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, hc]

/-- The scalar integration trace is preserved in every Cartesian presentation.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2, equality of integrations before transposition.
(blueprint: lem-pur-vector-integration-cartesian-trace).

Proof: first use vectorBundleIntegration_baseChange for the canonical tensor-pullback bundle.
The universal property of the two Cartesian squares identifies any other presentation with
that bundle over the new base. The top compact-support trace is invariant under this
isomorphism: on each geometric fibre it is the degree map on top compact-support cohomology,
and an isomorphism has degree one. Both trace sources are degree-zero sheaves, so geometric
stalks detect their equality. The normalized Tate pullback comparison and the composition
comparisons identify the coefficient map with the displayed one. Compact-support exchange
pastes with the presentation isomorphism, giving the formula. Finally the canonical map
from the degree-zero constant coefficient to the tensor unit commutes with pullback.
For rank zero these are unit comparisons; over an empty base there is only one map.
This statement contains no exceptional inverse image or purity family.
-/
theorem vectorIntegration_cartesianTrace
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {B B' : Scheme.{u}} [IsNoetherian B] [IsNoetherian B']
    (hB : IsUnit (N : Γ(B, ⊤))) (hB' : IsUnit (N : Γ(B', ⊤)))
    (d : ℕ) (F : B.Modules) (F' : B'.Modules)
    [F.IsFiniteLocallyFreeOfRank d] [F'.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    [HasCompactification (VectorBundleZeroSection.π B' d F')]
    [QuasiCompact (VectorBundleZeroSection.π B' d F')]
    {g : B' ⟶ B}
    {g' : VectorBundleZeroSection.scheme B' d F' ⟶ VectorBundleZeroSection.scheme B d F}
    (sq : IsPullback g' (VectorBundleZeroSection.π B' d F')
      (VectorBundleZeroSection.π B d F) g) :
    let l := purityPullbackSquare A sq (Etale.affineLinearBaseCoefficient A N hA B d) ≪≫
      (RfPullback A (VectorBundleZeroSection.π B' d F')).mapIso
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA
          (purityTwistTransport A N hN hA) g hB d)
    (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app
        (Etale.vectorIntegrationCoefficient A N hA B d F) ≫
      (RfShriek A (VectorBundleZeroSection.π B' d F')).map l.hom ≫
      (Etale.vectorBundleIntegration N hN A hA B' hB' d F' ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat A) B').hom) =
    (RfPullback A g).map (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
      (Etale.singleFunctorObjUnitIso (ModuleCat A) B).hom) ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat A) g).hom := by
  let F₀ := (Scheme.Modules.tensorPullback g).obj F
  let p := VectorBundleZeroSection.π B d F
  let q := VectorBundleZeroSection.π B' d F₀
  let r := VectorBundleZeroSection.π B' d F'
  let a := VectorTraceGeometry.baseChange g d F
  let s₀ := VectorTraceGeometry.baseChange_isPullback g d F
  let e := sq.isoIsPullback _ _ s₀
  have he : e.hom ≫ q = r := IsPullback.isoIsPullback_hom_snd _ _ sq s₀
  have hz : e.hom ≫ a = g' := IsPullback.isoIsPullback_hom_fst _ _ sq s₀
  have se : IsPullback e.hom r q (𝟙 B') :=
    IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  let K := Etale.affineLinearBaseCoefficient A N hA B d
  let L := Etale.affineLinearBaseCoefficient A N hA B' d
  let c := Etale.vectorIntegrationBaseCoefficientPullback A N hA
    (purityTwistTransport A N hN hA) g hB d
  let c₀ := purityPullbackSquare A s₀ K ≪≫ (RfPullback A q).mapIso c
  let c' := purityPullbackSquare A sq K ≪≫ (RfPullback A r).mapIso c
  let ce := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    e.hom q r he.symm).inv.app L
  let t₀ := Etale.vectorBundleIntegration N hN A hA B' hB' d F₀
  let t' := Etale.vectorBundleIntegration N hN A hA B' hB' d F'
  let E₀ := (Etale.rightDerivedLowerShriekBaseChangeMap A s₀).app
    (Etale.vectorIntegrationCoefficient A N hA B d F)
  let E' := (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app
    (Etale.vectorIntegrationCoefficient A N hA B d F)
  let I := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} A) B'
  have hc₀ : Etale.vectorTraceCoefficientBaseChange A N hA
      (purityTwistTransport A N hN hA) g hB d F = c₀ := by
    unfold Etale.vectorTraceCoefficientBaseChange c₀ purityPullbackSquare
    rw [← comp_transport A q g (a ≫ p) s₀.w K]
    simp only [Iso.trans_assoc]
    rfl
  have hbase : E₀ ≫ (RfShriek A q).map c₀.hom ≫ t₀ =
      (RfPullback A g).map (Etale.vectorBundleIntegration N hN A hA B hB d F) ≫
        (Etale.ordinaryFiniteUnitPullback A g).hom := by
    simpa only [hc₀] using Etale.vectorBundleIntegration_baseChange N hN A hA
      (purityTwistTransport A N hN hA) g hB d F
  have hiso := Etale.vectorIntegration_presentationIso N hN A hA B' hB' d F₀ F' e he se
  change I.inv.app _ ≫ (Etale.rightDerivedLowerShriekBaseChangeMap A se).app _ ≫
    (RfShriek A r).map ce ≫ t' = t₀ at hiso
  have hcoeff := coefficient_paste A s₀ sq he hz K L c
  dsimp only [RfPullback, Etale.ordinaryFinitePullback] at hcoeff
  have hpaste := exchange_paste_named A s₀ se g' g hz.symm
    (Category.id_comp g).symm sq (Etale.vectorIntegrationCoefficient A N hA B d F)
  have hunit : (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 B') g g (Category.id_comp g).symm).inv.app
        ((RfShriek A p).obj (Etale.vectorIntegrationCoefficient A N hA B d F)) =
        I.hom.app _ := by
    apply (cancel_epi ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
      (𝟙 B') g g (Category.id_comp g).symm).hom.app _)).mp
    simpa only [Iso.hom_inv_id_app] using
      (Etale.leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} A) g
        ((RfShriek A p).obj (Etale.vectorIntegrationCoefficient A N hA B d F))).symm
  rw [hunit] at hpaste
  have htrace : E' ≫ (RfShriek A r).map c'.hom ≫ t' =
      E₀ ≫ (RfShriek A q).map c₀.hom ≫ t₀ :=
    trace_of_exchange_paste
      (H := (Etale.upperStar (ModuleCat.{u + 1} A) e.hom).leftDerivedFunctor)
      I (Etale.rightDerivedLowerShriekBaseChangeMap A se) c₀.hom c'.hom
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        e.hom a g' hz.symm).hom.app (Etale.vectorIntegrationCoefficient A N hA B d F))
      ce E₀ E' t₀ t' hpaste hcoeff hiso
  have h := congrArg (fun k ↦ k ≫
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B').hom) (htrace.trans hbase)
  simpa only [Functor.map_comp, Category.assoc, Etale.ordinaryFiniteSingleUnitPullback_hom] using h

end WeilConjectures.PurityFiniteSetting
