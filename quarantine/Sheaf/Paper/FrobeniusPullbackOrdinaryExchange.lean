/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Paper.IsomorphismFieldTransport
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PullbackIdentitiesScalarExtension
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import Sheaf.Paper.AutomorphismConstructibleStageEquivalence
import Sheaf.Paper.IntegralComparisonCompositionReduction
import Sheaf.Paper.AutomorphismSquareRationalScalar

/-! # The normalized automorphism square and ordinary exchange

Source: blueprint prop-weil-operations.proof.md, sentence 1, via
lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange).

The comparisons below use the completed integral, raw rational and actual common-stage
operations. Full operation domains remain explicit. No Weil structure is put on an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective



universe u v a b c d
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Aut

namespace WeilConjectures
namespace OrdinaryAutomorphismSquare
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion ofHom)

/-- Restriction to a supplied full operation domain, with its actual arrow action.
Source: blueprint def-exchange-projection, supplied-domain paragraph
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def onDomain {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (h : ∀ K : P.FullSubcategory, Q (F.obj K.obj)) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) h

/-- Restrict the prescribed square, rather than choosing a new comparison.
Source: blueprint pullback square on supplied domains
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def onDomainSquare {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : C ⥤ D) (G : C ⥤ C) (H : D ⥤ D) (α : F ⋙ H ≅ G ⋙ F)
    (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj))
    (hH : ∀ K : Q.FullSubcategory, Q (H.obj K.obj)) :
    onDomain P Q F hF ⋙ onDomain Q Q H hH ≅
      onDomain P P G hG ⋙ onDomain P Q F hF :=
  NatIso.ofComponents (fun K ↦ Q.isoMk (α.app K.obj))
    (fun r ↦ ObjectProperty.hom_ext Q (α.hom.naturality r.hom))

/-- Ordinary exchange on every supplied closed full domain, including the displayed
unit--inverse-square--counit formula. Inverse horizontal pullbacks must preserve the same
domains, as required by the node's stipulation that all displayed operations preserve them.
`R,adj` are the supplied ordinary direct image and its ordinary adjunction; the assertion
applies to every supplied normalization, and never replaces them by a chosen adjoint.
Source: blueprint def-exchange-projection and fix-prop-adjunctions(1)
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def ExchangeOnDomains {C : Type a} {D : Type b} [Category.{c} C] [Category.{d} D]
    (F : C ⥤ D) (G Ginv : C ⥤ C) (H Hinv : D ⥤ D) (α : F ⋙ H ≅ G ⋙ F) : Prop :=
  ∀ (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ K : P.FullSubcategory, Q (F.obj K.obj))
    (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj))
    (_hGinv : ∀ K : P.FullSubcategory, P (Ginv.obj K.obj))
    (hH : ∀ K : Q.FullSubcategory, Q (H.obj K.obj))
    (_hHinv : ∀ K : Q.FullSubcategory, Q (Hinv.obj K.obj))
    (R : Q.FullSubcategory ⥤ P.FullSubcategory) (adj : onDomain P Q F hF ⊣ R),
    IsIso (mateEquiv adj adj (onDomainSquare P Q F G H α hF hG hH).inv).natTrans ∧
    ∀ K : Q.FullSubcategory,
      (mateEquiv adj adj (onDomainSquare P Q F G H α hF hG hH).inv).natTrans.app K =
        adj.unit.app ((onDomain P P G hG).obj (R.obj K)) ≫
          R.map ((onDomainSquare P Q F G H α hF hG hH).inv.app (R.obj K)) ≫
          R.map ((onDomain Q Q H hH).map (adj.counit.app K))

/-- Exact horizontal transport with the actual inverse pullback, in either field category.
Source: blueprint inverse automorphism square and lem-pod-isomorphism-field-transport
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
structure ExactInverse {C : Type a} [Category.{b} C] [HasZeroObject C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P Q : C ⥤ C) where
  equivalence : P.IsEquivalence
  shift : P.CommShift ℤ
  exact : (fun [_s : P.CommShift ℤ] ↦ P.IsTriangulated) (_s := shift)
  counit : P ⋙ Q ≅ 𝟭 C
  inverseCounit : Q ⋙ P ≅ 𝟭 C

private def restrictCancellation {C : Type a} [Category.{b} C]
    (P : ObjectProperty C) (G H : C ⥤ C) (e : G ⋙ H ≅ 𝟭 C)
    (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj))
    (hH : ∀ K : P.FullSubcategory, P (H.obj K.obj)) :
    onDomain P P G hG ⋙ onDomain P P H hH ≅ 𝟭 P.FullSubcategory :=
  NatIso.ofComponents (fun K ↦ P.isoMk (e.app K.obj))
    (fun r ↦ ObjectProperty.hom_ext P (e.hom.naturality r.hom))

private theorem restrictedEquivalence {C : Type a} [Category.{b} C]
    (P : ObjectProperty C) (G H : C ⥤ C)
    (e : G ⋙ H ≅ 𝟭 C) (e' : H ⋙ G ≅ 𝟭 C)
    (hG : ∀ K : P.FullSubcategory, P (G.obj K.obj))
    (hH : ∀ K : P.FullSubcategory, P (H.obj K.obj)) :
    (onDomain P P G hG).IsEquivalence :=
  Functor.IsEquivalence.mk' (onDomain P P H hH)
    (restrictCancellation P G H e hG hH).symm
    (restrictCancellation P H G e' hH hG)

private theorem exchangeOnDomains {C : Type a} {D : Type b}
    [Category.{c} C] [Category.{d} D]
    (F : C ⥤ D) (G Ginv : C ⥤ C) (H Hinv : D ⥤ D) (α : F ⋙ H ≅ G ⋙ F)
    (eG : G ⋙ Ginv ≅ 𝟭 C) (eG' : Ginv ⋙ G ≅ 𝟭 C)
    (eH : H ⋙ Hinv ≅ 𝟭 D) (eH' : Hinv ⋙ H ≅ 𝟭 D) :
    ExchangeOnDomains F G Ginv H Hinv α := by
  intro P Q hF hG hGinv hH hHinv R adj
  let _ := restrictedEquivalence P G Ginv eG eG' hG hGinv
  let _ := restrictedEquivalence Q H Hinv eH eH' hH hHinv
  refine ⟨isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj
    (onDomain P P G hG) (onDomain Q Q H hH)
    (onDomainSquare P Q F G H α hF hG hH).symm, ?_⟩
  intro K
  simp [mateEquiv]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Compose comparisons in a full category using their actual component arrows.
Source: the component expansion of the original integral square
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def comparisonSquare {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) {I : Type*} (F : I → A ⥤ P.FullSubcategory)
    {i j : I} (w : i = j) {G H : A ⥤ P.FullSubcategory}
    (c : F i ≅ G) (d : F j ≅ H) : G ≅ H :=
  NatIso.ofComponents (fun K ↦
    (c.app K).symm ≪≫ P.isoMk
      (eqToIso (congrArg (fun t ↦ ((F t).obj K).obj) w)) ≪≫ d.app K)
    (by
      subst j
      intro K J r
      change G.map r ≫ (c.inv.app J ≫ 𝟙 _ ≫ d.hom.app J) =
        (c.inv.app K ≫ 𝟙 _ ≫ d.hom.app K) ≫ H.map r
      simpa only [Category.id_comp, Category.assoc, NatTrans.comp_app,
        Iso.trans_hom, Iso.symm_hom] using (c.symm ≪≫ d).hom.naturality r)

private theorem comparisonSquare_eq {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) {I : Type*} (F : I → A ⥤ P.FullSubcategory)
    {i j : I} (w : i = j) {G H : A ⥤ P.FullSubcategory}
    (c : F i ≅ G) (d : F j ≅ H) :
    comparisonSquare P F w c d = c.symm ≪≫ eqToIso (congrArg F w) ≪≫ d := by
  subst j
  apply Iso.ext
  apply NatTrans.ext
  funext K
  change c.inv.app K ≫ 𝟙 _ ≫ d.hom.app K =
    c.inv.app K ≫ 𝟙 _ ≫ d.hom.app K
  rfl

/-- The integral square is exactly inverse c(gX,f), the equality of the composite
scheme maps, then c(f,gY). No reductions are used to select this map.
Source: blueprint pullback square, node proof step 1
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def integralSquare (C : IntegralPullbackCompositionFamily l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E gX ≅
      constructibleIntegralPullback l E gY ⋙ constructibleIntegralPullback l E f :=
  comparisonSquare (sfIntegralConstructible l E X)
    (fun h : X ⟶ Y ↦ constructibleIntegralPullback l E h)
    w (C gX f) (C f gY)

private def normalizedCompositor (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S) : IntegralPullbackCompositionFamily l E :=
  fun {_ _ _} _ _ _ h k ↦ NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (integralComparisonComposition l E S h k K))
    (fun r ↦ ObjectProperty.hom_ext _ (hS.naturality h k _ _ r))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem square_paste {C D : Type*} [Category C] [Category D] {I : Type*}
    (T : C ⥤ D) (A : I → C) (B : I → D) (ρ : ∀ i, T.obj (A i) ≅ B i)
    {i j : I} (w : i = j) {U V : C} {U' V' : D}
    (c : A i ≅ U) (d : A j ≅ V) (c' : B i ≅ U') (d' : B j ≅ V')
    (rU : T.obj U ≅ U') (rV : T.obj V ≅ V')
    (hc : T.map c.hom ≫ rU.hom = (ρ i).hom ≫ c'.hom)
    (hd : T.map d.hom ≫ rV.hom = (ρ j).hom ≫ d'.hom) :
    T.map (c.inv ≫ eqToHom (congrArg A w) ≫ d.hom) ≫ rV.hom =
      rU.hom ≫ c'.inv ≫ eqToHom (congrArg B w) ≫ d'.hom := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp]
  apply (cancel_epi (T.map c.hom)).1
  simp only [← Category.assoc, ← T.map_comp, Iso.hom_inv_id,
    Category.id_comp]
  rw [Category.assoc, hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hd

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralDerivedPullback integralComparisonComposition
  integralPullbackReductionIso integralFiniteCanonicalPullbackComposition
  scalarReductionDerivedExtension proEtaleConstantRingDerivedPullback
  AlgebraicGeometry.Scheme.residueField completedIntegralCoefficientSheafUnrestricted

private theorem fullSquare_component {A B : Type*} [Category A] [Category B]
    (P : ObjectProperty B) {I : Type*} (F : I → A ⥤ P.FullSubcategory)
    {i j : I} (w : i = j) {G H : A ⥤ P.FullSubcategory}
    (c : F i ≅ G) (d : F j ≅ H) (K : A) :
    (((comparisonSquare P F w c d).hom.app K).hom) =
      (c.inv.app K).hom ≫
        eqToHom (congrArg (fun t ↦ ((F t).obj K).obj) w) ≫ (d.hom.app K).hom := by
  rfl

private theorem integralSquare_component (C : IntegralPullbackCompositionFamily l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    ((integralSquare l E C f gX gY w).hom.app K).hom =
      ((C gX f).inv.app K).hom ≫
        eqToHom (congrArg (fun h ↦ ((constructibleIntegralPullback l E h).obj K).obj) w) ≫
        ((C f gY).hom.app K).hom := by
  exact fullSquare_component (sfIntegralConstructible l E X)
    (fun h : X ⟶ Y ↦ constructibleIntegralPullback l E h) w (C gX f) (C f gY) K

private theorem normalizedSquare_component (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y) :
    ((integralSquare l E (normalizedCompositor l E S hS) f gX gY w).hom.app K).hom =
      (integralComparisonComposition l E S gX f K).inv ≫
        eqToHom (congrArg (fun h ↦ (integralDerivedPullback l E h).obj K.obj) w) ≫
        (integralComparisonComposition l E S f gY K).hom := by
  rw [integralSquare_component]
  rfl

set_option backward.isDefEq.respectTransparency.types true in
private theorem normalizedSquare_eq (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    integralSquare l E (normalizedCompositor l E S hS) f gX gY w =
      automorphismStageIntegralSquare l E S f (asIso gY) (asIso gX) w := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  exact (normalizedSquare_component l E S hS f gX gY w K).trans
    ((automorphismStageIntegralSquare_existsUnique l E S f
      (asIso gY) (asIso gX) w).exists.choose_spec K).symm

/-- The componentwise equality square in an arbitrary functor category.
Source: expansion of the original finite square
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def functorComparisonSquare {A B : Type*} [Category A] [Category B] {I : Type*}
    (F : I → A ⥤ B) {i j : I} (w : i = j) {G H : A ⥤ B}
    (c : F i ≅ G) (d : F j ≅ H) : G ≅ H :=
  NatIso.ofComponents
    (fun K ↦ (c.app K).symm ≪≫ eqToIso (congrArg (fun t ↦ (F t).obj K) w) ≪≫ d.app K)
    (by
      subst j
      intro K J r
      simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom,
        Iso.app_hom, Iso.app_inv, NatTrans.comp_app] using (c.symm ≪≫ d).hom.naturality r)

private theorem functorComparisonSquare_eq {A B : Type*} [Category A] [Category B]
    {I : Type*} (F : I → A ⥤ B) {i j : I} (w : i = j) {G H : A ⥤ B}
    (c : F i ≅ G) (d : F j ≅ H) :
    functorComparisonSquare F w c d = c.symm ≪≫ eqToIso (congrArg F w) ≪≫ d := by
  subst j
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [functorComparisonSquare, NatIso.ofComponents_hom_app, eqToIso_refl,
    Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app]

/-- The finite square uses precisely the published finite constant-ring compositors.
The natural number n means the positive exponent n+1.
Source: Stacks 0D6D, node proof step 1
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def finiteSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) (n : ℕ) :
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gX ≅
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gY ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f :=
  functorComparisonSquare
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))) w
    (integralFiniteCanonicalPullbackComposition l E gX f n)
    (integralFiniteCanonicalPullbackComposition l E f gY n)

/-- The composite scalar comparison A (or B) is alpha for h, followed by h-star of
alpha for k, with the existing completed scalar extension at each endpoint.
Source: blueprint scalar square, node proof step 2
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def scalarComposite
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfIntegralConstructibleCategory l E V) :=
  integralPullbackScalarComparison l E L ι h ((constructibleIntegralPullback l E k).obj K) ≪≫
    (constructibleIntegralPullback l L h).mapIso (integralPullbackScalarComparison l E L ι k K)

/-- The one-field clauses retain the whole-system normalization of both compositors,
finite reductions, exact inverse transports, the raw rational component, and exchange
on the original supplied domains. Naturality of rational isomorphisms ranges over every
localized morphism, hence every sum of pure tensors and every balancing relation.
Source: blueprint pullback and ordinary exchange, node proof steps 1, 3, 5, 6
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
structure Stage (S : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] where
  compositor : IntegralPullbackCompositionFamily l E
  composition_left : ∀ K : sfIntegralConstructibleCategory l E Y,
    ((compositor gX f).hom.app K).hom =
      (integralComparisonComposition l E S gX f K).hom
  composition_right : ∀ K : sfIntegralConstructibleCategory l E Y,
    ((compositor f gY).hom.app K).hom =
      (integralComparisonComposition l E S f gY K).hom
  reduction : ∀ (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (d : DerivedCategory.Q.obj Q.obj ≅ ((constructibleIntegralPullback l E f).obj K).obj)
    (R : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (r : DerivedCategory.Q.obj R.obj ≅ ((constructibleIntegralPullback l E gY).obj K).obj)
    (n : ℕ),
    (scalarReductionDerivedExtension l E X n).map
        ((integralSquare l E compositor f gX gY w).hom.app K).hom ≫
        (integralPullbackReductionIso l E f
          ((constructibleIntegralPullback l E gY).obj K) R r n).hom ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
          (integralPullbackReductionIso l E gY K P e n).hom =
      (integralPullbackReductionIso l E gX
        ((constructibleIntegralPullback l E f).obj K) Q d n).hom ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) gX).map
          (integralPullbackReductionIso l E f K P e n).hom ≫
        (finiteSquare l E f gX gY w n).hom.app
          ((scalarReductionDerivedExtension l E Y n).obj K.obj)
  rational : rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E gX ≅
    rationalDerivedPullback l E gY ⋙ rationalDerivedPullback l E f
  rational_formula : ∀ K : sfRationalConstructibleCategory l E Y,
    HEq (rational.hom.app K) ((sfRationalConstructibleLocalization l E X).map
      ((integralSquare l E compositor f gX gY w).hom.app K.obj))
  transportX : ExactInverse (rationalDerivedPullback l E gX)
    (rationalDerivedPullback l E (inv gX))
  transportY : ExactInverse (rationalDerivedPullback l E gY)
    (rationalDerivedPullback l E (inv gY))
  exchange : ExchangeOnDomains (rationalDerivedPullback l E f)
    (rationalDerivedPullback l E gY) (rationalDerivedPullback l E (inv gY))
    (rationalDerivedPullback l E gX) (rationalDerivedPullback l E (inv gX)) rational

end OrdinaryAutomorphismSquare
end WeilConjectures

namespace WeilConjectures.OrdinaryAutomorphismSquare
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion ofHom)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Rationalization of the composite scalar comparison, in the published raw categories.
Source: blueprint scalar square after rationalization, node proof steps 2--3
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def rationalScalarComposite
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E V) :=
  (rationalPullbackScalarComparison l E L ι h).app ((rationalDerivedPullback l E k).obj K) ≪≫
    (rationalDerivedPullback l L h).mapIso ((rationalPullbackScalarComparison l E L ι k).app K)

/-- The equation B T(a_E) = a_L A, written in Lean's left-to-right composition order,
both before and after raw rationalization. This includes identity extensions.
Source: blueprint scalar square, node proof steps 2--3
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def ScalarLaw (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (S : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SE : Stage l E S f gX gY w) (SL : Stage l L S f gX gY w) : Prop :=
  (∀ K : sfIntegralConstructibleCategory l E Y,
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
        E L ι X).map ((integralSquare l E SE.compositor f gX gY w).hom.app K) ≫
        (scalarComposite l E L ι f gY K).hom =
      (scalarComposite l E L ι gX f K).hom ≫
        (integralSquare l L SL.compositor f gX gY w).hom.app
          ((sfConstructibleIntegralScalarExtension 0 l
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj K)) ∧
  (∀ K : sfRationalConstructibleCategory l E Y,
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        (SE.rational.hom.app K) ≫ (rationalScalarComposite l E L ι f gY K).hom =
      (rationalScalarComposite l E L ι gX f K).hom ≫
        SL.rational.hom.app ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj K))

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The literal common-stage object of a composite pullback.
Source: blueprint common-stage arrow calculation, node proof step 4
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def commonCompositeObject {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω V) :=
  commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω k K)

/-- The comparison conjugating a composite operation on a common-field representative.
Source: blueprint common-stage arrow calculation, node proof step 4
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def commonCompositeComparison {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω V)
    (L : Index l Ω) (hK : K.stage ≤ L) :=
  commonStagePullbackComparison l Ω h (commonStagePullbackObject l Ω k K) L hK ≪≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) h).mapIso
      (commonStagePullbackComparison l Ω k K L hK)

/-- The actual common-stage composite acts by A_target inverse, F_L(u), A_source.
Because the left side is a functor on the quotient Hom type, this also asserts
independence of representatives and further-field enlargement, including identity stages.
Source: blueprint common-stage arrow calculation, node proof step 4
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
def CommonCompositeArrowLaw {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)] : Prop :=
  ∀ (K J : generalAlgebraicallyClosedConstructibleCategory l Ω V)
    (L : Index l Ω) (hK : K.stage ≤ L) (hJ : J.stage ≤ L)
    (r : K.toStage hK ⟶ J.toStage hJ),
    HEq ((commonStageDerivedPullback l Ω k ⋙ commonStageDerivedPullback l Ω h).map
      (ofHom K J L hK hJ r))
      (ofHom (commonCompositeObject l Ω h k K) (commonCompositeObject l Ω h k J) L hK hJ
        ((commonCompositeComparison l Ω h k K L hK).hom ≫
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) h).map
            ((rationalDerivedPullback l (Coefficient.{u} l Ω L) k).map r) ≫
          (commonCompositeComparison l Ω h k J L hJ).inv))

private theorem map_heq {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem composite_arrows {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)] :
    CommonCompositeArrowLaw l Ω h k := by
  intro K J L hK hJ r
  have hk := (commonStageDerivedPullback_existsUnique l Ω k).exists.choose_spec
  have hh := (commonStageDerivedPullback_existsUnique l Ω h).exists.choose_spec
  refine (map_heq (commonStageDerivedPullback l Ω h) (hk.1 K) (hk.1 J)
    (hk.2 K J L hK hJ r)).trans ?_
  refine (hh.2 (commonStagePullbackObject l Ω k K)
    (commonStagePullbackObject l Ω k J) L hK hJ _).trans ?_
  apply heq_of_eq
  apply congrArg (ofHom (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω k K))
    (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω k J)) L hK hJ)
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  simp only [commonCompositeComparison, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

/-- The common-stage comparison is precisely the class of the rationalized integral
component. Its naturality covers arbitrary quotient arrows; the two arrow laws retain
exactly the A and B conjugations. The horizontal inverses are the actual inverse pullbacks.
Source: blueprint field stages and ordinary exchange, node proof steps 4--6
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange). -/
structure Common (S : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (SE : ∀ E : Index l Ω, Stage l (Coefficient.{u} l Ω E) S f gX gY w) where
  comparison : commonStageDerivedPullback l Ω f ⋙ commonStageDerivedPullback l Ω gX ≅
    commonStageDerivedPullback l Ω gY ⋙ commonStageDerivedPullback l Ω f
  component : ∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
    HEq (comparison.hom.app K)
      ((inclusion (Y := X) K.stage).map ((SE K.stage).rational.hom.app K.obj))
  left_arrows : CommonCompositeArrowLaw l Ω gX f
  right_arrows : CommonCompositeArrowLaw l Ω f gY
  transportX : ExactInverse (commonStageDerivedPullback l Ω gX)
    (commonStageDerivedPullback l Ω (inv gX))
  transportY : ExactInverse (commonStageDerivedPullback l Ω gY)
    (commonStageDerivedPullback l Ω (inv gY))
  exchange : ExchangeOnDomains (commonStageDerivedPullback l Ω f)
    (commonStageDerivedPullback l Ω gY) (commonStageDerivedPullback l Ω (inv gY))
    (commonStageDerivedPullback l Ω gX) (commonStageDerivedPullback l Ω (inv gX)) comparison

set_option allowUnsafeReducibility true in
attribute [local irreducible] rationalDerivedPullback commonStageDerivedPullback

private def rationalExactInverse {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    (hX hX' : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (S : IsomorphismFieldTransportStage l E g hX hX')
    (R : IsomorphismFieldTransportStage l E (inv g) hX' hX) :
    ExactInverse (rationalDerivedPullback l E g) (rationalDerivedPullback l E (inv g)) where
  equivalence := S.rationalEquivalence
  shift := S.rationalShift
  exact := S.rationalExact
  counit := S.rationalEpsilon
  inverseCounit := by
    have hb := R.rationalEpsilon
    rw [IsIso.inv_inv] at hb
    exact hb

private def commonExactInverse {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    (hX hX' : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (S : ∀ E : Index l Ω, IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) g hX hX')
    (R : ∀ E : Index l Ω,
      IsomorphismFieldTransportStage l (Coefficient.{u} l Ω E) (inv g) hX' hX)
    (s : IsomorphismFieldTransportCommon l Ω g hX hX' S)
    (r : IsomorphismFieldTransportCommon l Ω (inv g) hX' hX R) :
    ExactInverse (commonStageDerivedPullback l Ω g)
      (commonStageDerivedPullback l Ω (inv g)) where
  equivalence := s.equivalence
  shift := s.shift
  exact := s.exact
  counit := s.epsilon
  inverseCounit := by
    have hb := r.epsilon
    rw [IsIso.inv_inv] at hb
    exact hb

private theorem rationalSquare_component (S : IntegralComparisonSystem.{u} l)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    HEq ((automorphismStageRationalSquare l E S f (asIso gY) (asIso gX) w).hom.app K)
      ((sfRationalConstructibleLocalization l E X).map
        ((automorphismStageIntegralSquare l E S f (asIso gY) (asIso gX) w).hom.app K.obj)) :=
  (automorphismStageRationalSquare_existsUnique l E S f
    (asIso gY) (asIso gX) w).exists.choose_spec K

set_option backward.isDefEq.respectTransparency.types true in
private theorem normalizedStage_reduction (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∀ (K : sfIntegralConstructibleCategory l E Y)
      (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
      (Q : (integralOperationsGoodComplex l E X).FullSubcategory)
      (d : DerivedCategory.Q.obj Q.obj ≅ ((constructibleIntegralPullback l E f).obj K).obj)
      (R : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (r : DerivedCategory.Q.obj R.obj ≅ ((constructibleIntegralPullback l E gY).obj K).obj)
      (n : ℕ),
      (scalarReductionDerivedExtension l E X n).map
          ((integralSquare l E (normalizedCompositor l E S hS) f gX gY w).hom.app K).hom ≫
        (integralPullbackReductionIso l E f
          ((constructibleIntegralPullback l E gY).obj K) R r n).hom ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
          (integralPullbackReductionIso l E gY K P e n).hom =
      (integralPullbackReductionIso l E gX
        ((constructibleIntegralPullback l E f).obj K) Q d n).hom ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) gX).map
          (integralPullbackReductionIso l E f K P e n).hom ≫
        (finiteSquare l E f gX gY w n).hom.app
          ((scalarReductionDerivedExtension l E Y n).obj K.obj) := by
    intro K P e Q d R r n
    let ρ (t : X ⟶ Y) := integralPullbackReductionIso l E t K P e n
    let T := scalarReductionDerivedExtension l E X n
    let A (t : X ⟶ Y) := (integralDerivedPullback l E t).obj K.obj
    let B (t : X ⟶ Y) := (proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) t).obj
        ((scalarReductionDerivedExtension l E Y n).obj K.obj)
    let rU := integralPullbackReductionIso l E gX
      ((constructibleIntegralPullback l E f).obj K) Q d n ≪≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) gX).mapIso
          (integralPullbackReductionIso l E f K P e n)
    let rV := integralPullbackReductionIso l E f
      ((constructibleIntegralPullback l E gY).obj K) R r n ≪≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).mapIso
          (integralPullbackReductionIso l E gY K P e n)
    have hc := integralComparisonComposition_reduction l E S gX f K P e Q d n
    have hd := integralComparisonComposition_reduction l E S f gY K P e R r n
    have hh := square_paste T A B ρ w
      (integralComparisonComposition l E S gX f K)
      (integralComparisonComposition l E S f gY K)
      ((integralFiniteCanonicalPullbackComposition l E gX f n).app
        ((scalarReductionDerivedExtension l E Y n).obj K.obj))
      ((integralFiniteCanonicalPullbackComposition l E f gY n).app
        ((scalarReductionDerivedExtension l E Y n).obj K.obj)) rU rV
      (by
        set_option backward.isDefEq.respectTransparency false in
        simpa only [T, A, ρ, rU, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Functor.comp_obj, Category.assoc] using hc)
      (by
        set_option backward.isDefEq.respectTransparency false in
        simpa only [T, A, ρ, rV, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
          Functor.comp_obj, Category.assoc] using hd)
    rw [normalizedSquare_component]
    set_option backward.isDefEq.respectTransparency false in
    simpa only [T, A, B, rU, rV,
      finiteSquare, functorComparisonSquare, NatIso.ofComponents_hom_app,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToHom_app,
      Functor.mapIso_hom, Category.assoc, Functor.comp_obj] using hh

private def normalizedStage (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (TX : ExactInverse (rationalDerivedPullback l E gX)
      (rationalDerivedPullback l E (inv gX)))
    (TY : ExactInverse (rationalDerivedPullback l E gY)
      (rationalDerivedPullback l E (inv gY))) : Stage l E S f gX gY w :=
  { compositor := normalizedCompositor l E S hS
    composition_left := fun _ ↦ rfl
    composition_right := fun _ ↦ rfl
    reduction := normalizedStage_reduction l E S hS f gX gY w
    rational := automorphismStageRationalSquare l E S f (asIso gY) (asIso gX) w
    rational_formula := by
      intro K
      rw [normalizedSquare_eq]
      exact rationalSquare_component l E S f gX gY w K
    transportX := TX
    transportY := TY
    exchange := exchangeOnDomains _ _ _ _ _ _ TY.counit TY.inverseCounit
      TX.counit TX.inverseCounit }

private theorem normalizedStage_compositor (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (TX : ExactInverse (rationalDerivedPullback l E gX)
      (rationalDerivedPullback l E (inv gX)))
    (TY : ExactInverse (rationalDerivedPullback l E gY)
      (rationalDerivedPullback l E (inv gY))) :
    @Eq (IntegralPullbackCompositionFamily l E)
      (normalizedStage l E S hS f gX gY w TX TY).compositor
      (normalizedCompositor l E S hS) := rfl

private theorem normalizedStage_rational (S : IntegralComparisonSystem.{u} l)
    (hS : IntegralComparisonCompositionLaws l E S)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (TX : ExactInverse (rationalDerivedPullback l E gX)
      (rationalDerivedPullback l E (inv gX)))
    (TY : ExactInverse (rationalDerivedPullback l E gY)
      (rationalDerivedPullback l E (inv gY))) :
    (normalizedStage l E S hS f gX gY w TX TY).rational =
      automorphismStageRationalSquare l E S f (asIso gY) (asIso gX) w := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] normalizedStage

set_option backward.isDefEq.respectTransparency.types true in
/-- The specified integral square rationalizes and descends to the normalized field-stage
square; its specified ordinary exchange is an isomorphism on the supplied domains.

Source: latest blueprint prop-weil-operations.proof.md, sentence 1, via
lem-fix-weil-operations.proof.md, first paragraph
(blueprint: lem-pod-frobenius-pullback-ordinary-exchange).

Proof, following the six DAG steps:
1. Ell differs from p, hence is invertible on both schemes. Use
lem-pod-integral-pullback-composition for (gX,f) and (f,gY), realized by the same
whole-system calculus. Compose inverse c(gX,f), the equality of scheme maps, and c(f,gY).
Its finite reductions are exactly the corresponding square of finite compositors from
lem-weil-pbc-proetale-derived-pullback-composition. The integral map is constructed first;
no equality is deduced merely from equality at separately evaluated reductions.
2. Lem-pod-pullback-identities-scalar-extension and
lem-pur-integral-operations-scalar-extension give A T(C_E)=C_L gamma and
B T(D_E)=D_L gamma. Cancel C_E,C_L to get B T(a_E)=a_L A. The individual scalar
comparisons supply the identity and tower laws for both composite comparisons.
3. Apply the raw localization of def-weil-rationalization-karoubi to the integral square
and its inverse. Integral naturality extends to each pure tensor, then to every finite
sum by additivity. Tensor balancing proves independence of its expression. Rationalize
the scalar square; there is no rational-to-finite reduction functor.
4. On def-weil-algebraically-closed-coefficients take the class [E,a_E] at (E,K).
The two composite arrow actions are conjugated by A and B. The scalar square and
rational naturality prove naturality for an arrow over any larger common field.
Tower laws make these expressions agree after enlargement. Eventual equality of
representatives gives the same quotient arrow. The inverse is represented at E as well.
5. The automorphism square is Cartesian: its unique lift is gX inverse followed by
the given upper map. To use def-exchange-projection over k, restructure the two source
corners by a_X gX and a_Y gY; the pro-etale operations only see the underlying schemes.
Substitute a inverse into its ordinary unit--comparison--counit definition. This gives
exactly ExchangeOnDomains, for the supplied ordinary adjunction of fix-prop-adjunctions(1).
6. Lem-pod-isomorphism-field-transport supplies exact horizontal equivalences and their
inverse pullbacks at both stages, without separatedness of X or Y. Restrict them to the
stipulated domains, which are closed under the inverse operations as well. Apply
lem-weil-mate-iso-along-equivalences to a inverse and that same ordinary adjunction.
The resulting invertible mate is precisely the exchange in step 5. -/
theorem frobeniusPullbackOrdinaryExchange
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY) :
    ∃ (iX : ∀ x : X, Invertible (l : X.residueField x))
      (iY : ∀ y : Y, Invertible (l : Y.residueField y)),
      (fun [_iX : ∀ x : X, Invertible (l : X.residueField x)]
        [_iY : ∀ y : Y, Invertible (l : Y.residueField y)] ↦
        ∃ (S : IntegralComparisonSystem.{u} l)
          (SE : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
            Stage l E S f gX gY w),
          (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
            (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
            (ι : E →ₐ[ℚ_[l]] L),
            ScalarLaw l E L ι S f gX gY w (SE E) (SE L)) ∧
          Nonempty (Common l Ω S f gX gY w
            (fun E ↦ SE (Coefficient.{u} l Ω E)))) (_iX := iX) (_iY := iY) := by
  classical
  obtain ⟨iX, jX, hX⟩ := isomorphismFieldTransport D l _hl Ω gX
  obtain ⟨iY, jY, hY⟩ := isomorphismFieldTransport D l _hl Ω gY
  have hjX : jX = iX := Subsingleton.elim _ _
  have hjY : jY = iY := Subsingleton.elim _ _
  subst jX
  subst jY
  refine ⟨iX, iY, ?_⟩
  let _ := iX
  let _ := iY
  obtain ⟨hx, hx', sx, _, SX, RX, _, ⟨cX⟩, ⟨rX⟩⟩ := hX
  obtain ⟨hy, hy', sy, _, SY, RY, _, ⟨cY⟩, ⟨rY⟩⟩ := hY
  obtain ⟨S, hS⟩ := automorphismConstructibleStage_comparison_system.{u} l
  let laws (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    (hS E E (AlgHom.id ℚ_[l] E)).1.composition E
  let TX (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    rationalExactInverse l E gX hx hx' (sx E).1.some (sx E).2.some
  let TY (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    rationalExactInverse l E gY hy hy' (sy E).1.some (sy E).2.some
  let SE (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
    normalizedStage l E S (laws E) f gX gY w (TX E) (TY E)
  refine ⟨S, SE, ?_, ?_⟩
  · intro E _ _ _ L _ _ _ ι
    constructor
    · intro K
      change (sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X).map _ ≫ _ = _
      dsimp only [SE]
      simp only [normalizedStage_compositor]
      simp only [normalizedSquare_eq]
      apply ObjectProperty.hom_ext
      have hh := automorphismConstructibleStage_square_scalar l E L ι S
        (hS E L ι).1 f (asIso gY) (asIso gX) w K
      simp_rw [(hS E L ι).2] at hh
      set_option backward.isDefEq.respectTransparency false in
      simpa only [scalarComposite, Iso.trans_hom, Functor.mapIso_hom,
        ObjectProperty.FullSubcategory.comp_hom, asIso_hom, Category.assoc,
        integralComparisonConstructibleScalar, sfConstructibleIntegralScalarExtension,
        constructibleIntegralPullback, ObjectProperty.lift, Functor.comp_obj,
        Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.ι_obj,
        ObjectProperty.homMk] using hh
    · intro K
      have hi := fun J ↦ automorphismConstructibleStage_square_scalar l E L ι S
        (hS E L ι).1 f (asIso gY) (asIso gX) w J
      simp_rw [(hS E L ι).2] at hi
      have hr := automorphismStageRationalSquare_scalar l E L ι S f
        (asIso gY) (asIso gX) w hi K
      simpa only [SE, normalizedStage_rational, rationalScalarComposite, Iso.trans_hom,
        Functor.mapIso_hom, Iso.app_hom, asIso_hom, Category.assoc] using hr
  · let tx := commonExactInverse l Ω gX hx hx' SX RX cX rX
    let ty := commonExactInverse l Ω gY hy hy' SY RY cY rY
    refine ⟨{
      comparison := automorphismStageQbarSquare l Ω S f (asIso gY) (asIso gX) w
      component := ?_
      left_arrows := composite_arrows l Ω gX f
      right_arrows := composite_arrows l Ω f gY
      transportX := tx
      transportY := ty
      exchange := exchangeOnDomains _ _ _ _ _ _ ty.counit ty.inverseCounit
        tx.counit tx.inverseCounit }⟩
    intro K
    set_option backward.isDefEq.respectTransparency false in
    simpa only [SE, normalizedStage_rational, asIso_hom, automorphismStageQbarSquare] using
      (automorphismStageQbarSquare_existsUnique l Ω S f
        (asIso gY) (asIso gX) w).exists.choose_spec K


end WeilConjectures.OrdinaryAutomorphismSquare
