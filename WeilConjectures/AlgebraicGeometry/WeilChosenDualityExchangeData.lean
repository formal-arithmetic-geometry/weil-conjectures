/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleMateCoherence
public import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
public import WeilConjectures.SixFunctors.CoefVerdierWeilEquivariance
public import Mathlib.CategoryTheory.Adjunction.Unique
/-! # Interfaces for specified Weil exchange

Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md;
thm-sf-verdier-exchange.proof.md, Step 1; lem-sf-tensor-hom.proof.md, Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange).

The operation datum and its normalized common-stage lifts fix the operations.
The conclusion supplies the full constructible Hom domains and the restrictions
of the original adjunctions. All subsequent choices of structure right adjoints
are arbitrary. The displayed transposes are defined from the specified maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b c va vb vc
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
namespace WeilConjectures.WeilChosenDualityExchange
open PodConstructibleMate

/-- The specified three transposes, in exceptional, tensor-Hom, ordinary order.
Source: lem-sf-tensor-hom.proof.md, Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def transposeComponent
    {X : Type a} {Y : Type b} [Category.{va} X] [Category.{vb} Y]
    {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}
    (exceptional : F ⊣ G) (ordinary : P ⊣ Q)
    (TX : X ⥤ X ⥤ X) (TY : Y ⥤ Y ⥤ Y)
    (HX : Xᵒᵖ × X ⥤ X) (HY : Yᵒᵖ × Y ⥤ Y)
    (closedX : ∀ M, TX.obj M ⊣ (Functor.curry.obj HX).obj (op M))
    (closedY : ∀ N, TY.obj N ⊣ (Functor.curry.obj HY).obj (op N))
    (projection : ∀ M A, (TY.obj (F.obj M)).obj A ≅
      F.obj ((TX.obj M).obj (P.obj A))) (omega : Y) (M : X) :
    HY.obj (op (F.obj M), omega) ⟶ Q.obj (HX.obj (op M, G.obj omega)) :=
  ordinary.homEquiv _ _ ((closedX M).homEquiv _ _
    (exceptional.homEquiv _ _
      ((projection M (HY.obj (op (F.obj M), omega))).inv ≫
        (closedY (F.obj M)).counit.app omega)))

/-- The chosen-adjoint comparison is G(n_Y), then the composition mate, then n_X inverse.
Each n is the counit-compatible rightAdjointUniq comparison on pair categories.
Source: thm-sf-verdier-exchange.proof.md, Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def chosenComparison
    {X : Type a} {Y : Type b} {Z : Type c}
    [Category.{va} X] [Category.{vb} Y] [Category.{vc} Z]
    {F : X ⥤ Y} {G : Y ⥤ X} {FY : Y ⥤ Z} {JYcan JY : Z ⥤ Y}
    {FX : X ⥤ Z} {JXcan JX : Z ⥤ X}
    (adjF : F ⊣ G) (adjYcan : FY ⊣ JYcan) (adjXcan : FX ⊣ JXcan)
    (composition : FX ≅ F ⋙ FY) (adjY : FY ⊣ JY) (adjX : FX ⊣ JX) (unit : Z) :
    G.obj (JY.obj unit) ≅ JX.obj unit :=
  G.mapIso ((adjY.rightAdjointUniq adjYcan).app unit) ≪≫
    (conjugateIsoEquiv (adjF.comp adjYcan) adjXcan composition).app unit ≪≫
    ((adjX.rightAdjointUniq adjXcan).app unit).symm

/-- Natural transformations with exactly the specified transpose and exchange components.
Their types assert Weil equivariance and contravariant naturality, without asserting
invertibility. Source: lem-sf-tensor-hom.proof.md, Steps 1--2 and
thm-sf-verdier-exchange.proof.md, Steps 2--3
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
structure Exchange
    {X : Type a} {Y : Type b} [Category.{va} X] [Category.{vb} Y]
    {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}
    (exceptional : F ⊣ G) (ordinary : P ⊣ Q)
    (TX : X ⥤ X ⥤ X) (TY : Y ⥤ Y ⥤ Y)
    (HX : Xᵒᵖ × X ⥤ X) (HY : Yᵒᵖ × Y ⥤ Y)
    (closedX : ∀ M, TX.obj M ⊣ (Functor.curry.obj HX).obj (op M))
    (closedY : ∀ N, TY.obj N ⊣ (Functor.curry.obj HY).obj (op N))
    (projection : ∀ M A, (TY.obj (F.obj M)).obj A ≅
      F.obj ((TX.obj M).obj (P.obj A))) (omegaX : X) (omegaY : Y)
    (comparison : G.obj omegaY ≅ omegaX) where
  tau : F.op ⋙ (Functor.curry.obj HY).flip.obj omegaY ⟶
    (Functor.curry.obj HX).flip.obj (G.obj omegaY) ⋙ Q
  tau_app (M : X) : tau.app (op M) =
    transposeComponent exceptional ordinary TX TY HX HY closedX closedY projection omegaY M
  exchange : F.op ⋙ (Functor.curry.obj HY).flip.obj omegaY ⟶
    (Functor.curry.obj HX).flip.obj omegaX ⋙ Q
  exchange_app (M : X) : exchange.app (op M) =
    transposeComponent exceptional ordinary TX TY HX HY closedX closedY projection omegaY M ≫
      Q.map (HX.map (Prod.mkHom (𝟙 (op M)) comparison.hom))

section Geometric
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- The model point, in the already existing finite-type model category.
Source: cor-coef-verdier-weil-equivariance.proof.md, structure morphisms
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def point : Models D :=
  ⟨CoefVerdierWeil.pointModel D, inferInstance, inferInstance⟩

/-- The original structure arrow to the model point.
Source: thm-sf-verdier-exchange.proof.md, Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def structureMap (X : Models D) : X ⟶ point D :=
  ObjectProperty.homMk (CoefVerdierWeil.structureModel D X.obj)

/-- The original carrier category, with no completion or new objects.
Source: common-stage coefficient convention
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
abbrev Carrier (X : Models D) :=
  generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar (D.geometricFiber X.obj).left

/-- The existing fixed-pair category; commonFrobenius is the named standard pullback.
Source: def-weil-weil-sheaf-complex
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
abbrev Pair (X : Models D) := IsoAlgebra (commonFrobenius D C X)

/-- The exact permitted-pair object used by the recorded partial Hom functor.
Source: derived-Hom domain convention
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def homPair (X : Models D)
    (permitted : ∀ K N : Carrier D C X,
      commonStageHomPairs C.l C.Qbar (D.geometricFiber X.obj).left (op K, N))
    (K N : Carrier D C X) :=
  (⟨(op K, N), permitted K N⟩ :
    (commonStageHomPairs C.l C.Qbar (D.geometricFiber X.obj).left).FullSubcategory)

variable {D C}
variable {A : CommonStage D C} (L : CommonLifts D C A)

/-- The original ordinary adjunction lifted with its specified exchange mate.
Source: ordinary-adjunction paragraph of lem-fix-weil-operations.proof.md
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def ordinaryAdjunction {X Y : Models D} (f : X ⟶ Y) :
    L.pullFunctor f ⊣ L.directFunctor f := by
  unfold CommonLifts.pullFunctor CommonLifts.directFunctor
  exact IsoAlgebra.mapOfNatIsoAdjunction
    (A.pullDirectAdjunction ((fiberModels D).map f)) (L.pull f) (L.direct f)
    (L.directMate f).symm

/-- The canonical constructible exceptional adjunction lifted with its actual mate.
Source: cor-coef-verdier-weil-equivariance.proof.md, last paragraph
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def exceptionalAdjunction {X Y : Models D} (f : X ⟶ Y)
    (c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left) :
    L.supportFunctor f c₀ c ⊣ L.exceptionalFunctor f c₀ c := by
  unfold CommonLifts.supportFunctor CommonLifts.exceptionalFunctor
  exact IsoAlgebra.mapOfNatIsoAdjunction
    (A.exceptionalAdjunction ((fiberModels D).map f) c)
    (L.support f c₀ c) (L.exceptional f c₀ c) (L.exceptionalMate f c₀ c).symm

/-- Full bounded-constructible Hom, its standard Weil lift, and the restriction of
argument-first tensor-Hom adjunction. Carrier object and arrow equalities identify
the existing partial Hom, and counit normalization identifies its original evaluation.
Evaluation together with the tensor comparison determines the standard Hom structure.
These are conclusion data, not additional hypotheses on the schemes or complexes.
Source: cor-coef-verdier-weil-equivariance.proof.md, evaluation paragraph
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
structure HomLift (X : Models D) where
  permitted : ∀ K N : Carrier D C X,
    commonStageHomPairs C.l C.Qbar (D.geometricFiber X.obj).left (op K, N)
  hom : (Pair D C X)ᵒᵖ × Pair D C X ⥤ Pair D C X
  obj (K N : Pair D C X) :
    (hom.obj (op K, N)).carrier =
      (commonStageDerivedInternalHom C.l C.Qbar (D.geometricFiber X.obj).left).obj
        (homPair D C X permitted K.carrier N.carrier)
  map {K K' N N' : Pair D C X} (f : K' ⟶ K) (g : N ⟶ N') :
    HEq (hom.map (Prod.mkHom f.op g)).hom.f
      ((commonStageDerivedInternalHom C.l C.Qbar (D.geometricFiber X.obj).left).map
        (X := homPair D C X permitted K.carrier N.carrier)
        (Y := homPair D C X permitted K'.carrier N'.carrier)
        (ObjectProperty.homMk (Prod.mkHom f.hom.f.op g.hom.f)))
  closed (K : Pair D C X) :
    (Functor.curry.obj (L.tensorFunctor X)).obj K ⊣ (Functor.curry.obj hom).obj (op K)
  evaluation (K N : Pair D C X) :
    HEq ((closed K).counit.app N).hom.f
      ((fun [_h : ∀ x : (D.geometricFiber X.obj).left,
          Invertible (C.l : (D.geometricFiber X.obj).left.residueField x)] ↦
        podArgumentFirstEvaluation (podCommonClosed C.l C.Qbar (D.geometricFiber X.obj).left)
          (pullbackTensorCommonBraiding C.l C.Qbar (D.geometricFiber X.obj).left)
          (homPair D C X permitted K.carrier N.carrier))
        (_h := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x))


/-- The standard coefficient pair at the model point. Its underlying constant
object is fixed, and the Frobenius isomorphism is normalized by the tensor unit.
Source: cor-coef-verdier-weil-equivariance.proof.md, dualizing object paragraph
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
structure Constant where
  theta : (sfCommonStageWeilFrobeniusPullback D C.l C.different
      (CoefVerdierWeil.pointModel D) C.Qbar).obj
        (CoefVerdierWeil.commonUnit D C.l C.different C.Qbar
          (CoefVerdierWeil.pointModel D)) ≅
    CoefVerdierWeil.commonUnit D C.l C.different C.Qbar (CoefVerdierWeil.pointModel D)
  normalized (M : Carrier D C (point D)) :
    (CoefVerdierWeil.commonMu D C.l C.different C.Qbar (CoefVerdierWeil.pointModel D)
      (CoefVerdierWeil.commonUnit D C.l C.different C.Qbar
        (CoefVerdierWeil.pointModel D)) M).hom ≫
      (@commonStageDerivedTensor C.l _ C.Qbar _ _ _
        (D.geometricFiber (CoefVerdierWeil.pointModel D)).left
        (fun x ↦ sfWeilPrimeInvertible D C.l C.different
          (CoefVerdierWeil.pointModel D) x)).map
        (Prod.mkHom theta.hom (𝟙 _)) ≫
      (CoefVerdierWeil.commonUnitor D C.l C.different C.Qbar
        (CoefVerdierWeil.pointModel D)
        ((sfCommonStageWeilFrobeniusPullback D C.l C.different
          (CoefVerdierWeil.pointModel D) C.Qbar).obj M)).hom =
    (sfCommonStageWeilFrobeniusPullback D C.l C.different
      (CoefVerdierWeil.pointModel D) C.Qbar).map
        (CoefVerdierWeil.commonUnitor D C.l C.different C.Qbar
          (CoefVerdierWeil.pointModel D) M).hom

/-- The coefficient pair with its normalized constant structure.
Source: dualizing-object convention
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def Constant.pair (U : Constant (D := D) (C := C)) : Pair D C (point D) := by
  unfold Pair commonFrobenius point
  exact IsoAlgebra.mk _ U.theta

variable (D C)
variable (A : SixFunctorCommonStages D C) (W : CommonLifts D C A.commonStage)
variable (X Y : Models D) (f : X ⟶ Y)
variable (cf : Compactification f.hom.left)
variable (cy : Compactification (structureMap D Y).hom.left)
variable (cx : Compactification (f ≫ structureMap D Y).hom.left)

/-- Exactly the compactification's geometric scalar extension, as in the existing lift.
Source: geometric-base-change convention
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
abbrev geometricCompactification {X' Y' : Models D} (h : X' ⟶ Y')
    (c₀ : Compactification h.hom.left) :=
  FrobeniusExchange.geometricCompactification D h.hom c₀

/-- Constructible-domain and map-lifting conclusions needed by the displayed formulas.
The composition and projection isomorphisms have the specified carrier maps.
The structure arrow of X is written f followed by a_Y; its equality to a_X is
already the over-category condition on f, with no independent compositor chosen.
Source: the domain paragraph, thm-sf-verdier-exchange Step 1, and projection paragraph
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
structure Data where
  homX : HomLift W X
  homY : HomLift W Y
  homPoint : HomLift W (point D)
  unit : Constant (D := D) (C := C)
  composition :
    W.supportFunctor (f ≫ structureMap D Y) cx
        (geometricCompactification D (f ≫ structureMap D Y) cx) ≅
      W.supportFunctor f cf (geometricCompactification D f cf) ⋙
        W.supportFunctor (structureMap D Y) cy
          (geometricCompactification D (structureMap D Y) cy)
  composition_carrier (K : Pair D C X) :
    HEq (composition.hom.app K).hom.f
      ((A.commonStage.composition ((fiberModels D).map f)
        ((fiberModels D).map (structureMap D Y))
        (geometricCompactification D f cf)
        (geometricCompactification D (structureMap D Y) cy)
        (fiberCompositionCompactification D f (structureMap D Y)
          (geometricCompactification D (f ≫ structureMap D Y) cx))).hom.app K.carrier)
  projection (M : Pair D C X) (N : Pair D C Y) :
    (W.tensorFunctor Y).obj
        ((W.supportFunctor f cf (geometricCompactification D f cf)).obj M, N) ≅
      (W.supportFunctor f cf (geometricCompactification D f cf)).obj
        ((W.tensorFunctor X).obj (M, (W.pullFunctor f).obj N))
  projection_carrier (M : Pair D C X) (N : Pair D C Y) :
    HEq (projection M N).hom.hom.f
      (compactSupportProjectionComponent A.commonStageExchange
        ((fiberModels D).map f) (geometricCompactification D f cf) M.carrier N.carrier)

/-- The original ordinary unit, counit, and both Hom bijections on the pair categories.
Source: lem-fix-weil-operations.proof.md, ordinary-adjunction paragraph
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def OrdinaryMaps : Prop :=
  (∀ K : Pair D C Y, HEq ((ordinaryAdjunction W f).unit.app K).hom.f
    ((A.commonStage.pullDirectAdjunction ((fiberModels D).map f)).unit.app K.carrier)) ∧
  (∀ M : Pair D C X, HEq ((ordinaryAdjunction W f).counit.app M).hom.f
    ((A.commonStage.pullDirectAdjunction ((fiberModels D).map f)).counit.app M.carrier)) ∧
  (∀ (K : Pair D C Y) (M : Pair D C X)
    (v : (W.pullFunctor f).obj K ⟶ M)
    (v₀ : (A.commonStage.pull ((fiberModels D).map f)).obj K.carrier ⟶ M.carrier),
    HEq v.hom.f v₀ →
    HEq ((ordinaryAdjunction W f).homEquiv K M v).hom.f
      ((A.commonStage.pullDirectAdjunction ((fiberModels D).map f)).homEquiv
        K.carrier M.carrier v₀)) ∧
  ∀ (K : Pair D C Y) (M : Pair D C X) (w : K ⟶ (W.directFunctor f).obj M)
    (w₀ : K.carrier ⟶ (A.commonStage.direct ((fiberModels D).map f)).obj M.carrier),
    HEq w.hom.f w₀ →
    HEq (((ordinaryAdjunction W f).homEquiv K M).symm w).hom.f
      (((A.commonStage.pullDirectAdjunction ((fiberModels D).map f)).homEquiv
        K.carrier M.carrier).symm w₀)

/-- Naturality of the two specified maps for every choice of structure adjunctions.
The chosen comparison is an Iso in the pair category by its construction; every
component of tau and e is a pair morphism, with the three original transposes.
Source: thm-sf-verdier-exchange Steps 1--3 and lem-sf-tensor-hom Step 1
(blueprint: lem-sf-weil-chosen-duality-exchange). -/
def Data.Laws (d : Data D C A W X Y f cf cy cx) : Prop :=
  OrdinaryMaps D C A W X Y f ∧
  ∀ (JX : Pair D C (point D) ⥤ Pair D C X)
    (JY : Pair D C (point D) ⥤ Pair D C Y)
    (adjX : W.supportFunctor (f ≫ structureMap D Y) cx
        (geometricCompactification D (f ≫ structureMap D Y) cx) ⊣ JX)
    (adjY : W.supportFunctor (structureMap D Y) cy
        (geometricCompactification D (structureMap D Y) cy) ⊣ JY),
    Nonempty (Exchange
      (exceptionalAdjunction W f cf (geometricCompactification D f cf))
      (ordinaryAdjunction W f)
      (Functor.curry.obj (W.tensorFunctor X)) (Functor.curry.obj (W.tensorFunctor Y))
      d.homX.hom d.homY.hom d.homX.closed d.homY.closed d.projection
      (JX.obj d.unit.pair) (JY.obj d.unit.pair)
      (chosenComparison
        (exceptionalAdjunction W f cf (geometricCompactification D f cf))
        (exceptionalAdjunction W (structureMap D Y) cy
          (geometricCompactification D (structureMap D Y) cy))
        (exceptionalAdjunction W (f ≫ structureMap D Y) cx
          (geometricCompactification D (f ≫ structureMap D Y) cx))
        d.composition adjY adjX d.unit.pair))

end Geometric
end WeilConjectures.WeilChosenDualityExchange
