/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.FiniteTorStability
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.ExchangeFunctoriality
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Proper product and its two-counit transpose

Source: main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, final sentence
(blueprint: lem-sf-proper-product-counit-transpose).

All expressions below use ordinary proper coordinates. The support-to-direct
normalization is the datum's proper identification. The target `g_* q_* D` is
identified with `t_* D` by the adjunction-compatible composition comparison;
thus transposition is computed with the pasted adjunction. This retains that
comparison, rather than choosing an unrelated adjunction for the composite.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u vB uB vX uX vY uY vT uT
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Coordinates for the displayed composites, not an additional six-functor axiom.
The constructors below insert the recorded coefficient operations and comparisons.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
structure ProperProductCalculus
    (CB : Type uB) (CX : Type uX) (CY : Type uY) (CT : Type uT)
    [Category.{vB} CB] [Category.{vX} CX] [Category.{vY} CY] [Category.{vT} CT] where
  tensorB : CB × CB ⥤ CB
  tensorY : CY × CY ⥤ CY
  tensorT : CT × CT ⥤ CT
  fPull : CB ⥤ CX
  fPush : CX ⥤ CB
  fAdj : fPull ⊣ fPush
  gPull : CB ⥤ CY
  gPush : CY ⥤ CB
  gAdj : gPull ⊣ gPush
  pPull : CX ⥤ CT
  qPull : CY ⥤ CT
  qPush : CT ⥤ CY
  qAdj : qPull ⊣ qPush
  tPull : CB ⥤ CT
  tPush : CT ⥤ CB
  tAdj : tPull ⊣ tPush
  tComposition : tPull ≅ gPull ⋙ qPull
  square : gPull ⋙ qPull ≅ fPull ⋙ pPull
  muG : ∀ M N : CB,
    gPull.obj (tensorB.obj (M, N)) ≅ tensorY.obj (gPull.obj M, gPull.obj N)
  muQ : ∀ M N : CY,
    qPull.obj (tensorY.obj (M, N)) ≅ tensorT.obj (qPull.obj M, qPull.obj N)
  swapB : ∀ M N : CB, tensorB.obj (M, N) ≅ tensorB.obj (N, M)
  swapY : ∀ M N : CY, tensorY.obj (M, N) ≅ tensorY.obj (N, M)

namespace ProperProductCalculus
variable {CB : Type uB} {CX : Type uX} {CY : Type uY} {CT : Type uT}
  [Category.{vB} CB] [Category.{vX} CX] [Category.{vY} CY] [Category.{vT} CT]
  (A : ProperProductCalculus CB CX CY CT)

/-- The ordinary exchange component, the mate specified by def-exchange-projection.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def exchange (K : CX) :
    A.gPull.obj (A.fPush.obj K) ⟶ A.qPush.obj (A.pPull.obj K) :=
  (mateEquiv A.fAdj A.qAdj (TwoSquare.mk _ _ _ _ A.square.hom)).natTrans.app K

/-- The component of the counit-defined ordinary projection transformation for q.
This is precisely def-exchange-projection's formula pi = q_*a composed with eta.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def projectionQ (H : CT) (L : CY) :
    A.tensorY.obj (A.qPush.obj H, L) ⟶
      A.qPush.obj (A.tensorT.obj (H, A.qPull.obj L)) :=
  A.qAdj.homEquiv _ _ ((A.muQ (A.qPush.obj H) L).hom ≫
    A.tensorT.map (Prod.mkHom (A.qAdj.counit.app H) (𝟙 _)))

/-- The component of the same ordinary projection transformation for g.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def projectionG (L : CY) (F : CB) :
    A.tensorB.obj (A.gPush.obj L, F) ⟶
      A.gPush.obj (A.tensorY.obj (L, A.gPull.obj F)) :=
  A.gAdj.homEquiv _ _ ((A.muG (A.gPush.obj L) F).hom ≫
    A.tensorY.map (Prod.mkHom (A.gAdj.counit.app L) (𝟙 _)))

/-- The two signed swaps and the g-projection in the specified order, Psi_g.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def psi (F : CB) (L : CY) :
    A.tensorB.obj (F, A.gPush.obj L) ⟶
      A.gPush.obj (A.tensorY.obj (A.gPull.obj F, L)) :=
  (A.swapB F (A.gPush.obj L)).hom ≫ A.projectionG L F ≫
    A.gPush.map (A.swapY L (A.gPull.obj F)).hom

/-- Exchange tensored with the identity followed by the q-projection, with its
well-typed target q_*(p^* K tensor q^* L).
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def intermediate (K : CX) (L : CY) :
    A.tensorY.obj (A.gPull.obj (A.fPush.obj K), L) ⟶
      A.qPush.obj (A.tensorT.obj (A.pPull.obj K, A.qPull.obj L)) :=
  A.tensorY.map (Prod.mkHom (A.exchange K) (𝟙 L)) ≫ A.projectionQ (A.pPull.obj K) L

/-- Lambda in ordinary proper and pasted-composition coordinates. Applying the
inverse of sixFunctorDirectComposition to its target gives the node's map to t_*D.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def product (K : CX) (L : CY) :
    A.tensorB.obj (A.fPush.obj K, A.gPush.obj L) ⟶
      A.gPush.obj (A.qPush.obj (A.tensorT.obj (A.pPull.obj K, A.qPull.obj L))) :=
  A.psi (A.fPush.obj K) L ≫ A.gPush.map (A.intermediate K L)

/-- The specified product map to t_*D, including the adjunction-compatible
composition comparison. Its inverse is the datum's alpha in proper coordinates.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def lambda (K : CX) (L : CY) :
    A.tensorB.obj (A.fPush.obj K, A.gPush.obj L) ⟶
      A.tPush.obj (A.tensorT.obj (A.pPull.obj K, A.qPull.obj L)) :=
  A.product K L ≫
    (A.tAdj.rightAdjointUniq
      ((A.gAdj.comp A.qAdj).ofNatIsoLeft A.tComposition.symm)).inv.app
        (A.tensorT.obj (A.pPull.obj K, A.qPull.obj L))

/-- The map c_(f,g): pull the tensor back using the canonical composition and
monoidal comparisons, then tensor the pulled-back f- and g-counits.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def twoCounit (K : CX) (L : CY) :
    A.tPull.obj (A.tensorB.obj (A.fPush.obj K, A.gPush.obj L)) ⟶
      A.tensorT.obj (A.pPull.obj K, A.qPull.obj L) :=
  A.tComposition.hom.app (A.tensorB.obj (A.fPush.obj K, A.gPush.obj L)) ≫
    A.qPull.map (A.muG (A.fPush.obj K) (A.gPush.obj L)).hom ≫
    (A.muQ (A.gPull.obj (A.fPush.obj K)) (A.gPull.obj (A.gPush.obj L))).hom ≫
    A.tensorT.map (Prod.mkHom
      (A.square.hom.app (A.fPush.obj K) ≫ A.pPull.map (A.fAdj.counit.app K))
      (A.qPull.map (A.gAdj.counit.app L)))

/-- The intermediate transpose and the total two-counit transpose. The latter is
under the pasted adjunction g^* followed by q^*, so the composition comparison
appears in the coordinate convention, without an additional choice of counit.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def CounitIdentities (K : CX) (L : CY) : Prop :=
  (A.qAdj.homEquiv _ _).symm (A.intermediate K L) =
    (A.muQ (A.gPull.obj (A.fPush.obj K)) L).hom ≫
      A.tensorT.map (Prod.mkHom
        (A.square.hom.app (A.fPush.obj K) ≫ A.pPull.map (A.fAdj.counit.app K)) (𝟙 _)) ∧
  (A.tAdj.homEquiv _ _).symm (A.lambda K L) = A.twoCounit K L

end ProperProductCalculus

/-- The existing residue-field inverse, with the over-scheme map made explicit.
Source: the standing prime-to-characteristic convention
(blueprint: lem-sf-proper-product-counit-transpose). -/
@[instance_reducible]
def properProductResidueInvertible (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (W : SixFunctorSpace D) : ∀ x : W.obj.left, Invertible (C.l : W.obj.left.residueField x) :=
  letI : W.obj.left.Over (Spec (.of D.k)) := ⟨W.obj.hom⟩
  sfStabilityResidueInvertible D C.l C.different W.obj.left

/-- Finite coefficients in the canonical ambient realization. The theorem below
restricts its inputs to the recorded bounded constructible finite-Tor domain.
The adjunction is the canonical one retained by finiteDirectAdjunctionNormalization.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductFiniteWithInverses
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y Z T : SixFunctorSpace D}
    (f : X ⟶ Z) (g : Y ⟶ Z) (p : T ⟶ X) (q : T ⟶ Y)
    (comm : p ≫ f = q ≫ g)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    [∀ z : Z.obj.left, Invertible (C.l : Z.obj.left.residueField z)]
    [∀ t : T.obj.left, Invertible (C.l : T.obj.left.residueField t)] :
    ProperProductCalculus
      (proEtaleDerivedCategory Z.obj.left (finiteCoefficientRing C.l E (m + 1)))
      (proEtaleDerivedCategory X.obj.left (finiteCoefficientRing C.l E (m + 1)))
      (proEtaleDerivedCategory Y.obj.left (finiteCoefficientRing C.l E (m + 1)))
      (proEtaleDerivedCategory T.obj.left (finiteCoefficientRing C.l E (m + 1))) :=
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.succ_pos m)
  { tensorB := finiteIntrinsicDerivedTensor C.l E Z.obj.left m
    tensorY := finiteIntrinsicDerivedTensor C.l E Y.obj.left m
    tensorT := finiteIntrinsicDerivedTensor C.l E T.obj.left m
    fPull := finiteDerivedPullback C.l E m f.hom.left
    fPush := proEtaleConstantDerivedDirectImage f.hom.left (finiteCoefficientRing C.l E (m + 1))
    fAdj := (sfIntrinsicConstantModuleAdjunction f.hom.left
      (finiteCoefficientRing C.l E (m + 1))).mapDerivedCategoryRightDerivedAdjunction
    gPull := finiteDerivedPullback C.l E m g.hom.left
    gPush := proEtaleConstantDerivedDirectImage g.hom.left (finiteCoefficientRing C.l E (m + 1))
    gAdj := (sfIntrinsicConstantModuleAdjunction g.hom.left
      (finiteCoefficientRing C.l E (m + 1))).mapDerivedCategoryRightDerivedAdjunction
    pPull := finiteDerivedPullback C.l E m p.hom.left
    qPull := finiteDerivedPullback C.l E m q.hom.left
    qPush := proEtaleConstantDerivedDirectImage q.hom.left (finiteCoefficientRing C.l E (m + 1))
    qAdj := (sfIntrinsicConstantModuleAdjunction q.hom.left
      (finiteCoefficientRing C.l E (m + 1))).mapDerivedCategoryRightDerivedAdjunction
    tPull := finiteDerivedPullback C.l E m (q ≫ g).hom.left
    tPush := proEtaleConstantDerivedDirectImage (q ≫ g).hom.left
      (finiteCoefficientRing C.l E (m + 1))
    tAdj := (sfIntrinsicConstantModuleAdjunction (q ≫ g).hom.left
      (finiteCoefficientRing C.l E (m + 1))).mapDerivedCategoryRightDerivedAdjunction
    tComposition := sfIntrinsicDerivedPullbackComp
      (finiteCoefficientRing C.l E (m + 1)) q.hom.left g.hom.left
    square := (sfIntrinsicDerivedPullbackComp
      (finiteCoefficientRing C.l E (m + 1)) q.hom.left g.hom.left).symm ≪≫
      eqToIso (congrArg
        (fun h : T.obj.left ⟶ Z.obj.left ↦
          sfIntrinsicDerivedPullback (finiteCoefficientRing C.l E (m + 1)) h)
        (congrArg (fun h : T ⟶ Z ↦ h.hom.left) comm.symm)) ≪≫
      sfIntrinsicDerivedPullbackComp
        (finiteCoefficientRing C.l E (m + 1)) p.hom.left f.hom.left
    muG := canonicalFinitePullbackTensor C.l E g.hom.left m
    muQ := canonicalFinitePullbackTensor C.l E q.hom.left m
    swapB := fun M N ↦ (pullbackTensorBraiding (ProEt.topology Z.obj.left)
      (integralCoefficientCommRingSheaf C.l E Z.obj.left m)
      (finiteIntrinsicClosed C.l E Z.obj.left m)
      (finiteIntrinsicTensorModels C.l E Z.obj.left m)).app (M, N)
    swapY := fun M N ↦ (pullbackTensorBraiding (ProEt.topology Y.obj.left)
      (integralCoefficientCommRingSheaf C.l E Y.obj.left m)
      (finiteIntrinsicClosed C.l E Y.obj.left m)
      (finiteIntrinsicTensorModels C.l E Y.obj.left m)).app (M, N) }

/-- Finite proper coordinates with the standing residue inverses inserted.
The natural-number parameter m represents the positive exponent m+1, including one.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductFinite
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y Z T : SixFunctorSpace D}
    (f : X ⟶ Z) (g : Y ⟶ Z) (p : T ⟶ X) (q : T ⟶ Y)
    (comm : p ≫ f = q ≫ g) :
    ProperProductCalculus
      (proEtaleDerivedCategory Z.obj.left (finiteCoefficientRing C.l E (m + 1)))
      (proEtaleDerivedCategory X.obj.left (finiteCoefficientRing C.l E (m + 1)))
      (proEtaleDerivedCategory Y.obj.left (finiteCoefficientRing C.l E (m + 1)))
      (proEtaleDerivedCategory T.obj.left (finiteCoefficientRing C.l E (m + 1))) :=
  letI := properProductResidueInvertible D C X
  letI := properProductResidueInvertible D C Y
  letI := properProductResidueInvertible D C Z
  letI := properProductResidueInvertible D C T
  properProductFiniteWithInverses C E m f g p q comm

/-- Transport the canonical tensor comparison along the datum's equality with the
actual pullback. No tensor or pullback comparison is chosen here.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductTransportTensor
    {A : Type uB} {B : Type uY} [Category.{vB} A] [Category.{vY} B]
    {P Q : A ⥤ B} (e : P ≅ Q) (T : A × A ⥤ A) (U : B × B ⥤ B)
    (mu : ∀ M N : A, Q.obj (T.obj (M, N)) ≅ U.obj (Q.obj M, Q.obj N))
    (M N : A) : P.obj (T.obj (M, N)) ≅ U.obj (P.obj M, P.obj N) :=
  e.app (T.obj (M, N)) ≪≫ mu M N ≪≫ U.mapIso ((e.app M).symm.prod (e.app N).symm)

/-- Put one recorded coefficient stage in ordinary proper coordinates. The square
comparison is exactly the composite of the stage's pullback compositors.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductOfStage {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type uB} [∀ X, Category.{vB} (B X)]
    (S : SixFunctorPushStage D B) (tensor : ∀ X, B X × B X ⥤ B X)
    {X Y Z T : SixFunctorSpace D} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : T ⟶ X) (q : T ⟶ Y) (comm : p ≫ f = q ≫ g)
    (muG : ∀ M N, (S.pull g).obj ((tensor Z).obj (M, N)) ≅
      (tensor Y).obj ((S.pull g).obj M, (S.pull g).obj N))
    (muQ : ∀ M N, (S.pull q).obj ((tensor Y).obj (M, N)) ≅
      (tensor T).obj ((S.pull q).obj M, (S.pull q).obj N))
    (swapB : ∀ M N, (tensor Z).obj (M, N) ≅ (tensor Z).obj (N, M))
    (swapY : ∀ M N, (tensor Y).obj (M, N) ≅ (tensor Y).obj (N, M)) :
    ProperProductCalculus (B Z) (B X) (B Y) (B T) where
  tensorB := tensor Z
  tensorY := tensor Y
  tensorT := tensor T
  fPull := S.pull f
  fPush := S.direct f
  fAdj := S.pullDirectAdjunction f
  gPull := S.pull g
  gPush := S.direct g
  gAdj := S.pullDirectAdjunction g
  pPull := S.pull p
  qPull := S.pull q
  qPush := S.direct q
  qAdj := S.pullDirectAdjunction q
  tPull := S.pull (q ≫ g)
  tPush := S.direct (q ≫ g)
  tAdj := S.pullDirectAdjunction (q ≫ g)
  tComposition := S.pullComposition q g
  square := (S.pullComposition q g).symm ≪≫
    eqToIso (congrArg (fun h ↦ S.pull h) comm.symm) ≪≫ S.pullComposition p f
  muG := muG
  muQ := muQ
  swapB := swapB
  swapY := swapY

section Stages
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  {X Y Z T : SixFunctorSpace D}
  (f : X ⟶ Z) (g : Y ⟶ Z) (p : T ⟶ X) (q : T ⟶ Y)
  (comm : p ≫ f = q ≫ g)
/-- Completed integral coordinates using the recorded completed tensor and its
finite-reduction-normalized comparison and Koszul braiding.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductIntegral (S : SixFunctorOperationDatum D C E n hn) :
    ProperProductCalculus
      (sfIntegralConstructibleCategory C.l E Z.obj.left)
      (sfIntegralConstructibleCategory C.l E X.obj.left)
      (sfIntegralConstructibleCategory C.l E Y.obj.left)
      (sfIntegralConstructibleCategory C.l E T.obj.left) :=
  letI : ∀ x : Z.obj.left, Invertible (C.l : Z.obj.left.residueField x) :=
    properProductResidueInvertible D C Z
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    properProductResidueInvertible D C Y
  letI : ∀ x : T.obj.left, Invertible (C.l : T.obj.left.residueField x) :=
    properProductResidueInvertible D C T
  properProductOfStage S.higher.integral
    (fun W ↦
      letI := properProductResidueInvertible D C W
      constructibleIntegralTensor C.l E W.obj.left) f g p q comm
    (properProductTransportTensor (eqToIso (S.higher.integralPullback g))
      (constructibleIntegralTensor C.l E Z.obj.left)
      (constructibleIntegralTensor C.l E Y.obj.left)
      (canonicalIntegralPullbackTensor C.l E g.hom.left))
    (properProductTransportTensor (eqToIso (S.higher.integralPullback q))
      (constructibleIntegralTensor C.l E Y.obj.left)
      (constructibleIntegralTensor C.l E T.obj.left)
      (canonicalIntegralPullbackTensor C.l E q.hom.left))
    (pullbackTensorIntegralBraiding C.l E Z.obj.left)
    (pullbackTensorIntegralBraiding C.l E Y.obj.left)

/-- Rational coordinates use rationalization of precisely the integral comparison
and braiding, and the datum's rationalized ordinary adjunctions.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductRational (S : SixFunctorOperationDatum D C E n hn) :
    ProperProductCalculus
      (sfRationalConstructibleCategory C.l E Z.obj.left)
      (sfRationalConstructibleCategory C.l E X.obj.left)
      (sfRationalConstructibleCategory C.l E Y.obj.left)
      (sfRationalConstructibleCategory C.l E T.obj.left) :=
  letI : ∀ x : Z.obj.left, Invertible (C.l : Z.obj.left.residueField x) :=
    properProductResidueInvertible D C Z
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    properProductResidueInvertible D C Y
  letI : ∀ x : T.obj.left, Invertible (C.l : T.obj.left.residueField x) :=
    properProductResidueInvertible D C T
  properProductOfStage S.higher.rational
    (fun W ↦
      letI := properProductResidueInvertible D C W
      rationalDerivedTensor C.l E W.obj.left) f g p q comm
    (properProductTransportTensor (eqToIso (S.higher.rationalPullback g))
      (rationalDerivedTensor C.l E Z.obj.left) (rationalDerivedTensor C.l E Y.obj.left)
      (canonicalRationalPullbackTensor C.l E g.hom.left))
    (properProductTransportTensor (eqToIso (S.higher.rationalPullback q))
      (rationalDerivedTensor C.l E Y.obj.left) (rationalDerivedTensor C.l E T.obj.left)
      (canonicalRationalPullbackTensor C.l E q.hom.left))
    (pullbackTensorRationalBraiding C.l E Z.obj.left)
    (pullbackTensorRationalBraiding C.l E Y.obj.left)

/-- Algebraically closed coordinates use common finite-stage classes of the
specified rational tensor comparisons and signed braiding.
Source: final sentence of lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-proper-product-counit-transpose). -/
def properProductCommon (S : SixFunctorOperationDatum D C E n hn) :
    ProperProductCalculus
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Z.obj.left)
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left)
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar T.obj.left) :=
  letI : ∀ x : Z.obj.left, Invertible (C.l : Z.obj.left.residueField x) :=
    properProductResidueInvertible D C Z
  letI : ∀ x : Y.obj.left, Invertible (C.l : Y.obj.left.residueField x) :=
    properProductResidueInvertible D C Y
  letI : ∀ x : T.obj.left, Invertible (C.l : T.obj.left.residueField x) :=
    properProductResidueInvertible D C T
  properProductOfStage S.closure.commonStage
    (fun W ↦
      letI := properProductResidueInvertible D C W
      commonStageDerivedTensor C.l C.Qbar W.obj.left) f g p q comm
    (properProductTransportTensor (eqToIso (S.closure.commonStagePullback g))
      (commonStageDerivedTensor C.l C.Qbar Z.obj.left)
      (commonStageDerivedTensor C.l C.Qbar Y.obj.left)
      (canonicalCommonStagePullbackTensor C.l C.Qbar g.hom.left))
    (properProductTransportTensor (eqToIso (S.closure.commonStagePullback q))
      (commonStageDerivedTensor C.l C.Qbar Y.obj.left)
      (commonStageDerivedTensor C.l C.Qbar T.obj.left)
      (canonicalCommonStagePullbackTensor C.l C.Qbar q.hom.left))
    (pullbackTensorCommonBraiding C.l C.Qbar Z.obj.left)
    (pullbackTensorCommonBraiding C.l C.Qbar Y.obj.left)

end Stages
/-- Both transposes of the specified proper external-product composite, at all
four coefficient stages, in canonical ordinary proper coordinates.
Source: main-20261015, sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, final sentence
(blueprint: lem-sf-proper-product-counit-transpose).

Proof: properness is preserved by base change and composition, so the canonical
proper identifications apply to f, g, p, q and t. The proper compactification
with identity open factor identifies the supplied compact-support exchange with
its ordinary counit mate, by fix-lem-exchanges and def-exchange-projection.
The projection maps agree with their ordinary counit-defined maps by
fix-prop-projection-formula and def-sf-pf. For any such projection, counit
naturality and the triangle identity give epsilon composed with pullback of pi
as mu followed by epsilon tensor identity. Apply this first to q and use
naturality of mu: the transpose of the exchange is the pulled-back f-counit,
which gives the first equality. Apply the same calculation to g. Compatibility
of the signed braiding with pullback cancels the two swaps in Psi_g, leaving
the g-counit in the second tensor factor. Paste the two adjunctions using
lem-weil-pbc-mate-pasting and the A1 composition comparison of def-sf-datum.
The pasted counit is epsilon_q after q^*epsilon_g; naturality moves
the latter past the inner map. The two resulting factors are exactly the
pulled-back f- and g-counits, giving the second equality under t^* adjoint t_*.
The signed monoidal and composition comparisons are those of
lem-pur-derived-pullback-tensor-iso. The integral argument uses completed
operations; reduction, rationalization and common-stage scalar comparisons
carry the same units, counits and signed comparisons, hence give the same
calculation at every coefficient stage. -/
theorem properProductCounitTranspose
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorDatum D C E (m + 1) (Nat.succ_pos m))
    {X Y Z T : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    [IsSeparated Z.obj.hom] [IsSeparated T.obj.hom]
    (f : X ⟶ Z) (g : Y ⟶ Z) (p : T ⟶ X) (q : T ⟶ Y)
    [IsProper f.hom.left] [IsProper g.hom.left]
    [IsSeparated p.hom.left] [IsSeparated q.hom.left]
    [LocallyOfFiniteType p.hom.left] [LocallyOfFiniteType q.hom.left]
    [QuasiCompact p.hom.left] [QuasiCompact q.hom.left]
    (comm : p ≫ f = q ≫ g)
    (_cartesian : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    (∀ (K : finiteTorConstructibleCategory C.l E (m + 1) (Nat.succ_pos m) X.obj.left)
      (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.succ_pos m) Y.obj.left),
      (properProductFinite C E m f g p q comm).CounitIdentities K.obj L.obj) ∧
    (∀ (K : sfIntegralConstructibleCategory C.l E X.obj.left)
      (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
      S.toSixFunctorOperationDatum.integralFiniteTorDomain X K →
      S.toSixFunctorOperationDatum.integralFiniteTorDomain Y L →
      (properProductIntegral f g p q comm S.toSixFunctorOperationDatum).CounitIdentities K L) ∧
    (∀ (K : sfRationalConstructibleCategory C.l E X.obj.left)
      (L : sfRationalConstructibleCategory C.l E Y.obj.left),
      (properProductRational f g p q comm S.toSixFunctorOperationDatum).CounitIdentities K L) ∧
    (∀ (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
      (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left),
      (properProductCommon f g p q comm S.toSixFunctorOperationDatum).CounitIdentities K L) := by
  sorry

end WeilConjectures
