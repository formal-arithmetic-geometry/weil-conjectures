/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.ConstructibleWeilModelSquares
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains

/-! # Semilinear Frobenius exchange cubes

Source: blueprint, prop-weil-operations.proof.md, sentence 1, and
lem-fix-weil-operations.proof.md, composition and exchange paragraph
(blueprint: lem-pod-semilinear-exchange-cube-coherence).

The equations retain the specified exchanges, compositors and compactification comparisons.
All comparison formulas use Lean's diagrammatic order. Each support comparison retains its
model compactification as an index. Normalization transports only from that model anchor;
the conclusions compare different model anchors at arbitrary geometric compactifications.
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
universe u v w a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open CategoryTheory.SuppliedExchangeProjection
open WeilConjectures.PodConstructibleMate
namespace WeilConjectures.PodExchangeCube

/-- The iterated comparison c_GF = G(c_F)c_G, with its canonical associators.
Source: node proof step 3 (blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def iterated {C : Type a} {B : Type b} {T : Type c}
    [Category.{d} C] [Category.{e} B] [Category.{f} T]
    {P : C ⥤ C} {Q : B ⥤ B} {R : T ⥤ T} {F : C ⥤ B} {G : B ⥤ T}
    (cF : F ⋙ Q ≅ P ⋙ F) (cG : G ⋙ R ≅ Q ⋙ G) :
    (F ⋙ G) ⋙ R ≅ P ⋙ (F ⋙ G) :=
  Functor.associator F G R ≪≫ Functor.isoWhiskerLeft F cG ≪≫
    (Functor.associator F Q G).symm ≪≫ Functor.isoWhiskerRight cF G ≪≫
    Functor.associator P F G

/-- The displayed cube equation together with the equation for every actual Weil structure.
The second clause uses exactly c followed by F(theta), the existing fixed-pair lift.
Source: node statement, displayed identities and Weil-pair consequence
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def Equivariant {C : Type a} {B : Type b} [Category.{c} C] [Category.{d} B]
    {P : C ⥤ C} {Q : B ⥤ B} {F G : C ⥤ B}
    (cF : F ⋙ Q ≅ P ⋙ F) (cG : G ⋙ Q ≅ P ⋙ G) (α : F ⟶ G) : Prop :=
  (∀ K : C, cF.hom.app K ≫ α.app (P.obj K) =
    Q.map (α.app K) ≫ cG.hom.app K) ∧
  ∀ K : IsoAlgebra P,
    ((IsoAlgebra.mapOfNatIso cF).obj K).str.hom ≫ α.app K.carrier =
      Q.map (α.app K.carrier) ≫ ((IsoAlgebra.mapOfNatIso cG).obj K).str.hom

/-- Relabel a k-scheme using a_W g_W; its underlying scheme is unchanged.
Source: node proof steps 1--2 (blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def twist {k : Type u} [Field k] (W : Over (Spec (.of k))) (g : Aut W.left) :
    Over (Spec (.of k)) := Over.mk (g.hom ≫ W.hom)

/-- The same underlying automorphism is now a k-linear isomorphism.
Source: node proof step 1 (blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def twistIso {k : Type u} [Field k] (W : Over (Spec (.of k))) (g : Aut W.left) :
    twist W g ≅ W := Over.isoMk g rfl

/-- Relabeling preserves finite type and makes every commuting semilinear face linear.
This applies to arbitrary relative compactifications as well as geometric fibers.
No separatedness of W or V over k is assumed.
Source: node proof steps 1, 2 and 5
(blueprint: lem-pod-semilinear-exchange-cube-coherence).
Proof: an isomorphism is of finite type, so composition preserves finite type.
For the arrow equation substitute r g_V = g_W r and then r a_V = a_W.
The pro-etale site and its constant rings use only the underlying scheme, unchanged by
Over.mk. Therefore every unit, counit and operation component on that site is unchanged.
Base-changing a compactification along g_V retains its proper and open factors; apply
the same calculation to its projection isomorphism and to every refinement arrow. -/
theorem relabeling {k : Type u} [Field k]
    (W V : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    (gW : Aut W.left) (gV : Aut V.left) (r : W.left ⟶ V.left)
    (hr : r ≫ V.hom = W.hom) (hg : r ≫ gV.hom = gW.hom ≫ r) :
    LocallyOfFiniteType (twist W gW).hom ∧ QuasiCompact (twist W gW).hom ∧
      r ≫ (twist V gV).hom = (twist W gW).hom := by
  refine ⟨?_, ?_, ?_⟩
  · change LocallyOfFiniteType (gW.hom ≫ W.hom)
    infer_instance
  · change QuasiCompact (gW.hom ≫ W.hom)
    infer_instance
  · change r ≫ (gV.hom ≫ V.hom) = gW.hom ≫ W.hom
    rw [← Category.assoc, hg, Category.assoc, hr]

section Stage
variable {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type v}
  [∀ X : SixFunctorSpace D, Category.{w} (B X)]

/-- The supplied individual Frobenius comparisons. Their normalization is imposed below
at the actual rational and common coefficient stages. Support retains the model anchor
as well as the geometric representative. This record adds no operations.
Source: node statement, standard lifts
(blueprint: lem-pod-semilinear-exchange-cube-coherence).
Prerequisite interface owner: (blueprint: def-pod-semilinear-exchange-cube-data). -/
structure Comparisons (S : SixFunctorPushStage D B)
    (P : ∀ X : Models D, B ((fiberModels D).obj X) ⥤ B ((fiberModels D).obj X)) where
  pull : ∀ {X Y : Models D} (f : X ⟶ Y),
    S.pull ((fiberModels D).map f) ⋙ P X ≅ P Y ⋙ S.pull ((fiberModels D).map f)
  direct : ∀ {X Y : Models D} (f : X ⟶ Y),
    S.direct ((fiberModels D).map f) ⋙ P Y ≅ P X ⋙ S.direct ((fiberModels D).map f)
  support : ∀ {X Y : Models D} (f : X ⟶ Y)
    (_c₀ : Compactification f.hom.left)
    (c : Compactification ((fiberModels D).map f).hom.left),
    S.support ((fiberModels D).map f) c ⋙ P Y ≅
      P X ⋙ S.support ((fiberModels D).map f) c

/-- Normalize the stage's specified direct exchange to its named operation endpoints.
Source: def-exchange-projection, supplied-domain formula
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def directExchange (S : SixFunctorPushStage D B)
    {T : ∀ X : SixFunctorSpace D, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (E : SixFunctorExchangeData S T Q) :
    S.direct Q.f ⋙ S.pull Q.g ⟶ S.pull Q.g' ⋙ S.direct Q.f' :=
  eqToHom (congrArg₂ (fun F G ↦ F ⋙ G) E.push E.horizontal).symm ≫ E.stage.exchange ≫
    eqToHom (congrArg₂ (fun F G ↦ F ⋙ G) E.horizontal' E.push')

/-- The actual chosen-compactification exchange with its supplied endpoint identifications.
Source: def-exchange-projection, proper mate followed by open base change
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def compactExchange (S : SixFunctorPushStage D B)
    {T : ∀ X : SixFunctorSpace D, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (E : SixFunctorExchangeData S T Q) :
    S.support Q.f Q.compactification ⋙ S.pull Q.g ⟶
      S.pull Q.g' ⋙ S.support Q.f' Q.compactification' :=
  eqToHom (congrArg₂ (fun F G ↦ F ⋙ G) E.compactSupport E.horizontal).symm ≫
    E.stage.compactExchange ≫
    eqToHom (congrArg₂ (fun F G ↦ F ⋙ G) E.horizontal' E.compactSupport')

/-- Change both compactification representatives using exactly the canonical comparisons.
The reference square may descend to k₀; the new representatives need not do so.
Source: node statement, representative independence
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def changedExchange (S : SixFunctorPushStage D B)
    {T : ∀ X : SixFunctorSpace D, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (E : SixFunctorExchangeData S T Q)
    (c : Compactification Q.f.hom.left) (c' : Compactification Q.f'.hom.left) :
    S.support Q.f c ⋙ S.pull Q.g ⟶ S.pull Q.g' ⋙ S.support Q.f' c' :=
  Functor.whiskerRight (S.comparison Q.f c Q.compactification).hom (S.pull Q.g) ≫
    compactExchange S E ≫
    Functor.whiskerLeft (S.pull Q.g') (S.comparison Q.f' Q.compactification' c').hom

/-- The specified direct-image compositor, including scalar-extension functoriality.
Source: node statement, composition comparison
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def directComposition (S : SixFunctorPushStage D B) {X Y Z : Models D}
    (f : X ⟶ Y) (h : Y ⟶ Z) :
    S.direct ((fiberModels D).map f) ⋙ S.direct ((fiberModels D).map h) ≅
      S.direct ((fiberModels D).map (f ≫ h)) :=
  (sixFunctorDirectComposition S ((fiberModels D).map f) ((fiberModels D).map h)).symm ≪≫
    eqToIso (congrArg S.direct ((fiberModels D).map_comp f h).symm)

/-- Transport only an equality of the scheme arrow, retaining the same compactification.
Source: node statement, composition comparisons
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def supportTransport (S : SixFunctorPushStage D B) {X Y : SixFunctorSpace D}
    {f g : X ⟶ Y} (h : f = g) (c : Compactification f.hom.left) :
    S.support f c ≅ S.support g (c.copy (congrArg (fun e ↦ e.hom.left) h).symm) := by
  cases h
  exact Iso.refl _

/-- The compact-support compositor for arbitrary geometric compactifications.
Source: node statement, compact-support composition comparison
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def supportComposition (S : SixFunctorPushStage D B) {X Y Z : Models D}
    (f : X ⟶ Y) (h : Y ⟶ Z)
    (cf : Compactification ((fiberModels D).map f).hom.left)
    (ch : Compactification ((fiberModels D).map h).hom.left)
    (c : Compactification ((fiberModels D).map (f ≫ h)).hom.left) :
    S.support ((fiberModels D).map f) cf ⋙ S.support ((fiberModels D).map h) ch ≅
      S.support ((fiberModels D).map (f ≫ h)) c :=
  (S.composition ((fiberModels D).map f) ((fiberModels D).map h) cf ch
    (fiberCompositionCompactification D f h c)).symm ≪≫
    (supportTransport S ((fiberModels D).map_comp f h) c).symm

/-- All cube, composition and representative-change identities on the supplied domains.
Each Equivariant clause includes its exact fixed-pair morphism equation. Model anchors are
independent in the compact exchange, composition and representative-change clauses;
in particular clause 5 asserts agreement of exchanges from different model compactifications.
Source: node statement, all three displayed identities and their compatibility
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def Laws (S : SixFunctorPushStage D B)
    (T : ∀ X : SixFunctorSpace D, B X ⥤ B X ⥤ B X)
    (E : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S T Q)
    (P : ∀ X : Models D, B ((fiberModels D).obj X) ⥤ B ((fiberModels D).obj X))
    (L : Comparisons S P) : Prop :=
  (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left],
    Equivariant (iterated (L.direct Q.f) (L.pull Q.g))
      (iterated (L.pull Q.g') (L.direct Q.f')) (directExchange S (E Q.fiber))) ∧
  (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left]
      (c₀ : Compactification Q.f.hom.left) (c₀' : Compactification Q.f'.hom.left)
      (c : Compactification ((fiberModels D).map Q.f).hom.left)
      (c' : Compactification ((fiberModels D).map Q.f').hom.left),
    Equivariant (iterated (L.support Q.f c₀ c) (L.pull Q.g))
      (iterated (L.pull Q.g') (L.support Q.f' c₀' c'))
      (changedExchange S (E Q.fiber) c c')) ∧
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left],
    Equivariant (iterated (L.direct f) (L.direct h)) (L.direct (f ≫ h))
      (directComposition S f h).hom) ∧
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left]
      (cf₀ : Compactification f.hom.left) (ch₀ : Compactification h.hom.left)
      (c₀ : Compactification (f ≫ h).hom.left)
      (cf : Compactification ((fiberModels D).map f).hom.left)
      (ch : Compactification ((fiberModels D).map h).hom.left)
      (c : Compactification ((fiberModels D).map (f ≫ h)).hom.left),
    Equivariant (iterated (L.support f cf₀ cf) (L.support h ch₀ ch))
      (L.support (f ≫ h) c₀ c) (supportComposition S f h cf ch c).hom) ∧
  (∀ {X Y : Models D} (f : X ⟶ Y) (c₀ c₀' : Compactification f.hom.left)
      (c c' : Compactification ((fiberModels D).map f).hom.left),
    Equivariant (L.support f c₀ c) (L.support f c₀' c')
      (S.comparison ((fiberModels D).map f) c c').hom) ∧
  (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left]
      (c₀ d₀ : Compactification Q.f.hom.left)
      (c₀' d₀' : Compactification Q.f'.hom.left)
      (c d : Compactification ((fiberModels D).map Q.f).hom.left)
      (c' d' : Compactification ((fiberModels D).map Q.f').hom.left),
    Equivariant (iterated (L.support Q.f c₀ c) (L.pull Q.g))
      (iterated (L.support Q.f d₀ d) (L.pull Q.g))
      (Functor.whiskerRight (S.comparison ((fiberModels D).map Q.f) c d).hom
        (S.pull ((fiberModels D).map Q.g))) ∧
    Equivariant (iterated (L.pull Q.g') (L.support Q.f' c₀' c'))
      (iterated (L.pull Q.g') (L.support Q.f' d₀' d'))
      (Functor.whiskerLeft (S.pull ((fiberModels D).map Q.g'))
        (S.comparison ((fiberModels D).map Q.f') c' d').hom) ∧
    Functor.whiskerRight (S.comparison ((fiberModels D).map Q.f) c d).hom
        (S.pull ((fiberModels D).map Q.g)) ≫ changedExchange S (E Q.fiber) d d' =
      changedExchange S (E Q.fiber) c c' ≫
        Functor.whiskerLeft (S.pull ((fiberModels D).map Q.g'))
          (S.comparison ((fiberModels D).map Q.f') c' d').hom) ∧
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left]
      (cf₀ df₀ : Compactification f.hom.left)
      (ch₀ dh₀ : Compactification h.hom.left)
      (c₀ d₀ : Compactification (f ≫ h).hom.left)
      (cf df : Compactification ((fiberModels D).map f).hom.left)
      (ch dh : Compactification ((fiberModels D).map h).hom.left)
      (c d : Compactification ((fiberModels D).map (f ≫ h)).hom.left),
    Equivariant (iterated (L.support f cf₀ cf) (L.support h ch₀ ch))
      (iterated (L.support f df₀ df) (L.support h dh₀ dh))
      (Functor.whiskerRight (S.comparison ((fiberModels D).map f) cf df).hom
          (S.support ((fiberModels D).map h) ch) ≫
        Functor.whiskerLeft (S.support ((fiberModels D).map f) df)
          (S.comparison ((fiberModels D).map h) ch dh).hom) ∧
    Equivariant (L.support (f ≫ h) c₀ c) (L.support (f ≫ h) d₀ d)
      (S.comparison ((fiberModels D).map (f ≫ h)) c d).hom ∧
    Functor.whiskerRight (S.comparison ((fiberModels D).map f) cf df).hom
        (S.support ((fiberModels D).map h) ch) ≫
      Functor.whiskerLeft (S.support ((fiberModels D).map f) df)
        (S.comparison ((fiberModels D).map h) ch dh).hom ≫
      (supportComposition S f h df dh d).hom =
    (supportComposition S f h cf ch c).hom ≫
      (S.comparison ((fiberModels D).map (f ≫ h)) c d).hom)
end Stage

/-- The canonical rational pullback-composition component, with inherited prime units.
Source: node proof step 3 (blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def rationalPullComponent (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {X Y : Models D} (f : X ⟶ Y)
    (K : sfRationalConstructibleCategory C.l E (D.geometricFiber Y.obj).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  letI := fun y ↦ sfWeilPrimeInvertible D C.l C.different Y.obj y
  (pullbackTensorRationalComposition C.l E (FrobeniusExchange.fiberMap D f.hom)
    (D.geometricFrobenius X.obj).hom K).symm ≪≫
    eqToIso (congrArg
      (fun m : (D.geometricFiber X.obj).left ⟶ (D.geometricFiber Y.obj).left ↦
        (rationalDerivedPullback C.l E m).obj K)
      (D.frobenius_square_cartesian X.obj Y.obj f.hom).2.2.2.2.1) ≪≫
    pullbackTensorRationalComposition C.l E (D.geometricFrobenius Y.obj).hom
      (FrobeniusExchange.fiberMap D f.hom) K

/-- Normalizations fixing the standard rational comparisons, rather than arbitrary isomorphisms.
Pullback uses its actual compositors, direct image their adjunction mate, and support the
actual proper/open Frobenius exchange of the indexed model compactification. Conjugation
specifies its value at any geometric compactification from that same model anchor only.
Agreement between different model anchors is a conclusion, not a normalization hypothesis.
No equivariance equation for an exchange or compositor is assumed here.
Source: node statement, canonical comparisons and compactification changes
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def rationalNormalized (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    (A : SixFunctorHigherOperations D C E)
    (L : Comparisons A.rational
      (fun X : Models D ↦ sfWeilFrobeniusPullback D C.l C.different X.obj E)) : Prop :=
  (∀ {X Y : Models D} (f : X ⟶ Y)
      (K : sfRationalConstructibleCategory C.l E (D.geometricFiber Y.obj).left),
    HEq ((L.pull f).app K) (rationalPullComponent D C E f K)) ∧
  (∀ {X Y : Models D} (f : X ⟶ Y),
    (L.direct f).hom = (mateEquiv
      (A.rational.pullDirectAdjunction ((fiberModels D).map f))
      (A.rational.pullDirectAdjunction ((fiberModels D).map f)) (L.pull f).inv).natTrans) ∧
  (∀ {X Y : Models D} (f : X ⟶ Y)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      (c₀ : Compactification f.hom.left)
      (K : sfRationalConstructibleCategory C.l E (D.geometricFiber X.obj).left),
    HEq ((L.support f c₀ (FrobeniusExchange.geometricCompactification D f.hom c₀)).hom.app K)
      ((FrobeniusExchange.frobeniusRational D C.l C.different E f.hom
        (FrobeniusExchange.frobeniusCompactModel D f.hom c₀)).app K)) ∧
  ∀ {X Y : Models D} (f : X ⟶ Y) (c₀ : Compactification f.hom.left)
      (c : Compactification ((fiberModels D).map f).hom.left),
    (L.support f c₀ c).hom =
      Functor.whiskerRight
        (A.rational.comparison ((fiberModels D).map f) c
          (FrobeniusExchange.geometricCompactification D f.hom c₀)).hom
        (sfWeilFrobeniusPullback D C.l C.different Y.obj E) ≫
      (L.support f c₀ (FrobeniusExchange.geometricCompactification D f.hom c₀)).hom ≫
      Functor.whiskerLeft (sfWeilFrobeniusPullback D C.l C.different X.obj E)
        (A.rational.comparison ((fiberModels D).map f)
          (FrobeniusExchange.geometricCompactification D f.hom c₀) c).hom

/-- The canonical common pullback-composition component, with inherited prime units.
Source: node proof step 3 (blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def commonPullComponent (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    {X Y : Models D} (f : X ⟶ Y)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      (D.geometricFiber Y.obj).left) :=
  letI := fun x ↦ sfWeilPrimeInvertible D C.l C.different X.obj x
  letI := fun y ↦ sfWeilPrimeInvertible D C.l C.different Y.obj y
  (pullbackTensorCommonComposition C.l C.Qbar (FrobeniusExchange.fiberMap D f.hom)
    (D.geometricFrobenius X.obj).hom K).symm ≪≫
    eqToIso (congrArg
      (fun m : (D.geometricFiber X.obj).left ⟶ (D.geometricFiber Y.obj).left ↦
        (commonStageDerivedPullback C.l C.Qbar m).obj K)
      (D.frobenius_square_cartesian X.obj Y.obj f.hom).2.2.2.2.1) ≪≫
    pullbackTensorCommonComposition C.l C.Qbar (D.geometricFrobenius Y.obj).hom
      (FrobeniusExchange.fiberMap D f.hom) K

/-- Normalizations fixing the standard common comparisons, rather than arbitrary isomorphisms.
Pullback uses its actual compositors, direct image their adjunction mate, and support the
actual proper/open Frobenius exchange of the indexed model compactification. Conjugation
specifies its value at any geometric compactification from that same model anchor only.
Agreement between different model anchors is a conclusion, not a normalization hypothesis.
No equivariance equation for an exchange or compositor is assumed here.
Source: node statement, canonical comparisons and compactification changes
(blueprint: lem-pod-semilinear-exchange-cube-coherence). -/
def commonNormalized (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (A : SixFunctorCommonStages D C)
    (L : Comparisons A.commonStage
      (fun X : Models D ↦
        sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar)) : Prop :=
  (∀ {X Y : Models D} (f : X ⟶ Y)
      (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
      (D.geometricFiber Y.obj).left),
    HEq ((L.pull f).app K) (commonPullComponent D C f K)) ∧
  (∀ {X Y : Models D} (f : X ⟶ Y),
    (L.direct f).hom = (mateEquiv
      (A.commonStage.pullDirectAdjunction ((fiberModels D).map f))
      (A.commonStage.pullDirectAdjunction ((fiberModels D).map f)) (L.pull f).inv).natTrans) ∧
  (∀ {X Y : Models D} (f : X ⟶ Y)
      [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
      (c₀ : Compactification f.hom.left)
      (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar
        (D.geometricFiber X.obj).left),
    HEq ((L.support f c₀ (FrobeniusExchange.geometricCompactification D f.hom c₀)).hom.app K)
      ((FrobeniusExchange.frobeniusCommonStage D C.l C.different f.hom
        (FrobeniusExchange.frobeniusCompactModel D f.hom c₀) C.Qbar).app K)) ∧
  ∀ {X Y : Models D} (f : X ⟶ Y) (c₀ : Compactification f.hom.left)
      (c : Compactification ((fiberModels D).map f).hom.left),
    (L.support f c₀ c).hom =
      Functor.whiskerRight
        (A.commonStage.comparison ((fiberModels D).map f) c
          (FrobeniusExchange.geometricCompactification D f.hom c₀)).hom
        (sfCommonStageWeilFrobeniusPullback D C.l C.different Y.obj C.Qbar) ≫
      (L.support f c₀ (FrobeniusExchange.geometricCompactification D f.hom c₀)).hom ≫
      Functor.whiskerLeft (sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar)
        (A.commonStage.comparison ((fiberModels D).map f)
          (FrobeniusExchange.geometricCompactification D f.hom c₀) c).hom

end WeilConjectures.PodExchangeCube
