/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.ConstructibleProjectionMates
public import Sheaf.Paper.CtfCoefficientStageSelectors
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.FinitePullbackTensorComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Relative-product coefficient factor squares

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-kunneth-relative,
the six displayed factors and the following coefficient/proper compatibility sentence
(blueprint: def-sf-relative-product-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w v' w'
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures

/-- The Cartesian corner is the recorded scheme fibre product, with its given
projections. Source: T = X ×_B Y in the relative product display
(blueprint: def-sf-relative-product-factors). -/
def relativeProductFibreProductIso {D : FiniteFieldDatum.{u}}
    (Q : SixFunctorCompactifiedSquare D) :
    Q.X'.obj.left ≅ pullback Q.f.hom.left Q.g.hom.left :=
  Q.square.isoPullback

/-- The operations needed by the relative-product chain. Pullback is requested only
for separated maps, the domain on which the datum supplies finite-Tor preservation.
Source: the six displayed factors
(blueprint: def-sf-relative-product-factors). -/
structure RelativeProductStage (D : FiniteFieldDatum.{u})
    (B : SixFunctorSpace D → Type v) [∀ X, Category.{w} (B X)] where
  pull : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    IsSeparated f.hom.left → B Y ⥤ B X
  support : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    Compactification f.hom.left → B X ⥤ B Y
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification (f ≫ g).hom.left),
    support (f ≫ g) ch ≅ support f cf ⋙ support g cg

/-- Primitive comparisons, before forming any of the seven composites.
Source: A5 and the coefficient comparisons defining c_i
(blueprint: def-sf-relative-product-factors). -/
structure RelativeProductComparison {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    (S : RelativeProductStage D B) (S' : RelativeProductStage D B')
    (F : ∀ X, B X ⥤ B' X) where
  pull : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left),
    S.pull f hf ⋙ F X ≅ F Y ⋙ S'.pull f hf
  support : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left), S.support f c ⋙ F Y ≅ F X ⋙ S'.support f c

/-- Operation expressions occurring in the seven displayed objects. The two leaves
are the two inputs, not newly chosen derived objects.
Source: the displayed relative-product chain
(blueprint: def-sf-relative-product-factors). -/
inductive RelativeProductTerm (D : FiniteFieldDatum.{u}) (X Y : SixFunctorSpace D) :
    SixFunctorSpace D → Type (u + 1)
  | left : RelativeProductTerm D X Y X
  | right : RelativeProductTerm D X Y Y
  | pull {U V : SixFunctorSpace D} (f : U ⟶ V) (hf : IsSeparated f.hom.left) :
      RelativeProductTerm D X Y V → RelativeProductTerm D X Y U
  | support {U V : SixFunctorSpace D} (f : U ⟶ V) (c : Compactification f.hom.left) :
      RelativeProductTerm D X Y U → RelativeProductTerm D X Y V
  | tensor {U : SixFunctorSpace D} :
      RelativeProductTerm D X Y U → RelativeProductTerm D X Y U → RelativeProductTerm D X Y U

/-- Evaluate expressions using exactly the given operations. This simultaneously
records their action on objects and on both input morphisms.
Source: the displayed relative-product chain
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductTerm.eval {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ U, Category.{w} (B U)]
    (S : RelativeProductStage D B) (T : ∀ U, B U × B U ⥤ B U)
    {X Y U : SixFunctorSpace D} : RelativeProductTerm D X Y U → B X × B Y ⥤ B U
  | .left => CategoryTheory.Prod.fst _ _
  | .right => CategoryTheory.Prod.snd _ _
  | .pull f hf a => a.eval S T ⋙ S.pull f hf
  | .support f c a => a.eval S T ⋙ S.support f c
  | .tensor a b => (a.eval S T).prod' (b.eval S T) ⋙ T _

/-- The seven expressions D0,...,D6. A Cartesian square presents the fibre product;
its primed vertical and horizontal maps are v and u respectively. The chosen
compactifications only evaluate the datum's supplied compact-support functors.
Source: the seven objects preceding the six-factor assertion
(blueprint: def-sf-relative-product-factors). -/
def relativeProductTerms {D : FiniteFieldDatum.{u}} (Q : SixFunctorCompactifiedSquare D)
    [hg : IsSeparated Q.g.hom.left] [hu : IsSeparated Q.g'.hom.left]
    [hv : IsSeparated Q.f'.hom.left]
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :
    Fin 7 → RelativeProductTerm D Q.X Q.Y' Q.Y
  | 0 => .support (Q.f' ≫ Q.g) ch
      (.tensor (.pull Q.g' hu .left) (.pull Q.f' hv .right))
  | 1 => .support Q.g cg (.support Q.f' Q.compactification'
      (.tensor (.pull Q.g' hu .left) (.pull Q.f' hv .right)))
  | 2 => .support Q.g cg
      (.tensor (.support Q.f' Q.compactification' (.pull Q.g' hu .left)) .right)
  | 3 => .support Q.g cg
      (.tensor (.pull Q.g hg (.support Q.f Q.compactification .left)) .right)
  | 4 => .support Q.g cg
      (.tensor .right (.pull Q.g hg (.support Q.f Q.compactification .left)))
  | 5 => .tensor (.support Q.g cg .right) (.support Q.f Q.compactification .left)
  | 6 => .tensor (.support Q.f Q.compactification .left) (.support Q.g cg .right)

/-- The recursively assembled operation comparison at every displayed expression.
No comparison of whole relative-product maps is supplied as data: only the primitive
pullback, support and tensor comparisons are used.
Source: definition of c_i in the coefficient-factor assertion
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductTerm.coefficientIso {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ U, Category.{w} (B U)]
    {B' : SixFunctorSpace D → Type v'} [∀ U, Category.{w'} (B' U)]
    {S : RelativeProductStage D B} {S' : RelativeProductStage D B'}
    {T : ∀ U, B U × B U ⥤ B U} {T' : ∀ U, B' U × B' U ⥤ B' U}
    {F : ∀ U, B U ⥤ B' U} (C : RelativeProductComparison S S' F)
    (t : ∀ U, T U ⋙ F U ≅ (F U).prod (F U) ⋙ T' U)
    {X Y U : SixFunctorSpace D} (a : RelativeProductTerm D X Y U) :
    a.eval S T ⋙ F U ≅ (F X).prod (F Y) ⋙ a.eval S' T' := by
  induction a with
  | left => exact Iso.refl _
  | right => exact Iso.refl _
  | pull f hf a ih =>
      exact sixFunctorCompositeRealization ih (C.pull f hf)
  | support f c a ih =>
      exact sixFunctorCompositeRealization ih (C.support f c)
  | tensor a b ia ib =>
      exact Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (t _) ≪≫
        Functor.isoWhiskerRight (((prodFunctorToFunctorProd _ _ _).mapIso (Iso.prod ia ib))) _ ≪≫
        Iso.refl _


/-- Source of the supplied projection transformation in uncurried coordinates.
Source: def-sf-pf and the displayed inverse projection factors
(blueprint: def-sf-relative-product-factors). -/
def relativeProjectionSource {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ U, Category.{w} (B U)]
    (S : RelativeProductStage D B) (T : ∀ U, B U × B U ⥤ B U)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (_hf : IsSeparated f.hom.left)
    (c : Compactification f.hom.left) :
    B X × B Y ⥤ B Y :=
  ((CategoryTheory.Prod.fst _ _ ⋙ S.support f c).prod'
    (CategoryTheory.Prod.snd _ _)) ⋙ T Y

/-- Target of the same supplied projection transformation.
Source: def-sf-pf and the displayed inverse projection factors
(blueprint: def-sf-relative-product-factors). -/
def relativeProjectionTarget {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ U, Category.{w} (B U)]
    (S : RelativeProductStage D B) (T : ∀ U, B U × B U ⥤ B U)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left)
    (c : Compactification f.hom.left) :
    B X × B Y ⥤ B Y :=
  ((CategoryTheory.Prod.fst _ _).prod'
    (CategoryTheory.Prod.snd _ _ ⋙ S.pull f hf) ⋙ T X) ⋙ S.support f c

/-- The six individual factors as natural isomorphisms of the two input variables.
The inputs `projection` and `exchange` are the supplied transformations in their
isomorphism form, with their direction retained; they are inverted only where the
blueprint inverts them. The two remaining inputs are the actual tensor symmetries.
Source: the displayed six-factor relative-product chain
(blueprint: def-sf-relative-product-factors). -/
def relativeProductFactors {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ U, Category.{w} (B U)]
    (S : RelativeProductStage D B) (T : ∀ U, B U × B U ⥤ B U)
    (projection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (hf : IsSeparated f.hom.left) (c : Compactification f.hom.left),
      relativeProjectionSource S T f hf c ≅ relativeProjectionTarget S T f hf c)
    (symmetry : ∀ U, T U ≅ (CategoryTheory.Prod.swap _ _) ⋙ T U)
    (Q : SixFunctorCompactifiedSquare D)
    [hg : IsSeparated Q.g.hom.left] [hu : IsSeparated Q.g'.hom.left]
    [hv : IsSeparated Q.f'.hom.left]
    (exchange : S.support Q.f Q.compactification ⋙ S.pull Q.g hg ≅
      S.pull Q.g' hu ⋙ S.support Q.f' Q.compactification')
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :
    ∀ i : Fin 6, (relativeProductTerms Q cg ch i.castSucc).eval S T ≅
      (relativeProductTerms Q cg ch i.succ).eval S T
  | 0 => Functor.isoWhiskerLeft
      ((RelativeProductTerm.tensor
        (.pull Q.g' hu (.left : RelativeProductTerm D Q.X Q.Y' Q.X))
        (.pull Q.f' hv .right)).eval S T)
      (S.composition Q.f' Q.g Q.compactification' cg ch)
  | 1 => Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (((CategoryTheory.Prod.fst _ _ ⋙ S.pull Q.g' hu).prod'
          (CategoryTheory.Prod.snd _ _)))
        (projection Q.f' hv Q.compactification').symm) (S.support Q.g cg)
  | 2 => Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (((prodFunctorToFunctorProd _ _ _).mapIso
          (Iso.prod (Functor.isoWhiskerLeft (CategoryTheory.Prod.fst _ _) exchange.symm)
            (Iso.refl (CategoryTheory.Prod.snd _ _))))) (T Q.Y')) (S.support Q.g cg)
  | 3 => Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((CategoryTheory.Prod.fst _ _ ⋙ S.support Q.f Q.compactification ⋙ S.pull Q.g hg).prod'
          (CategoryTheory.Prod.snd _ _)) (symmetry Q.Y')) (S.support Q.g cg)
  | 4 => Functor.isoWhiskerLeft
      ((CategoryTheory.Prod.snd _ _).prod'
        (CategoryTheory.Prod.fst _ _ ⋙ S.support Q.f Q.compactification))
      (projection Q.g hg cg).symm
  | 5 => Functor.isoWhiskerLeft
      ((CategoryTheory.Prod.snd _ _ ⋙ S.support Q.g cg).prod'
        (CategoryTheory.Prod.fst _ _ ⋙ S.support Q.f Q.compactification)) (symmetry Q.Y)


/-- Finite exchange in the datum's intrinsic operation coordinates. Its source is
transported by the fixed pullback/support comparisons; its target is transported
back, followed by the specified comparison to the retained primed compactification.
Source: A2 and the finite realization convention of def-sf-datum
(blueprint: def-sf-relative-product-factors). -/
def relativeFiniteExchange
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (Q : SixFunctorCompactifiedSquare D) (K : sixFunctorFiniteCategory D C E n hn Q.X) :
    (S.finite.pull Q.g).obj ((S.finite.support Q.f Q.compactification).obj K) ⟶
      (S.finite.support Q.f' Q.compactification').obj ((S.finite.pull Q.g').obj K) := by
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let R := sixFunctorFiniteRealization D C E n hn Q.Y'
  let a := CompactSupportFiniteProjection.pullRealization S.toSixFunctorFiniteOperations Q.g
    ((S.finite.support Q.f Q.compactification).obj K) ≪≫
    R.functor.mapIso
      ((CompactSupportFiniteProjection.fixedPullComparison
        (C := C) (E := E) (n := n) Q.g).symm.app _) ≪≫
    R.functor.mapIso
      ((CompactSupportFiniteProjection.fixedDerivedPull
        (C := C) (E := E) (n := n) Q.g).mapIso
          (CompactSupportFiniteProjection.fixedSupportRealization
            S.toSixFunctorFiniteOperations Q.f Q.compactification K))
  let c := Q.compactification.ofIsPullback Q.square
  let b := CompactSupportFiniteProjection.supportRealization S.toSixFunctorFiniteOperations
    Q.f' c ((S.finite.pull Q.g').obj K) ≪≫
    R.functor.mapIso
      ((AlgebraicGeometry.ProEtale.sfFixedCompactSupport
        (Padic.coefficientExtensionRing C.l E n) c).mapIso
          (CompactSupportFiniteProjection.fixedPullRealization
            S.toSixFunctorFiniteOperations Q.g' K))
  exact ObjectProperty.homMk
    (a.hom ≫ (S.finiteExchangeProjection Q).2.1.app K ≫ b.inv) ≫
      (S.finite.comparison Q.f' c Q.compactification').hom.app
        ((S.finite.pull Q.g').obj K)

/-- Higher-stage exchange with only the datum's endpoint equalities inserted.
Source: A2, supplied-domain exchange
(blueprint: def-sf-relative-product-factors). -/
def relativeHigherExchange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {Q : SixFunctorCompactifiedSquare D} (A : SixFunctorExchangeData S T Q) (K : B Q.X) :
    (S.pull Q.g).obj ((S.support Q.f Q.compactification).obj K) ⟶
      (S.support Q.f' Q.compactification').obj ((S.pull Q.g').obj K) :=
  eqToHom (by rw [A.compactSupport, A.horizontal]; rfl) ≫
    A.stage.compactExchange.app K ≫
    eqToHom (by rw [A.compactSupport', A.horizontal']; rfl)

/-- A finite-Tor interpretation of the seven objects, with its inclusion in the
actual coefficient category. The comparison of primitive operations is fixed on
objects and arrows by the full inclusion, rather than by an arbitrary equivalence.
Source: the finite-Tor domains preceding the displayed chain
(blueprint: def-sf-relative-product-factors). -/
structure RelativeProductCoordinates {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (O : SixFunctorPushStage D B) (P : ∀ X, ObjectProperty (B X))
    (A : ∀ X, B X ⥤ (P X).FullSubcategory ⥤ B X) where
  operations : RelativeProductStage D (fun X ↦ (P X).FullSubcategory)
  pullNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsSeparated f.hom.left),
    operations.pull f hf ⋙ (P X).ι = (P Y).ι ⋙ O.pull f
  supportNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left),
    operations.support f c ⋙ (P Y).ι = (P X).ι ⋙ O.support f c
  compositionNormalization : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification (f ≫ g).hom.left) K,
    HEq ((P Z).ι.map ((operations.composition f g cf cg ch).hom.app K))
      ((O.composition f g cf cg ch).hom.app K.obj)
  tensor : ∀ X, (P X).FullSubcategory × (P X).FullSubcategory ⥤ (P X).FullSubcategory
  tensorNormalization : ∀ X,
    tensor X ⋙ (P X).ι =
      ((P X).ι.prod (𝟭 (P X).FullSubcategory)) ⋙ Functor.uncurry.obj (A X)

/-- The actual closed structure at the selected coefficient stage.
Source: A3 and the signed symmetry in the relative-product chain
(blueprint: def-sf-relative-product-factors). -/
def relativeProductClosed
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage) (X : SixFunctorSpace D) :
    SixFunctorClosedDomain
      (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X)
      (PodCoefficientStage.homPairs (S := S.toSixFunctorOperationDatum) s X)
      (PodCoefficientStage.internalHom (S := S.toSixFunctorOperationDatum) s X) := by
  cases s with
  | finite => exact S.finiteClosed X
  | integral => exact S.integralClosed X
  | rational => exact S.rationalClosed X
  | common => exact S.commonClosed X

/-- The two-input finite-Tor tensor as presented by the datum's closed structure.
Its symmetry is the supplied signed symmetry, including odd-degree inputs.
Source: A6 and the two symmetry factors
(blueprint: def-sf-relative-product-factors). -/
def relativeProductClosedTensor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    (X : SixFunctorSpace D) :
    (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory ×
      (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory ⥤
        (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory :=
  (relativeProductClosed S s X).closed.tensor

/-- Read the specified projection map in the ambient coordinates of each stage.
At the finite stage this is the normalized fixed-coefficient projection conjugate;
at higher stages it is the supplied proper-mate/open-extension composite.
Source: def-sf-pf and the two inverse projection factors
(blueprint: def-sf-relative-product-factors). -/
def relativeProductProjection
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (_hf : IsSeparated f.hom.left)
    (c : Compactification f.hom.left)
    (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory)
    (L : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Y).FullSubcategory) :
    Arrow (PodCoefficientStage.category (_S := S.toSixFunctorOperationDatum) s Y) := by
  cases s with
  | finite =>
      exact Arrow.mk (CompactSupportFiniteProjection.component
        S.toSixFunctorFiniteOperations f c K.obj ⟨L.obj.obj, L.property⟩)
  | integral =>
      exact Arrow.mk (compactSupportProjectionComponent S.higher.integralExchange f c K.obj L.obj)
  | rational =>
      exact Arrow.mk (compactSupportProjectionComponent S.higher.rationalExchange f c K.obj L.obj)
  | common =>
      exact Arrow.mk
        (compactSupportProjectionComponent S.closure.commonStageExchange f c K.obj L.obj)

/-- The specified exchange, before restriction to the full finite-Tor subcategory.
Source: A2 and the inverse exchange factor
(blueprint: def-sf-relative-product-factors). -/
def relativeProductExchange
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    (Q : SixFunctorCompactifiedSquare D)
    (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q.X).FullSubcategory) :
    Arrow (PodCoefficientStage.category (_S := S.toSixFunctorOperationDatum) s Q.Y') := by
  cases s with
  | finite => exact Arrow.mk (relativeFiniteExchange S.toSixFunctorOperationDatum Q K.obj)
  | integral => exact Arrow.mk (relativeHigherExchange (S.higher.integralExchange Q) K.obj)
  | rational => exact Arrow.mk (relativeHigherExchange (S.higher.rationalExchange Q) K.obj)
  | common => exact Arrow.mk (relativeHigherExchange (S.closure.commonStageExchange Q) K.obj)

/-- The canonical signed symmetry: finite coefficients use the derived braiding
through the fixed realization, integral coefficients the completed braiding,
and field coefficients its localization or common-stage class.
Source: the two signed symmetry factors
(blueprint: def-sf-relative-product-factors). -/
def relativeProductSignedSymmetry
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    (X : SixFunctorSpace D) [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    (K L : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory) :
    Arrow (PodCoefficientStage.category (_S := S.toSixFunctorOperationDatum) s X) := by
  cases s with
  | finite =>
      let V := CompactSupportFiniteProjection.realization (C := C) (E := E) (n := n)
        (hn := hn) X
      let T := CompactSupportFiniteProjection.partialTensor S.toSixFunctorFiniteOperations X
      exact Arrow.mk (show (T.obj K.obj).obj ⟨L.obj.obj, L.property⟩ ⟶
          (T.obj L.obj).obj ⟨K.obj.obj, K.property⟩ from
        ObjectProperty.homMk (V.functor.map
          ((@BraidedCategory.braiding _ _ _
            (_root_.DerivedCategory.braidedCategory' _)
            (V.inverse.obj K.obj.obj) (V.inverse.obj L.obj.obj)).hom)))
  | integral =>
      exact Arrow.mk (pullbackTensorIntegralBraiding C.l E X.obj.left K.obj L.obj).hom
  | rational =>
      exact Arrow.mk (pullbackTensorRationalBraiding C.l E X.obj.left K.obj L.obj).hom
  | common =>
      exact Arrow.mk (pullbackTensorCommonBraiding C.l C.Qbar X.obj.left K.obj L.obj).hom

/-- A presentation on the actual full finite-Tor subcategories. Its projection and
exchange are required to be exactly the specified maps after full inclusion, and
its tensor and signed symmetry are those of the datum's closed structure.
Source: the six factors and their naturality assertion
(blueprint: def-sf-relative-product-factors). -/
structure RelativeProductPresentation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    (Q : SixFunctorCompactifiedSquare D)
    [hg : IsSeparated Q.g.hom.left] [hu : IsSeparated Q.g'.hom.left]
    [hv : IsSeparated Q.f'.hom.left] where
  coordinates : RelativeProductCoordinates
    (PodCoefficientStage.operations S.toSixFunctorOperationDatum s)
    (PodCoefficientStage.domain S.toSixFunctorOperationDatum s)
    (PodCoefficientStage.tensor S.toSixFunctorOperationDatum s)
  tensorClosed : ∀ X, coordinates.tensor X ≅ relativeProductClosedTensor S s X
  projection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsSeparated f.hom.left) (c : Compactification f.hom.left),
    relativeProjectionSource coordinates.operations coordinates.tensor f hf c ≅
      relativeProjectionTarget coordinates.operations coordinates.tensor f hf c
  projection_eq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsSeparated f.hom.left) (c : Compactification f.hom.left)
    (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory)
    (L : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Y).FullSubcategory),
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Y).ι.map
      ((projection f hf c).hom.app (K, L))) (relativeProductProjection S s f hf c K L).hom
  exchange : coordinates.operations.support Q.f Q.compactification ⋙
    coordinates.operations.pull Q.g hg ≅
      coordinates.operations.pull Q.g' hu ⋙
        coordinates.operations.support Q.f' Q.compactification'
  exchange_eq : ∀ K,
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q.Y').ι.map
      (exchange.hom.app K)) (relativeProductExchange S s Q K).hom
  symmetry : ∀ X, coordinates.tensor X ≅
    CategoryTheory.Prod.swap _ _ ⋙ coordinates.tensor X
  signedNormalization : ∀ (X : SixFunctorSpace D)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)] K L,
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).ι.map
      ((symmetry X).hom.app (K, L))) (relativeProductSignedSymmetry S s X K L).hom
  symmetry_eq : ∀ X K L,
    (symmetry X).hom.app (K, L) ≫ (tensorClosed X).hom.app (L, K) =
      (tensorClosed X).hom.app (K, L) ≫
        ((relativeProductClosed S s X).symmetric.braiding K L).hom

/-- The six factors in the normalized finite-Tor coordinates.
Source: the six displayed arrows, with their supplied-map normalization
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductPresentation.factors
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :=
  relativeProductFactors R.coordinates.operations R.coordinates.tensor R.projection R.symmetry
    Q R.exchange cg ch


/-- A primitive coefficient comparison on finite-Tor coordinates. The coefficient
functor and all primitive comparisons are retained before any relative-product
factor is formed. The last four equations are precisely the primitive A5
composition, projection, exchange and signed-tensor compatibility requirements;
none assumes a square for a relative-product factor or its composite.
Source: A5 and the coefficient comparison paragraph
(blueprint: def-sf-relative-product-factors). -/
structure RelativeProductCoefficientData
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (R' : RelativeProductPresentation S' s' Q) where
  functor : ∀ X,
    (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory ⥤
      (PodCoefficientStage.domain S'.toSixFunctorOperationDatum s' X).FullSubcategory
  operations : RelativeProductComparison R.coordinates.operations R'.coordinates.operations functor
  ambientFunctor : ∀ X,
    PodCoefficientStage.category (_S := S.toSixFunctorOperationDatum) s X ⥤
      PodCoefficientStage.category (_S := S'.toSixFunctorOperationDatum) s' X
  ambientOperations : SixFunctorCoefficientComparison
    (PodCoefficientStage.operations S.toSixFunctorOperationDatum s)
    (PodCoefficientStage.operations S'.toSixFunctorOperationDatum s') ambientFunctor
  functorNormalization : ∀ X,
    functor X ⋙ (PodCoefficientStage.domain S'.toSixFunctorOperationDatum s' X).ι =
      (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).ι ⋙ ambientFunctor X
  pullNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsSeparated f.hom.left) K,
    HEq ((PodCoefficientStage.domain S'.toSixFunctorOperationDatum s' X).ι.map
      ((operations.pull f hf).hom.app K))
      ((ambientOperations.directAdjunction f).left.hom.app K.obj)
  supportNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) K,
    HEq ((PodCoefficientStage.domain S'.toSixFunctorOperationDatum s' Y).ι.map
      ((operations.support f c).hom.app K))
      ((ambientOperations.supportAdjunction f c).left.hom.app K.obj)
  tensor : ∀ X, R.coordinates.tensor X ⋙ functor X ≅
    (functor X).prod (functor X) ⋙ R'.coordinates.tensor X

  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification (f ≫ g).hom.left) K,
    (functor Z).map ((R.coordinates.operations.composition f g cf cg ch).hom.app K) ≫
        (operations.support g cg).hom.app ((R.coordinates.operations.support f cf).obj K) ≫
        (R'.coordinates.operations.support g cg).map ((operations.support f cf).hom.app K) =
      (operations.support (f ≫ g) ch).hom.app K ≫
        (R'.coordinates.operations.composition f g cf cg ch).hom.app ((functor X).obj K)
  projection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsSeparated f.hom.left) (c : Compactification f.hom.left) K L,
    (functor Y).map ((R.projection f hf c).hom.app (K, L)) ≫
        (operations.support f c).hom.app
          ((R.coordinates.tensor X).obj (K, (R.coordinates.operations.pull f hf).obj L)) ≫
        (R'.coordinates.operations.support f c).map
          ((tensor X).hom.app (K, (R.coordinates.operations.pull f hf).obj L) ≫
            (R'.coordinates.tensor X).map
              (Prod.mkHom (𝟙 _) ((operations.pull f hf).hom.app L))) =
      (tensor Y).hom.app ((R.coordinates.operations.support f c).obj K, L) ≫
        (R'.coordinates.tensor Y).map
          (Prod.mkHom ((operations.support f c).hom.app K) (𝟙 _)) ≫
        (R'.projection f hf c).hom.app ((functor X).obj K, (functor Y).obj L)
  exchange : ∀ K,
    (functor Q.Y').map (R.exchange.hom.app K) ≫
        (operations.support Q.f' Q.compactification').hom.app
          ((R.coordinates.operations.pull Q.g' inferInstance).obj K) ≫
        (R'.coordinates.operations.support Q.f' Q.compactification').map
          ((operations.pull Q.g' inferInstance).hom.app K) =
      (operations.pull Q.g inferInstance).hom.app
          ((R.coordinates.operations.support Q.f Q.compactification).obj K) ≫
        (R'.coordinates.operations.pull Q.g inferInstance).map
          ((operations.support Q.f Q.compactification).hom.app K) ≫
        R'.exchange.hom.app ((functor Q.X).obj K)
  symmetry : ∀ X K L,
    (functor X).map ((R.symmetry X).hom.app (K, L)) ≫
        (tensor X).hom.app (L, K) =
      (tensor X).hom.app (K, L) ≫
        (R'.symmetry X).hom.app ((functor X).obj K, (functor X).obj L)

/-- The comparison c_i is obtained recursively from the primitive pullback,
compact-support and tensor comparisons, with no independent endpoint isomorphism.
Source: definition of c_i in the individual factor squares
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.objectIso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R') (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) (i : Fin 7) :=
  (relativeProductTerms Q cg ch i).coefficientIso A.operations A.tensor

/-- The six individual commuting-square equations, rather than just compatibility
of their composite. The seven vertical maps are the recursively defined c_i.
Source: the displayed equation for every 0 <= i < 6
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.FactorSquares
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R') (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) : Prop :=
  ∀ (i : Fin 6) K L,
    (A.functor Q.Y).map ((R.factors cg ch i).hom.app (K, L)) ≫
        (A.objectIso cg ch i.succ).hom.app (K, L) =
      (A.objectIso cg ch i.castSucc).hom.app (K, L) ≫
        (R'.factors cg ch i).hom.app
          ((A.functor Q.X).obj K, (A.functor Q.Y').obj L)



/-- Restrictions of the specified proper direct images and proper identifications.
The full-inclusion equations fix the functors and maps, including the identity-open
normalization inherited from the operation datum.
Source: proper replacement paragraph
(blueprint: def-sf-relative-product-factors). -/
structure RelativeProductProperCoordinates {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {O : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty (B X)}
    {T : ∀ X, B X ⥤ (P X).FullSubcategory ⥤ B X}
    (R : RelativeProductCoordinates O P T) where
  direct : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y),
    IsProper f.hom.left → (P X).FullSubcategory ⥤ (P Y).FullSubcategory
  direct_eq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsProper f.hom.left),
    direct f hf ⋙ (P Y).ι = (P X).ι ⋙ O.direct f
  identification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsProper f.hom.left) (c : Compactification f.hom.left),
    R.operations.support f c ≅ direct f hf
  identification_eq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsProper f.hom.left) (c : Compactification f.hom.left) K,
    HEq ((P Y).ι.map ((identification f hf c).hom.app K))
      ((@SixFunctorPushStage.properIdentification _ _ _ O _ _ f hf c).hom.app K.obj)

namespace RelativeProductProperCoordinates
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {O : SixFunctorPushStage D B} {P : ∀ X, ObjectProperty (B X)}
  {T : ∀ X, B X ⥤ (P X).FullSubcategory ⥤ B X}
  {R : RelativeProductCoordinates O P T} (J : RelativeProductProperCoordinates R)
  (q : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → Bool)
  (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y), q f = true → IsProper f.hom.left)

/-- Replace precisely the selected proper occurrences; no other support is replaced.
Source: arbitrary proper structural replacements, including only h proper
(blueprint: def-sf-relative-product-factors). -/
def support {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) : (P X).FullSubcategory ⥤ (P Y).FullSubcategory :=
  if h : q f = true then J.direct f (hq f h) else R.operations.support f c

/-- The specified proper identification, or the identity at an unreplaced occurrence.
Source: the maps rho in proof step 6
(blueprint: def-sf-relative-product-factors). -/
def replacement {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) :
    R.operations.support f c ≅ J.support q hq f c := by
  unfold support
  split
  next h => exact J.identification f (hq f h) c
  next => exact Iso.refl _

/-- The same operation interpretation with selected support occurrences replaced.
Its compositor is the supplied compositor with the specified proper maps inserted.
Source: proper-normalized composition factor
(blueprint: def-sf-relative-product-factors). -/
def stage : RelativeProductStage D (fun X ↦ (P X).FullSubcategory) where
  pull := R.operations.pull
  support := J.support q hq
  composition f g cf cg ch :=
    (J.replacement q hq (f ≫ g) ch).symm ≪≫
      R.operations.composition f g cf cg ch ≪≫
      Functor.isoWhiskerRight (J.replacement q hq f cf) (R.operations.support g cg) ≪≫
      Functor.isoWhiskerLeft (J.support q hq f cf) (J.replacement q hq g cg)

/-- Primitive replacement comparison, with identity on pullbacks and tensor.
Source: recursive definition of the maps j_i
(blueprint: def-sf-relative-product-factors). -/
def comparison : RelativeProductComparison R.operations (J.stage q hq) (fun _X ↦ 𝟭 _) where
  pull _ _ := Iso.refl _
  support := J.replacement q hq

/-- Insert proper identifications recursively, also at nested occurrences and Q.
Source: the seven j_i in proof step 6
(blueprint: def-sf-relative-product-factors). -/
def objectIso {X Y U : SixFunctorSpace D} (t : RelativeProductTerm D X Y U) :
    t.eval R.operations R.tensor ≅ t.eval (J.stage q hq) R.tensor :=
  t.coefficientIso (J.comparison q hq) (fun _ ↦ Iso.refl _)
end RelativeProductProperCoordinates

/-- The normalized six factors are the conjugates by the recursively inserted j_i.
This definition works for any subset of proper structural maps; in particular it
does not infer that f or g is proper from the properness of h.
Source: proper factor identification in proof step 6
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductPresentation.properFactors
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (J : RelativeProductProperCoordinates R.coordinates)
    (q : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → Bool)
    (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y), q f = true → IsProper f.hom.left)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) (i : Fin 6) :=
  (J.objectIso q hq (relativeProductTerms Q cg ch i.castSucc)).symm ≪≫
    R.factors cg ch i ≪≫ J.objectIso q hq (relativeProductTerms Q cg ch i.succ)

/-- The canonical direct-image exchange, the mate of the square's pullback
comparison under the specified pullback/direct-image adjunctions.
Source: proper-base-change factor in proof step 7
(blueprint: def-sf-relative-product-factors). -/
def relativeProductDirectExchange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (O : SixFunctorPushStage D B) (Q : SixFunctorCompactifiedSquare D) :
    O.direct Q.f ⋙ O.pull Q.g ⟶ O.pull Q.g' ⋙ O.direct Q.f' :=
  (mateEquiv (O.pullDirectAdjunction Q.f) (O.pullDirectAdjunction Q.f')
    (TwoSquare.mk _ _ _ _
      ((O.pullComposition Q.f' Q.g).symm ≪≫
        eqToIso (congrArg (fun e ↦ O.pull e) Q.squareComm.symm) ≪≫
          O.pullComposition Q.g' Q.f).hom)).natTrans

/-- The specified direct-image projection in each coefficient convention.
Source: proper projection identification in proof step 6
(blueprint: def-sf-relative-product-factors). -/
def relativeProductDirectProjection
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (s : PodCoefficientStage)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s X).FullSubcategory)
    (L : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Y).FullSubcategory) :
    Arrow (PodCoefficientStage.category (_S := S.toSixFunctorOperationDatum) s Y) := by
  cases s with
  | finite => exact Arrow.mk (CompactSupportFiniteProjection.properComponent
      S.toSixFunctorFiniteOperations f K.obj ⟨L.obj.obj, L.property⟩)
  | integral =>
      exact Arrow.mk (compactSupportProperProjection S.higher.integralExchange f K.obj L.obj)
  | rational =>
      exact Arrow.mk (compactSupportProperProjection S.higher.rationalExchange f K.obj L.obj)
  | common =>
      exact Arrow.mk (compactSupportProperProjection S.closure.commonStageExchange f K.obj L.obj)

/-- Coefficient comparison after the proper replacements, obtained by inserting
exactly the same proper identifications on both sides of the original c_i.
Source: proper coefficient square in proof step 8
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.properObjectIso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R')
    (J : RelativeProductProperCoordinates R.coordinates)
    (J' : RelativeProductProperCoordinates R'.coordinates)
    (q : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → Bool)
    (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y), q f = true → IsProper f.hom.left)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) (i : Fin 7) :=
  Functor.isoWhiskerRight
      (J.objectIso q hq (relativeProductTerms Q cg ch i)).symm (A.functor Q.Y) ≪≫
    A.objectIso cg ch i ≪≫
    Functor.isoWhiskerLeft ((A.functor Q.X).prod (A.functor Q.Y'))
      (J'.objectIso q hq (relativeProductTerms Q cg ch i))





/-- The normalized projection is obtained by the specified proper identification
at its input and output, with the same tensor and pullback.
Source: proper projection factors in proof step 6
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductPresentation.properProjection
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (J : RelativeProductProperCoordinates R.coordinates)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left)
    (hp : IsProper f.hom.left) (c : Compactification f.hom.left) K L :=
  (R.coordinates.tensor Y).map
      (Prod.mkHom ((J.identification f hp c).inv.app K) (𝟙 L)) ≫
    (R.projection f hf c).hom.app (K, L) ≫
    (J.identification f hp c).hom.app
      ((R.coordinates.tensor X).obj (K, (R.coordinates.operations.pull f hf).obj L))

/-- Conjugate the compact-support exchange by the specified proper maps.
Source: proper exchange factor in proof step 7
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductPresentation.properExchange
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [hg : IsSeparated Q.g.hom.left] [hu : IsSeparated Q.g'.hom.left]
    [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (J : RelativeProductProperCoordinates R.coordinates)
    (hf : IsProper Q.f.hom.left) (hv : IsProper Q.f'.hom.left) K :=
  (R.coordinates.operations.pull Q.g hg).map
      ((J.identification Q.f hf Q.compactification).inv.app K) ≫
    R.exchange.hom.app K ≫
    (J.identification Q.f' hv Q.compactification').hom.app
      ((R.coordinates.operations.pull Q.g' hu).obj K)

/-- The individual proper-normalized factor squares, with the same recursively
inserted coefficient and proper comparisons.
Source: proper coefficient compatibility, proof step 8
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.ProperFactorSquares
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R')
    (J : RelativeProductProperCoordinates R.coordinates)
    (J' : RelativeProductProperCoordinates R'.coordinates)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) : Prop :=
  ∀ (q : ∀ {X Y : SixFunctorSpace D}, (X ⟶ Y) → Bool)
    (hq : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y), q f = true → IsProper f.hom.left)
    (i : Fin 6) K L,
    (A.functor Q.Y).map ((R.properFactors J q hq cg ch i).hom.app (K, L)) ≫
        (A.properObjectIso J J' q hq cg ch i.succ).hom.app (K, L) =
      (A.properObjectIso J J' q hq cg ch i.castSucc).hom.app (K, L) ≫
        (R'.properFactors J' q hq cg ch i).hom.app
          ((A.functor Q.X).obj K, (A.functor Q.Y').obj L)

/-- The proper projection and exchange are the specified direct-image maps, not
arbitrary isomorphisms between their endpoints.
Source: proper normalization clauses, proof steps 6--7
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductPresentation.ProperNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q)
    (J : RelativeProductProperCoordinates R.coordinates) : Prop :=
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left)
    (hp : IsProper f.hom.left) (c : Compactification f.hom.left) K L,
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Y).ι.map
      (R.properProjection J f hf hp c K L))
      (@relativeProductDirectProjection _ _ _ _ _ _ _ _ S s _ _ f hp K L).hom) ∧
  (∀ hf : IsProper Q.f.hom.left, ∃ hv : IsProper Q.f'.hom.left, ∀ K,
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q.Y').ι.map
      (R.properExchange J hf hv K))
      ((relativeProductDirectExchange
        (PodCoefficientStage.operations S.toSixFunctorOperationDatum s) Q).app K.obj))

/-- Coefficient change after inserting the specified proper identifications
is the original direct-image adjunction comparison, including its component map.
Source: A5 for proper identifications, proof step 8
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.ProperComparisonNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R')
    (J : RelativeProductProperCoordinates R.coordinates)
    (J' : RelativeProductProperCoordinates R'.coordinates) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hp : IsProper f.hom.left)
    (c : Compactification f.hom.left) K,
    HEq ((PodCoefficientStage.domain S'.toSixFunctorOperationDatum s' Y).ι.map
      ((A.functor Y).map ((J.identification f hp c).inv.app K) ≫
        (A.operations.support f c).hom.app K ≫
        (J'.identification f hp c).hom.app ((A.functor X).obj K)))
      ((A.ambientOperations.directAdjunction f).right.hom.app K.obj)

/-- The ringed-site tensor model is the explicit restriction of the datum's actual
K-flat model, retaining all representative components. Source: the canonical finite
tensor comparison in A5 (blueprint: def-sf-relative-product-factors). -/
def relativeProductFiniteTensorModel
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn) (X : SixFunctorSpace D) :
    Scheme.ProEtaleTensorModel X.obj.left
      (Scheme.proEtaleConstantRing X.obj.left (Padic.coefficientExtensionRing C.l E n)) where
  tensor := (S.finiteModel X).closed.tensor
  representative := Functor.isoWhiskerLeft
    ((ObjectProperty.ιOfLE (fun P hP ↦ pullbackTensorIndependent X.obj.left
      (Scheme.proEtaleConstantRing X.obj.left (Padic.coefficientExtensionRing C.l E n))
      ⟨P, hP⟩)).prod (ObjectProperty.ιOfLE (fun P hP ↦ pullbackTensorIndependent X.obj.left
      (Scheme.proEtaleConstantRing X.obj.left (Padic.coefficientExtensionRing C.l E n))
      ⟨P, hP⟩))) (S.finiteModel X).models.comparison

/-- Transport the finite tensor through the specified closed-model comparison.
Source: A5 on the finite-Tor domain
(blueprint: def-sf-relative-product-factors). -/
def relativeProductFiniteTensorIso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S .finite Q) (X : SixFunctorSpace D)
    (K L : (S.finiteTorDomain X).FullSubcategory) :=
  ((S.finiteTorDomain X).ι ⋙
    (Scheme.intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι).mapIso
      ((R.tensorClosed X).app (K, L)) ≪≫
    (S.finiteModelComparison X).comparison.tensor.app (K, L)

/-- The recorded constant-coefficient pullback in the ringed coordinates, for
any positive exponent. Source: A5 finite comparisons
(blueprint: def-sf-relative-product-factors). -/
def relativeProductFinitePullIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PurCompactSupport.pull (PurCompactSupport.finite l E n hn) f ≅
      @Scheme.sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn) _ _ f := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ m =>
      letI := Padic.finite_coefficientExtensionRing l E (m + 1) hn
      let e := PurCompactSupport.finitePullbackIso l E m f
      letI : (Scheme.sfIntrinsicPullback (Padic.coefficientExtensionRing l E (m + 1)) f).Additive :=
        Functor.additive_of_iso e
      letI : PreservesFiniteLimits
          (Scheme.sfIntrinsicPullback (Padic.coefficientExtensionRing l E (m + 1)) f) :=
        preservesFiniteLimits_of_natIso e
      letI : PreservesFiniteColimits
          (Scheme.sfIntrinsicPullback (Padic.coefficientExtensionRing l E (m + 1)) f) :=
        preservesFiniteColimits_of_natIso e
      exact Functor.mapDerivedCategoryNatIso e

/-- The recorded proper/open presentation comparison at any positive exponent.
Source: A5 finite comparisons
(blueprint: def-sf-relative-product-factors). -/
def relativeProductFiniteImageIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    PurCompactSupport.image (PurCompactSupport.finite l E n hn) c ≅
      @Scheme.sfIntrinsicCompactSupport _ _ _ c (Padic.coefficientExtensionRing l E n) _
        (Padic.finite_coefficientExtensionRing l E n hn) := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ m => exact PurCompactSupport.finiteImageIso l E m c

/-- Finite scalar comparisons are the existing scalar/pullback balancing, the
proper/open scalar mate, and the signed K-flat tensor balancing. All transports
are the recorded finite-operation and closed-model transports; no free endpoint
isomorphism enters. Source: finite reduction and scalar extension in A5
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.FiniteScalarNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S .finite Q}
    {R' : RelativeProductPresentation S' .finite Q}
    (A : RelativeProductCoefficientData R R')
    (c : PurCompactSupport.Change (PurCompactSupport.finite C.l E n hn)
      (PurCompactSupport.finite C.l E' n' hn'))
 : Prop :=
    (∀ X, HEq
      (A.ambientFunctor X ⋙
        (Scheme.intrinsicFiniteTorsionConstructible C.l E' n' hn' X.obj.left).ι)
      ((Scheme.intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι ⋙
        Scheme.pbcDerivedExtend (c.map X.obj.left))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) K,
      HEq
        ((Scheme.intrinsicFiniteTorsionConstructible C.l E' n' hn' X.obj.left).ι.map
            ((A.ambientOperations.directAdjunction f).left.hom.app K) ≫
          (S'.finitePullback f).hom.app ((A.ambientFunctor Y).obj K))
        ((Scheme.pbcDerivedExtend (c.map X.obj.left)).map
            ((S.finitePullback f).hom.app K) ≫
          (Scheme.pbcDerivedExtend (c.map X.obj.left)).map
          ((relativeProductFinitePullIso C.l E n hn f.hom.left).inv.app K.obj) ≫
        (PurCompactSupport.scalarPull c f.hom.left).hom.app K.obj ≫
        (relativeProductFinitePullIso C.l E' n' hn' f.hom.left).hom.app
          ((Scheme.pbcDerivedExtend (c.map Y.obj.left)).obj K.obj))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (cf : Compactification f.hom.left) K,
      HEq
        ((Scheme.intrinsicFiniteTorsionConstructible C.l E' n' hn' Y.obj.left).ι.map
            ((A.ambientOperations.supportAdjunction f cf).left.hom.app K) ≫
          (S'.finiteSupport f cf).hom.app ((A.ambientFunctor X).obj K))
        ((Scheme.pbcDerivedExtend (c.map Y.obj.left)).map
            ((S.finiteSupport f cf).hom.app K) ≫
          (Scheme.pbcDerivedExtend (c.map Y.obj.left)).map
          ((relativeProductFiniteImageIso C.l E n hn cf).inv.app K.obj) ≫
        (PurCompactSupport.comparison c cf).app K.obj ≫
        (relativeProductFiniteImageIso C.l E' n' hn' cf).hom.app
          ((Scheme.pbcDerivedExtend (c.map X.obj.left)).obj K.obj))) ∧
  (∀ X K L,
      HEq
        (((S'.finiteTorDomain X).ι ⋙
            (Scheme.intrinsicFiniteTorsionConstructible C.l E' n' hn' X.obj.left).ι).map
            ((A.tensor X).hom.app (K, L)) ≫
          (relativeProductFiniteTensorIso R' X
            ((A.functor X).obj K) ((A.functor X).obj L)).hom)
        ((Scheme.pbcDerivedExtend (c.map X.obj.left)).map
            (relativeProductFiniteTensorIso R X K L).hom ≫
          (PurCompactSupport.scalarTensor (c.map X.obj.left)
            (relativeProductFiniteTensorModel S X) (relativeProductFiniteTensorModel S' X)).hom.app
              (K.obj.obj, L.obj.obj)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Completed scalar comparisons retain the published Roos-normalized pullback,
tensor and proper/open support maps. Source: scalar extension in A5
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.IntegralScalarNormalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S .integral Q}
    {R' : RelativeProductPresentation S' .integral Q}
    (A : RelativeProductCoefficientData R R') (a : E →ₐ[Padic C.l] E') : Prop :=
  (∀ X, HEq
    (A.functor X ⋙ (S'.integralFiniteTorDomain X).ι ⋙
      (sfIntegralConstructible C.l E' X.obj.left).ι)
    ((S.integralFiniteTorDomain X).ι ⋙ (sfIntegralConstructible C.l E X.obj.left).ι ⋙
      integralScalarExtension C.l E E' a X.obj.left)) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left)
    (K : (S.integralFiniteTorDomain Y).FullSubcategory)
    (hK : IsSfDerivedComplete C.l E Y.obj.left K.obj.obj)
    (hF : IsSfDerivedComplete C.l E X.obj.left
      ((integralDerivedPullback C.l E f.hom.left).obj K.obj.obj)),
    HEq (((S'.integralFiniteTorDomain X).ι ⋙
        (sfIntegralConstructible C.l E' X.obj.left).ι).map
      ((A.operations.pull f hf).hom.app K))
      (scalarPullbackCompleted C.l E E' a f.hom.left K.obj.obj hK hF).hom) ∧
  (∀ (X : SixFunctorSpace D) (K L : (S.integralFiniteTorDomain X).FullSubcategory)
    (hK : IsSfDerivedComplete C.l E X.obj.left K.obj.obj)
    (hL : IsSfDerivedComplete C.l E X.obj.left L.obj.obj)
    (hT : IsSfDerivedComplete C.l E X.obj.left
      ((integralCompletedTensor C.l E X.obj.left).obj (K.obj.obj, L.obj.obj))),
    HEq (((S'.integralFiniteTorDomain X).ι ⋙
        (sfIntegralConstructible C.l E' X.obj.left).ι).map
      ((A.tensor X).hom.app (K, L)))
      (scalarTensorCompleted C.l E E' a X.obj.left K.obj.obj L.obj.obj hK hL hT).hom) ∧
  (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated (X.obj.left ↘ Spec (.of D.k))]
    [IsSeparated (Y.obj.left ↘ Spec (.of D.k))]
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (cf : Compactification f.hom.left)
    (K : (S.integralFiniteTorDomain X).FullSubcategory),
    HEq (((S'.integralFiniteTorDomain Y).ι ⋙
        (sfIntegralConstructible C.l E' Y.obj.left).ι).map
      ((A.operations.support f cf).hom.app K))
      ((PurCompactSupport.recordedComparisonIso C.l E E' a D C.different f.hom.left cf).hom.app
        ⟨K.obj.obj, K.property⟩))

/-- The primitive comparison is the datum's recorded coefficient comparison.
In particular integral reduction targets its own finiteLevels, and its closed tensor
comparison is the recorded reductionClosedComparison, not a freely chosen tensorator.
The equations conjugate only by the two specified tensor-coordinate identifications.
Source: A5 and the canonical c_i in the coefficient paragraph
(blueprint: def-sf-relative-product-factors). -/
def RelativeProductCoefficientData.RecordedComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E E' : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] [Field E'] [Algebra (Padic C.l) E']
    [FiniteDimensional (Padic C.l) E'] {n n' : ℕ} {hn : 1 ≤ n} {hn' : 1 ≤ n'}
    {S : SixFunctorDatum D C E n hn} {S' : SixFunctorDatum D C E' n' hn'}
    {s s' : PodCoefficientStage} {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S' s' Q}
    (A : RelativeProductCoefficientData R R') : Prop :=
  (s = s' ∧ HEq S S' ∧ (∀ X, HEq (A.ambientFunctor X)
      (𝟭 (PodCoefficientStage.category (_S := S.toSixFunctorOperationDatum) s X))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) K,
      HEq ((A.ambientOperations.directAdjunction f).left.hom.app K)
        (𝟙 (((PodCoefficientStage.operations S.toSixFunctorOperationDatum s).pull f).obj K))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
      (c : Compactification f.hom.left) K,
      HEq ((A.ambientOperations.supportAdjunction f c).left.hom.app K)
        (𝟙 (((PodCoefficientStage.operations S.toSixFunctorOperationDatum s).support f c).obj K))) ∧
    (∀ X, HEq
      (Functor.isoWhiskerRight (R.tensorClosed X).symm (A.functor X) ≪≫
        A.tensor X ≪≫ Functor.isoWhiskerLeft ((A.functor X).prod (A.functor X))
          (R'.tensorClosed X)) (Iso.refl (relativeProductClosedTensor S s X)))) ∨
  (∃ (Rf : RelativeProductPresentation S .finite Q)
      (Rf' : RelativeProductPresentation S' .finite Q)
      (Af : RelativeProductCoefficientData Rf Rf'),
    HEq A Af ∧
    ((∃ (h : n' ≤ n)
      (c : PurCompactSupport.Change (PurCompactSupport.finite C.l E n hn)
        (PurCompactSupport.finite C.l E' n' hn')),
      (∀ X, HEq (c.map X)
        ((PurCompactSupport.finiteQuotientChange C.l E n n' hn hn' h).map X)) ∧
      Af.FiniteScalarNormalization c) ∨
    (∃ (a : E →ₐ[Padic C.l] E') (e : ℕ)
      (he : PurCompactSupport.Ramification C.l E E' a e) (hepos : 1 ≤ e)
      (h : n' ≤ e * n),
      ∃ c : PurCompactSupport.Change (PurCompactSupport.finite C.l E n hn)
          (PurCompactSupport.finite C.l E' n' hn'),
        (∀ X, c.map X =
          (PurCompactSupport.finiteChange C.l E E' a e he hepos n hn).map X ≫
            (PurCompactSupport.finiteQuotientChange C.l E' (e * n) n'
              (Nat.mul_pos hepos hn) hn' h).map X) ∧ Af.FiniteScalarNormalization c))) ∨
  (∃ (Ri : RelativeProductPresentation S .integral Q)
      (Ri' : RelativeProductPresentation S' .integral Q)
      (Ai : RelativeProductCoefficientData Ri Ri') (a : E →ₐ[Padic C.l] E'),
    HEq A Ai ∧ Ai.IntegralScalarNormalization a) ∨
  (s = .integral ∧ s' = .finite ∧ ∃ m : ℕ, m + 1 = n' ∧
    HEq S'.finite (S.integralNormalization.finiteLevels m).finite ∧
    HEq A.ambientOperations (S.integralNormalization.reduction m) ∧
    ∀ X, HEq (relativeProductClosed S' s' X) (S.reductionClosed m X) ∧
      HEq
        (Functor.isoWhiskerRight (R.tensorClosed X).symm (A.functor X) ≪≫
          A.tensor X ≪≫ Functor.isoWhiskerLeft ((A.functor X).prod (A.functor X))
            (R'.tensorClosed X))
        ((S.reductionClosedComparison m X).comparison.tensor)) ∨
  (s = .integral ∧ s' = .rational ∧
    HEq S'.higher.rational S.higher.rational ∧
    HEq A.ambientOperations S.higher.rationalization ∧
    ∀ X, HEq (relativeProductClosed S' s' X) (S.rationalClosed X) ∧
      HEq
        (Functor.isoWhiskerRight (R.tensorClosed X).symm (A.functor X) ≪≫
          A.tensor X ≪≫ Functor.isoWhiskerLeft ((A.functor X).prod (A.functor X))
            (R'.tensorClosed X))
        ((S.rationalClosedComparison X).comparison.tensor)) ∨
  (s = .rational ∧ s' = .rational ∧
    ∃ (E₀ L₀ : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ L₀),
      HEq S.higher.rational (sixFunctorCoefficientRational D C S.closure.coefficientStages E₀) ∧
      HEq S'.higher.rational (sixFunctorCoefficientRational D C S.closure.coefficientStages L₀) ∧
      HEq A.ambientOperations (S.closure.coefficientTransition h) ∧
      ∀ X,
        HEq (relativeProductClosed S s X) (S.coefficientClosedModels E₀ X).rational ∧
        HEq (relativeProductClosed S' s' X) (S.coefficientClosedModels L₀ X).rational ∧
        HEq
        (Functor.isoWhiskerRight (R.tensorClosed X).symm (A.functor X) ≪≫
          A.tensor X ≪≫ Functor.isoWhiskerLeft ((A.functor X).prod (A.functor X))
            (R'.tensorClosed X))
        ((S.coefficientClosedComparison E₀ L₀ h X).comparison.tensor)) ∨
  (s = .rational ∧ s' = .common ∧
    ∃ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      HEq S.higher.rational (sixFunctorCoefficientRational D C S.closure.coefficientStages E₀) ∧
      HEq S'.closure.commonStage S.closure.commonStage ∧
      HEq A.ambientOperations (S.closure.commonStageComparison E₀) ∧
      ∀ X,
        HEq (relativeProductClosed S s X) (S.coefficientClosedModels E₀ X).rational ∧
        HEq (relativeProductClosed S' s' X) (S.commonClosed X) ∧
        HEq
        (Functor.isoWhiskerRight (R.tensorClosed X).symm (A.functor X) ≪≫
          A.tensor X ≪≫ Functor.isoWhiskerLeft ((A.functor X).prod (A.functor X))
            (R'.tensorClosed X))
        ((S.commonClosedComparison E₀ X).comparison.tensor))



end WeilConjectures
