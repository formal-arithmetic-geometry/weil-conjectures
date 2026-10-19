/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.FiniteForwardProductSymmetry
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.FiniteDirectImageComposition
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.Paper.PfRefinementCompatibility
import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.PurityFiniteSetting
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.SixFunctors.AmbientProperOpenPasting
import Sheaf.SixFunctors.CompositionProjectionMate
import Sheaf.SixFunctors.ProperOpenProjectionMate

/-! # The finite forward product in compactification coordinates

Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, proper-reduction paragraph
(blueprint: lem-pur-finite-product-compactification).

## Main definitions and statements

* `finiteProductCompactification`: the displayed product compactification.
* `finiteProductOpenTensor`: the two-stage normalized open comparison.
* `finiteProductOrdinary`: the ordinary direct-image product map.
* `FinitePurityProductCompactification`: the assertion for arbitrary choices.
* `finiteProduct_compactification`: the finite-level comparison theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}

/-- The three Cartesian products used in the displayed product compactification.
This packages only the geometric products, not any operations on derived categories.
Source: P, X times_B Zbar and C in the node
(blueprint: lem-pur-finite-product-compactification). -/
structure FiniteProductGeometry (f : X ⟶ B) (g : Z ⟶ B) where
  cf : Compactification f
  cg : Compactification g
  P : Scheme.{u}
  W : Scheme.{u}
  T : Scheme.{u}
  p : P ⟶ X
  q : P ⟶ Z
  s : W ⟶ X
  v : W ⟶ cg.Z
  r : T ⟶ cf.Z
  t : T ⟶ cg.Z
  sqP : IsPullback p q f g
  sqW : IsPullback s v f cg.g
  sqT : IsPullback r t cf.g cg.g

/-- The actual Mathlib pullbacks for the chosen displayed compactifications.
Source: the node's three fibre products
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductGeometry (cf : Compactification f) (cg : Compactification g) :
    FiniteProductGeometry f g where
  cf := cf
  cg := cg
  P := pullback f g
  W := pullback f cg.g
  T := pullback cf.g cg.g
  p := pullback.fst f g
  q := pullback.snd f g
  s := pullback.fst f cg.g
  v := pullback.snd f cg.g
  r := pullback.fst cf.g cg.g
  t := pullback.snd cf.g cg.g
  sqP := IsPullback.of_hasPullback f g
  sqW := IsPullback.of_hasPullback f cg.g
  sqT := IsPullback.of_hasPullback cf.g cg.g

variable (G : FiniteProductGeometry f g)

/-- The first open P to X times_B Zbar is the unique Cartesian lift.
Source: the first open extension defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductFirstOpen : G.P ⟶ G.W :=
  G.sqW.lift G.p (G.q ≫ G.cg.i)
    (by rw [Category.assoc, ← G.cg.comm]; exact G.sqP.w)

/-- Its first projection equation, with precisely the displayed endpoints.
Source: the first open extension defining e
(blueprint: lem-pur-finite-product-compactification). -/
abbrev finiteProductFirstOpen_fst : finiteProductFirstOpen G ≫ G.s = G.p :=
  G.sqW.lift_fst _ _ _

/-- The first open is the base change of k.
Source: the Cartesian open squares defining e
(blueprint: lem-pur-finite-product-compactification). -/
abbrev finiteProductFirstSquare :
    IsPullback G.q (finiteProductFirstOpen G) G.cg.i G.v :=
  IsPullback.of_bot
    (by simpa only [finiteProductFirstOpen, IsPullback.lift_fst, ← G.cg.comm] using
      G.sqP.flip)
    (G.sqW.lift_snd _ _ _).symm G.sqW.flip

/-- Base change preserves openness for the first open.
Source: the product compactification construction
(blueprint: lem-pur-finite-product-compactification). -/
instance finiteProductFirstOpen_isOpenImmersion : IsOpenImmersion (finiteProductFirstOpen G) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (finiteProductFirstSquare G) inferInstance

/-- The second open X times_B Zbar to C is the unique Cartesian lift.
Source: the second open extension defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductSecondOpen : G.W ⟶ G.T :=
  G.sqT.lift (G.s ≫ G.cf.i) G.v
    (by rw [Category.assoc, ← G.cf.comm]; exact G.sqW.w)

/-- Its second projection equation, with precisely the displayed endpoints.
Source: the second open extension defining e
(blueprint: lem-pur-finite-product-compactification). -/
abbrev finiteProductSecondOpen_snd : finiteProductSecondOpen G ≫ G.t = G.v :=
  G.sqT.lift_snd _ _ _

/-- The second open is the base change of j.
Source: the Cartesian open squares defining e
(blueprint: lem-pur-finite-product-compactification). -/
abbrev finiteProductSecondSquare :
    IsPullback G.s (finiteProductSecondOpen G) G.cf.i G.r :=
  IsPullback.of_bot
    (by rw [finiteProductSecondOpen_snd, ← G.cf.comm]; exact G.sqW)
    (G.sqT.lift_fst _ _ _).symm G.sqT

/-- Base change preserves openness for the second open.
Source: the product compactification construction
(blueprint: lem-pur-finite-product-compactification). -/
instance finiteProductSecondOpen_isOpenImmersion : IsOpenImmersion (finiteProductSecondOpen G) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (finiteProductSecondSquare G) inferInstance

/-- The projection t is proper by base change of a.
Source: properness in the product compactification
(blueprint: lem-pur-finite-product-compactification). -/
instance finiteProductGeometry_t_isProper : IsProper G.t :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback G.sqT inferInstance

/-- The displayed product compactification h=cu, using the actual unique open lifts.
Source: the product compactification of the node
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductCompactification : Compactification (G.q ≫ g) where
  Z := G.T
  g := G.t ≫ G.cg.g
  i := finiteProductFirstOpen G ≫ finiteProductSecondOpen G
  comm := by
    rw [Category.assoc, ← Category.assoc _ G.t G.cg.g, finiteProductSecondOpen_snd,
      finiteProductFirstOpen, ← Category.assoc, IsPullback.lift_snd,
      Category.assoc, ← G.cg.comm]
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Compactifiability of q follows from the given Cartesian square and that of f.
Source: the base-changed compactification in PF_q
(blueprint: lem-pur-finite-product-compactification). -/
instance finiteProductGeometry_q_hasCompactification [HasCompactification f] :
    HasCompactification G.q := HasCompactification.of_isPullback G.sqP

/-- Quasi-compactness of q follows by base change from f.
Source: the finite-type hypotheses of the node
(blueprint: lem-pur-finite-product-compactification). -/
instance finiteProductGeometry_q_quasiCompact [QuasiCompact f] : QuasiCompact G.q :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback G.sqP inferInstance

/-- The constructed product compactification supplies compactifiability of h.
Source: the actual compactification (u,c)
(blueprint: lem-pur-finite-product-compactification). -/
instance finiteProductGeometry_h_hasCompactification : HasCompactification (G.q ≫ g) :=
  ⟨⟨finiteProductCompactification G⟩⟩

section Components
variable (V : Type u') [Category.{u + 1} V] [Abelian V]
  [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V]
  [MonoidalPreadditive V] [SymmetricCategory V] [MonoidalClosed V]
  [Abelian.HasFunctorialFlatResolution V] [UpperStarPreservesFlat V]

/-- The component of the ordinary counit projection, with explicit endpoints.
Source: the two pi factors of Omega
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOrdinaryProjection {U W : Scheme.{u}} (a : U ⟶ W)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) V))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) V)) :
    ((derivedTensor V W).obj (R(lowerStar V a).obj K)).obj L ⟶
      R(lowerStar V a).obj
        (((derivedTensor V U).obj K).obj (L(upperStar V a).obj L)) :=
  ((rightDerivedLowerStarProjectionMap V a).app K).app L

/-- The component of the inverse open projection isomorphism, with explicit endpoints.
Source: the two open tensor factors defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenProjection {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) V))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) V)) :
    ((derivedTensor V W).obj
      ((openImmersionLowerShriek V j).mapDerivedCategory.obj K)).obj L ⟶
    (openImmersionLowerShriek V j).mapDerivedCategory.obj
      (((derivedTensor V U).obj K).obj (L(upperStar V j).obj L)) :=
  ((derivedOpenImmersionLowerShriekProjectionIso V j).inv.app K).app L

/-- Tensoring a specified arrow on the left, evaluated at the right object.
Source: the tensor functor used in e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductTensorMapLeft (T : Scheme.{u})
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)}
    (v : K ⟶ K') (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)) :
    ((derivedTensor V T).obj K).obj L ⟶ ((derivedTensor V T).obj K').obj L :=
  ((derivedTensor V T).map v).app L

/-- Tensoring a specified arrow on the right, evaluated at the left object.
Source: the tensor functor used in e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductTensorMapRight (T : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V))
    {L L' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) V)} (v : L ⟶ L') :
    ((derivedTensor V T).obj K).obj L ⟶ ((derivedTensor V T).obj K).obj L' :=
  ((derivedTensor V T).obj K).map v

/-- The action of the actual derived extension by zero on an arrow.
Source: the extension functor used in e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenMap {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    {K L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) V)} (v : K ⟶ L) :
    (openImmersionLowerShriek V j).mapDerivedCategory.obj K ⟶
      (openImmersionLowerShriek V j).mapDerivedCategory.obj L :=
  (openImmersionLowerShriek V j).mapDerivedCategory.map v

end Components

section TensorConstruction
variable (Coeff : Type u') [Category.{u + 1} Coeff] [Abelian Coeff]
  [IsGrothendieckAbelian.{u + 1} Coeff] [MonoidalCategory Coeff]
  [MonoidalPreadditive Coeff] [SymmetricCategory Coeff] [MonoidalClosed Coeff]
  [Abelian.HasFunctorialFlatResolution Coeff] [UpperStarPreservesFlat Coeff]

/-- The pullback square compositor, including transport along a commuting triangle.
This is an abbreviation of the canonical pullback compositor, not additional data.
Source: the canonical identifications suppressed in the displayed e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductPullTriangle {U V₀ W : Scheme.{u}} (a : U ⟶ V₀) (b : V₀ ⟶ W)
    (c : U ⟶ W) (h : a ≫ b = c) :
    L(upperStar Coeff b) ⋙ L(upperStar Coeff a) ≅
      L(upperStar Coeff c) :=
  (leftDerivedUpperStarComp Coeff a b).symm ≪≫
    leftDerivedUpperStarCongr Coeff h

/-- The object component of the canonical commuting-triangle pullback comparison.
Source: the suppressed pullback identifications in e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductPullTriangleObj {U V₀ W : Scheme.{u}} (a : U ⟶ V₀) (b : V₀ ⟶ W)
    (c : U ⟶ W) (h : a ≫ b = c)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W) Coeff)) :
    L(upperStar Coeff a).obj (L(upperStar Coeff b).obj M) ≅
      L(upperStar Coeff c).obj M :=
  (finiteProductPullTriangle Coeff a b c h).app M

/-- Open composition with its adjunction normalization, from iterated to single extension.
Source: the two successive open extensions defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenComposition {U V₀ W : Scheme.{u}} (a : U ⟶ V₀) (b : V₀ ⟶ W)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    (openImmersionLowerShriek Coeff a).mapDerivedCategory ⋙
      (openImmersionLowerShriek Coeff b).mapDerivedCategory ≅
    (openImmersionLowerShriek Coeff (a ≫ b)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction Coeff a)
        (openImmersionLowerShriekUpperStarAdjunction Coeff b)
        (openImmersionLowerShriekUpperStarAdjunction Coeff (a ≫ b))
        (upperStarComp Coeff a b).symm)

/-- Canonical open base change, in total-left-derived pullback coordinates.
Source: the open base-change factors of the displayed e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenBaseChange {U' U V₀' V₀ : Scheme.{u}}
    {a : U' ⟶ U} {j' : U' ⟶ V₀'} {j : U ⟶ V₀} {b : V₀' ⟶ V₀}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b) :
    (openImmersionLowerShriek Coeff j).mapDerivedCategory ⋙
        L(upperStar Coeff b) ≅
      L(upperStar Coeff a) ⋙
        (openImmersionLowerShriek Coeff j').mapDerivedCategory :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory Coeff b) ≪≫
    (derivedOpenImmersionLowerShriekBaseChangeIso Coeff sq).symm ≪≫
      Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory Coeff a).symm _

/-- Open base change followed by the open tensor map in its right variable.
Source: the inner open factor of the specified e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenTensorRight {U' U W' W : Scheme.{u}}
    {a : U' ⟶ U} {j' : U' ⟶ W'} {j : U ⟶ W} {b : W' ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b)
    (S : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W') Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) Coeff)) :
    ((derivedTensor Coeff W').obj S).obj (L(upperStar Coeff b).obj
      ((openImmersionLowerShriek Coeff j).mapDerivedCategory.obj N)) ⟶
    (openImmersionLowerShriek Coeff j').mapDerivedCategory.obj
      (((derivedTensor Coeff U').obj (L(upperStar Coeff j').obj S)).obj
        (L(upperStar Coeff a).obj N)) :=
  ((derivedTensor Coeff W').obj S).map ((finiteProductOpenBaseChange Coeff sq).hom.app N) ≫
    finiteForwardTensorSymmetry Coeff W' S
      ((openImmersionLowerShriek Coeff j').mapDerivedCategory.obj
        (L(upperStar Coeff a).obj N)) ≫
    finiteProductOpenProjection Coeff j' (L(upperStar Coeff a).obj N) S ≫
    (openImmersionLowerShriek Coeff j').mapDerivedCategory.map
      (finiteForwardTensorSymmetry Coeff U' (L(upperStar Coeff a).obj N)
        (L(upperStar Coeff j').obj S))

/-- Open base change followed by the open tensor map in its left variable.
Source: the outer open factor of the specified e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenTensorLeft {U' U W' W : Scheme.{u}}
    {a : U' ⟶ U} {j' : U' ⟶ W'} {j : U ⟶ W} {b : W' ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) Coeff))
    (G : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology W') Coeff)) :
    ((derivedTensor Coeff W').obj (L(upperStar Coeff b).obj
      ((openImmersionLowerShriek Coeff j).mapDerivedCategory.obj M))).obj G ⟶
    (openImmersionLowerShriek Coeff j').mapDerivedCategory.obj
      (((derivedTensor Coeff U').obj (L(upperStar Coeff a).obj M)).obj
        (L(upperStar Coeff j').obj G)) :=
  ((derivedTensor Coeff W').map ((finiteProductOpenBaseChange Coeff sq).hom.app M)).app G ≫
    finiteProductOpenProjection Coeff j' (L(upperStar Coeff a).obj M) G

/-- The right open tensor step including its commuting-triangle pullback comparison.
Source: the first complete open step defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenTensorRightPull {U' U W' W R : Scheme.{u}}
    {a : U' ⟶ U} {j' : U' ⟶ W'} {j : U ⟶ W} {b : W' ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b)
    (s : W' ⟶ R) (p : U' ⟶ R) (h : j' ≫ s = p)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology R) Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) Coeff)) :
    ((derivedTensor Coeff W').obj (L(upperStar Coeff s).obj M)).obj
      (L(upperStar Coeff b).obj
        ((openImmersionLowerShriek Coeff j).mapDerivedCategory.obj N)) ⟶
    (openImmersionLowerShriek Coeff j').mapDerivedCategory.obj
      (((derivedTensor Coeff U').obj (L(upperStar Coeff p).obj M)).obj
        (L(upperStar Coeff a).obj N)) :=
  finiteProductOpenTensorRight Coeff sq (L(upperStar Coeff s).obj M) N ≫
    finiteProductOpenMap Coeff j'
      (finiteProductTensorMapLeft Coeff U'
        (finiteProductPullTriangleObj Coeff j' s p h M).hom
        (L(upperStar Coeff a).obj N))

/-- The left open tensor step including its commuting-triangle pullback comparison.
Source: the second complete open step defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenTensorLeftPull {U' U W' W R : Scheme.{u}}
    {a : U' ⟶ U} {j' : U' ⟶ W'} {j : U ⟶ W} {b : W' ⟶ W}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback a j' j b)
    (t : W' ⟶ R) (v : U' ⟶ R) (h : j' ≫ t = v)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) Coeff))
    (J : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology R) Coeff)) :
    ((derivedTensor Coeff W').obj (L(upperStar Coeff b).obj
      ((openImmersionLowerShriek Coeff j).mapDerivedCategory.obj M))).obj
        (L(upperStar Coeff t).obj J) ⟶
    (openImmersionLowerShriek Coeff j').mapDerivedCategory.obj
      (((derivedTensor Coeff U').obj (L(upperStar Coeff a).obj M)).obj
        (L(upperStar Coeff v).obj J)) :=
  finiteProductOpenTensorLeft Coeff sq M (L(upperStar Coeff t).obj J) ≫
    finiteProductOpenMap Coeff j'
      (finiteProductTensorMapRight Coeff U' (L(upperStar Coeff a).obj M)
        (finiteProductPullTriangleObj Coeff j' t v h J).hom)

/-- D=Lp*M tensor Lq*N, using the ordinary unbounded derived tensor.
Source: the displayed definition of D
(blueprint: lem-pur-finite-product-compactification). -/
abbrev finiteProductExternal
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) Coeff)) :=
  ((derivedTensor Coeff (G.P)).obj
    (L(upperStar Coeff (G.p)).obj M)).obj
    (L(upperStar Coeff (G.q)).obj N)

/-- Lr*H tensor Lt*J on the product of the compactifying schemes.
Source: the source of the specified open comparison e
(blueprint: lem-pur-finite-product-compactification). -/
abbrev finiteProductExtendedTensor
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) Coeff)) :=
  ((derivedTensor Coeff (G.T)).obj
    (L(upperStar Coeff (G.r)).obj
      ((openImmersionLowerShriek Coeff G.cf.i).mapDerivedCategory.obj M))).obj
    (L(upperStar Coeff (G.t)).obj
      ((openImmersionLowerShriek Coeff G.cg.i).mapDerivedCategory.obj N))

/-- The inner open tensor comparison, from X ×_B Zbar back to P.
Source: the first of the two successive extensions defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductInnerOpenTensor
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) Coeff)) :=
  finiteProductOpenTensorRightPull Coeff (finiteProductFirstSquare G)
    G.s G.p (finiteProductFirstOpen_fst G) M N


/-- The outer open tensor comparison on Xbar ×_B Zbar.
Source: the second of the two successive extensions defining e
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOuterOpenTensor
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) Coeff)) :=
  finiteProductOpenTensorLeftPull Coeff (finiteProductSecondSquare G)
    G.t G.v (finiteProductSecondOpen_snd G) M
    ((openImmersionLowerShriek Coeff G.cg.i).mapDerivedCategory.obj N)


/-- The specified e, first extending from P to X ×_B Zbar and then to Xbar ×_B Zbar.
Only open base change, open tensor isomorphisms and canonical compositors occur.
Both signed symmetries come from the actual Koszul braiding on the derived category.
The normalization to 1_D is the open unit normalization.
Source: the displayed e and its normalization; lem-sf-open-tensor-normalization
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOpenTensor
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) Coeff))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) Coeff)) :=
  finiteProductOuterOpenTensor G Coeff M N ≫
    finiteProductOpenMap Coeff (finiteProductSecondOpen G)
      (finiteProductInnerOpenTensor G Coeff M N) ≫
    (finiteProductOpenComposition Coeff (finiteProductFirstOpen G)
      (finiteProductSecondOpen G)).hom.app (finiteProductExternal G Coeff M N)

end TensorConstruction

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The specified open comparison e is an isomorphism on arbitrary unbounded objects.
Source: the displayed isomorphism e in the node; open tensor normalization
(blueprint: lem-pur-finite-product-compactification).
Proof: each beta is canonical open base change and each gamma is the inverse open
projection isomorphism. Pullback and open composition are canonical isomorphisms.
The two signed swaps are the derived Koszul symmetries and are isomorphisms.
Consequently their displayed composite is an isomorphism. Restricting to P and
using the section-unit normalization of beta, gamma and the open compositor
identifies it with 1_D; the two swaps cancel under these identifications. -/
theorem finiteProductOpenTensor_isIso
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    IsIso (finiteProductOpenTensor G (ModuleCat.{u + 1} A) M N) := by
  sorry

/-- Omega is entirely ordinary: symmetry, pi_b, symmetry, Ex_* tensor 1, pi_t,
and the inverse ordinary direct-image compositor. No inverse projection or exchange occurs.
Source: the displayed Omega_{a,b}
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOrdinary {U V T : Scheme.{u}} (a : U ⟶ B) (b : V ⟶ B)
    {r : T ⟶ U} {t : T ⟶ V} (sq : IsPullback r t a b)
    (H : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)))
    (J : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology V) (ModuleCat.{u + 1} A))) :
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj
      (R(lowerStar (ModuleCat.{u + 1} A) a).obj H)).obj
      (R(lowerStar (ModuleCat.{u + 1} A) b).obj J) ⟶
    R(lowerStar (ModuleCat.{u + 1} A) (t ≫ b)).obj
      (((derivedTensor (ModuleCat.{u + 1} A) (T)).obj
        (L(upperStar (ModuleCat.{u + 1} A) (r)).obj H)).obj
        (L(upperStar (ModuleCat.{u + 1} A) (t)).obj J)) :=
  let L := R(lowerStar (ModuleCat.{u + 1} A) a).obj H
  let bL := L(upperStar (ModuleCat.{u + 1} A) b).obj L
  let rH := L(upperStar (ModuleCat.{u + 1} A) (r)).obj H
  finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) B L
      (R(lowerStar (ModuleCat.{u + 1} A) b).obj J) ≫
    finiteProductOrdinaryProjection (ModuleCat.{u + 1} A) b J L ≫
    R(lowerStar (ModuleCat.{u + 1} A) b).map
      (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) V J bL ≫
        ((derivedTensor (ModuleCat.{u + 1} A) V).map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A)
            sq.toCommSq).app H)).app J) ≫
    R(lowerStar (ModuleCat.{u + 1} A) b).map
      (finiteProductOrdinaryProjection (ModuleCat.{u + 1} A) (t) rH J) ≫
    (finiteDirectImageComposition A (t) b).inv.app _

/-- The normalized alpha on arbitrary displayed compactifications, expressed by
conjugating the recorded origin compositor with the canonical compactification comparisons.
Its q compactification need not be the globally chosen one.
Source: the normalized alpha and independence-of-choices clauses
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductComposition {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W)
    [QuasiCompact a] [QuasiCompact b]
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    (ca : Compactification a) (cb : Compactification b) (cab : Compactification (a ≫ b))
    (D : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A)))
    (hD : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) U D) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca).obj D) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cab).obj D :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb).map
      ((finiteForwardCompactificationComparison A ca
        (HasCompactification.compactification a)).hom.app ⟨D, hD⟩) ≫
    (finiteForwardCompactificationComparison A cb
      (HasCompactification.compactification b)).hom.app
        ⟨(rightDerivedLowerShriek (ModuleCat.{u + 1} A) a).obj D,
          hD.rightDerivedLowerShriek_obj a⟩ ≫
    (originCompositionAmbient A a b).hom.app ⟨D, hD⟩ ≫
    (finiteForwardCompactificationComparison A
      (HasCompactification.compactification (a ≫ b)) cab).hom.app ⟨D, hD⟩

/-- All tensor objects in the forward composite, in the original chosen coordinates.
Source: the explicit bounded-below etale-origin tensor-domain requirement
(blueprint: lem-pur-finite-product-compactification). -/
def FiniteProductCompactificationDomain (cf : Compactification f) (cg : Compactification g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))) :
    Prop :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) B
    (((derivedTensor (ModuleCat.{u + 1} A) B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N))) ∧
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) B
    (((derivedTensor (ModuleCat.{u + 1} A) B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))) ∧
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z
    (((derivedTensor (ModuleCat.{u + 1} A) Z).obj N).obj
      (L(upperStar (ModuleCat.{u + 1} A) g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)))) ∧
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z
    (((derivedTensor (ModuleCat.{u + 1} A) Z).obj
      (L(upperStar (ModuleCat.{u + 1} A) g).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M))).obj N)) ∧
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z
    (((derivedTensor (ModuleCat.{u + 1} A) Z).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (cf.ofIsPullback G.sqP)).obj
          (L(upperStar (ModuleCat.{u + 1} A) (G.p)).obj M))).obj N)) ∧
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) (G.P)
    (finiteProductExternal G (ModuleCat.{u + 1} A) M N))

/-- T for arbitrary original compactifications, with the normalized compositor alpha.
The five prefix factors are literally the specified PF and Ex_! components.
Source: the displayed T_{f,g}, in exactly its displayed order
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductChosenForward [HasCompactification f] [HasCompactification g]
    [HasCompactification (G.q ≫ g)] [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (ch : Compactification (G.q ≫ g))
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hD : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) (G.P)
      (finiteProductExternal G (ModuleCat.{u + 1} A) M N)) :
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).obj M)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).obj N) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch).obj
      (finiteProductExternal G (ModuleCat.{u + 1} A) M N) :=
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf
  let Gfun := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg
  finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) B (F.obj M) (Gfun.obj N) ≫
    finiteForwardProjectionMap (ModuleCat.{u + 1} A) cg N (F.obj M) ≫
    Gfun.map (finiteForwardTensorSymmetry (ModuleCat.{u + 1} A) Z N
        (L(upperStar (ModuleCat.{u + 1} A) g).obj (F.obj M)) ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Z).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
          G.sqP cf).app M)).app N) ≫
    Gfun.map (finiteForwardProjectionMap (ModuleCat.{u + 1} A) (cf.ofIsPullback G.sqP)
      (L(upperStar (ModuleCat.{u + 1} A) (G.p)).obj M) N) ≫
    finiteProductComposition A (G.q) g (cf.ofIsPullback G.sqP) cg ch
      (finiteProductExternal G (ModuleCat.{u + 1} A) M N) hD

/-- The product candidate is, definitionally, Rc_* after extension by its actual open u.
This named identity prevents repeated unfolding of the compactification's construction.
Source: the normalized identification Rh_!D=Rc_*u_!D in the node
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductTargetModel
    (D : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (G.P)) (ModuleCat.{u + 1} A))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (finiteProductCompactification G)).obj D ≅
    R(lowerStar (ModuleCat.{u + 1} A) (G.t ≫ G.cg.g)).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A)
        (finiteProductCompactification G).i).mapDerivedCategory.obj D) :=
  Iso.refl _

/-- The left side after the normalized target identification.
Source: the target-identification clause of the final equality
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductForwardInCoordinates
    [HasCompactification f] [HasCompactification g]
    [HasCompactification (G.q ≫ g)] [QuasiCompact f] [QuasiCompact g]
    (cf₀ : Compactification f) (cg₀ : Compactification g)
    (ch₀ : Compactification (G.q ≫ g))
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (d : FiniteProductCompactificationDomain G A cf₀ cg₀ M N) :
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf₀).obj M)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg₀).obj N) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (finiteProductCompactification G)).obj
      (finiteProductExternal G (ModuleCat.{u + 1} A) M N) :=
  finiteProductChosenForward G A cf₀ cg₀ ch₀ M N d.2.2.2.2.2 ≫
      (finiteForwardCompactificationComparison A ch₀
        (finiteProductCompactification G)).hom.app ⟨_, d.2.2.2.2.2⟩

/-- The ordinary route after both normalized source identifications.
Source: the source-identification clause of the final equality
(blueprint: lem-pur-finite-product-compactification). -/
def finiteProductOrdinaryInCoordinates
    [HasCompactification f] [HasCompactification g]
    [HasCompactification (G.q ≫ g)] [QuasiCompact f] [QuasiCompact g]
    (cf₀ : Compactification f) (cg₀ : Compactification g)
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hN : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z N) :
    ((derivedTensor (ModuleCat.{u + 1} A) B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf₀).obj M)).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg₀).obj N) ⟶
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (finiteProductCompactification G)).obj
      (finiteProductExternal G (ModuleCat.{u + 1} A) M N) :=
  (((derivedTensor (ModuleCat.{u + 1} A) B).map
      ((finiteForwardCompactificationComparison A cf₀ G.cf).hom.app ⟨M, hM⟩)).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg₀).obj N)) ≫
    (((derivedTensor (ModuleCat.{u + 1} A) B).obj
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) G.cf).obj M)).map
      ((finiteForwardCompactificationComparison A cg₀ G.cg).hom.app ⟨N, hN⟩)) ≫
    finiteProductOrdinary A G.cf.g G.cg.g G.sqT
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) G.cf.i).mapDerivedCategory.obj M)
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) G.cg.i).mapDerivedCategory.obj N) ≫
    R(lowerStar (ModuleCat.{u + 1} A) (G.t ≫ G.cg.g)).map
      (finiteProductOpenTensor G (ModuleCat.{u + 1} A) M N) ≫
    (finiteProductTargetModel G A (finiteProductExternal G (ModuleCat.{u + 1} A) M N)).inv

/-- Equality in the displayed product-compactification coordinates. All three
endpoint comparisons are the normalized ones, for arbitrary original and displayed choices.
Source: the final equality and independence-of-choices clauses
(blueprint: lem-pur-finite-product-compactification). -/
def FiniteProductCompactificationEquation
    [HasCompactification f] [HasCompactification g]
    [HasCompactification (G.q ≫ g)] [QuasiCompact f] [QuasiCompact g]
    (cf₀ : Compactification f) (cg₀ : Compactification g)
    (ch₀ : Compactification (G.q ≫ g))
    (M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (N : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hN : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z N)
    (d : FiniteProductCompactificationDomain G A cf₀ cg₀ M N) : Prop :=
  finiteProductForwardInCoordinates G A cf₀ cg₀ ch₀ M N d =
    finiteProductOrdinaryInCoordinates G A cf₀ cg₀ M N hM hN

/-- The finite-coefficient assertion over the fixed field k, with precisely its
separated finite-type hypotheses and retained bounded-below origin witnesses.
The local instances below are consequences of finite type over k, used only to
instantiate Nagata. Original and displayed compactifications are independently quantified.
Source: the hypotheses and final universal-choices clause of the node
(blueprint: lem-pur-finite-product-compactification). -/
def FinitePurityProductCompactification
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (CommRingCat.of C.field.k))]
    [X.Over (Spec (CommRingCat.of C.field.k))]
    [Z.Over (Spec (CommRingCat.of C.field.k))]
    [IsSeparated (B ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (B ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (CommRingCat.of C.field.k))]
    [g.IsOver (Spec (CommRingCat.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N) : Prop :=
  letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated
    (X ↘ Spec (CommRingCat.of C.field.k))
  letI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (CommRingCat.of C.field.k))
  letI : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated
    (Z ↘ Spec (CommRingCat.of C.field.k))
  ∀ (cf : Compactification f) (cg : Compactification g),
    let G := finiteProductGeometry cf cg
    ∀ (cf₀ : Compactification f) (cg₀ : Compactification g)
      (ch₀ : Compactification (G.q ≫ g))
      (d : FiniteProductCompactificationDomain G C.Coefficient cf₀ cg₀ M.obj N.obj),
      FiniteProductCompactificationEquation G C.Coefficient cf₀ cg₀ ch₀ M.obj N.obj
        ⟨wM.complex.obj, wM.complex.property, ⟨wM.iso⟩⟩
        ⟨wN.complex.obj, wN.complex.property, ⟨wN.iso⟩⟩ d

/-- The finite forward product equals the ordinary product followed by Rc_*(e).
Source: blueprint sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, symmetry/proper-reduction paragraph; the agent-formulated
finite-level calculation of this node (blueprint: lem-pur-finite-product-compactification).

Proof:
1. Work at A=A_{E,n} in the ordinary unbounded categories. The displayed bounded-below
etale-origin conditions are used only for compactification comparisons and alpha.
First take the displayed compactifications as the original choices in T.
2. Set W=Xbar times_B Z, v:W→Z, i:W→C, j_q:P→W. Then q=v j_q, t i=k v,
and i j_q=u. Properness and finite type are stable under base change and composition;
finite type over a field makes these schemes Noetherian and the displayed opens
quasi-compact. Thus (j_q,v) and (u,c) compactify q and h. By
lem-sf-composition-projection-mate the compositor is kappa^{-1} Rb(Gamma), including
open composition, where Gamma:k_!Rv→Rt i_! is the normalized proper/open mate.
3. Put L=Ra H, L0=Lb*L, F=Lr*H, E=Li*F, K=j_q!Lp*M, KD=j_q!D, and let
beta:E≅K be open base change. Write A0=Ex_{*,a,b,H}:L0→Rt F, and
rho:Lk*Rt F≅Rv Li*F for open restriction. On a K-injective representative rho is the
ordinary exchange: its transpose is Li* of the proper counit. Horizontal mate pasting
gives B0=Ex_{!,f,g,M}=Rv(beta) rho Lk*(A0). No exchange for q occurs here.
4. Put m=i_!K, chi=epsilon_i i_!(beta^{-1}):m→F, and
s=Gamma_K k_!(B0):k_!Lk*L0→Rt m. The open-counit equation is
Rt(chi) s=A0 epsilon_k. Indeed Gamma_E is the k_! adjunct of the inverse of the
normalized open restriction lambda:Lk*Rt i_!E≅Rv E. Naturality of rho, followed by
the open triangle identity, shows Rt(epsilon_i) Gamma_E k_!(rho_F)=epsilon_k.
Substitute B0 and apply naturality with beta and A0 to obtain the equation.
5. Let delta denote the normalized open tensor map. Under Lk*J≅N put
nu=k_!(sigma) delta_{k;N,L0} sigma and eta=epsilon_{k,L0} tensor 1_J.
Open tensor identifies both source and target of eta with objects in the image of k_!.
Their restrictions make eta the identity and cancel the two symmetries in nu.
Full faithfulness gives that eta is invertible and nu eta=delta_{k;Lk*L0,J}.
6. Let d:K tensor Lv*N≅KD be the open factor of PF_q. Set
w=i_!(d) delta_{i;K,Lt*J}:m tensor Lt*J→u_!D. The normalization of beta, d,
open tensor and the open counit shows that w=e (chi tensor 1). Both maps restrict
to 1_D on P and their source lies in the image of u_!, so full faithfulness proves
this equality. This keeps the essential counit chi; w and e have different sources.
7. Put Psi=Gamma_KD k_!Rv(d) k_!(pi_{v;K,N}) k_!(B0 tensor 1_N), and
z=Rb(sigma) pi_{b;J,L} sigma. Expanding the definitions of PF and Ex gives
T=kappa^{-1} Rb(Psi nu) z and
Omega=kappa^{-1} Rb(pi_{t;F,J}(A0 tensor 1_J)) z. These are the actual maps,
including the ordinary exchange A0 and pi_b.
8. Apply lem-sf-proper-open-projection-mate to (i,v,k,t), K and J. Postcompose
with Rt i_!(d), use naturality of Gamma, and precompose with k_!(B0) tensor 1_J.
Naturality of delta and step 5 give
Psi nu eta=Rt(w) pi_{t;m,J}(s tensor 1_J). This mate identity holds on arbitrary
unbounded objects, so no Tor-amplitude or constructibility hypothesis is introduced.
9. Substitute w=e(chi tensor 1). Naturality of pi in chi, followed by step 4, gives
Psi nu eta=Rt(e) pi_{t;F,J}(A0 tensor 1_J) eta. Cancel only the open-tensor
isomorphism eta. Apply Rb, precompose with z and postcompose with kappa^{-1}.
Naturality of the ordinary direct-image compositor at e gives T=Rc(e) Omega.
10. For arbitrary original choices, use the normalized common-refinement comparisons
and cocycle of prop-compactification-coherence-detailed. The refinement square for
PF (lem-pur-pf-refinement-compatibility), exchange refinement (fix-lem-exchanges,
item 4), independence of alpha (thm-sf-comp-composition), and naturality of symmetry
paste to the displayed equality after the three endpoint identifications. All tensor
inputs have the required bounded-below etale-origin conditions. The calculation
applies to every displayed pair. No projection, exchange or chi is inverted, and
no exceptional adjoint or abstract six-functor data are used. -/
theorem finiteProduct_compactification
    (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X Z : Scheme.{u}}
    [B.Over (Spec (CommRingCat.of C.field.k))]
    [X.Over (Spec (CommRingCat.of C.field.k))]
    [Z.Over (Spec (CommRingCat.of C.field.k))]
    [IsSeparated (B ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of C.field.k))]
    [IsSeparated (Z ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of C.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (B ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of C.field.k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of C.field.k))]
    (f : X ⟶ B) (g : Z ⟶ B)
    [f.IsOver (Spec (CommRingCat.of C.field.k))]
    [g.IsOver (Spec (CommRingCat.of C.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} C.Coefficient)))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} C.Coefficient)))
    (wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M)
    (wN : Scheme.FixedEtaleOriginWitness Z C.Coefficient N) :
    FinitePurityProductCompactification C f g M N wM wN := by
  sorry

end AlgebraicGeometry.ProEtale
