/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedWeilEquivarianceParent
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.AdicSmoothDualizingComplexes
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.SecSmoothPurity.TraceBasic
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization

/-! # The smooth dualizing object in the condensed strict Weil category

Source: latest blueprint, sec-smooth-purity/sk-cor-sp-all-coefficients,
cor-pur-adic-and-rational-smooth-dualizing-complexes, and its proof; the strict-pair
lift is the operation-lift argument in sec-poincare-duality, prop-weil-operations.
(blueprint: lem-pur-weil-smooth-dualizing-complex).

All carrier categories are the recorded condensed Dctf categories. The two exchanges
below are constructed from the canonical support exchange and the independent
pullback/tensor/shift comparison, before using purity. The right adjoint on strict
pairs may be any supplied choice, with its supplied adjunction and counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing AlgebraicGeometry.ProEtale.PurityTransport
open CompactSupportComposition
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.CondensedWeilSmoothDualizing

/-- The finite base as a scheme over itself. Its geometric fibre is canonically Spec k.
Source: the structure morphism in the smooth-dualizing statement
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
abbrev base (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k₀)) := Over.mk (𝟙 _)

/-- The identity structure morphism of the base is of finite type.
Source: s_0 = Spec k_0 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance baseFiniteType (D : FiniteFieldDatum.{u}) : LocallyOfFiniteType (base D).hom := by
  change LocallyOfFiniteType (𝟙 (Spec (.of D.k₀)))
  infer_instance

/-- The base structure morphism is quasi-compact.
Source: s_0 = Spec k_0 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance baseQuasiCompact (D : FiniteFieldDatum.{u}) : QuasiCompact (base D).hom := by
  change QuasiCompact (𝟙 (Spec (.of D.k₀)))
  infer_instance

/-- The base structure morphism is separated.
Source: s_0 = Spec k_0 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance baseSeparated (D : FiniteFieldDatum.{u}) : IsSeparated (base D).hom := by
  change IsSeparated (𝟙 (Spec (.of D.k₀)))
  infer_instance

/-- The canonical identification of this pullback representative of s with Spec k.
Source: X = X_0 times k and s = Spec k
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def baseIso (D : FiniteFieldDatum.{u}) :
    (D.purityFrobeniusFiber (base D)).left ≅ Spec (.of D.k) :=
  asIso (pullback.snd (𝟙 (Spec (.of D.k₀)))
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))

/-- The geometric parameters, bundled only to keep the strict-pair signatures readable.
The compactification is a presentation of the recorded support functor.
Source: separated finite-type X_0 and its smooth structure morphism of pure dimension d
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
structure Model (D : FiniteFieldDatum.{u}) where
  X₀ : Over (Spec (.of D.k₀))
  [finiteType : LocallyOfFiniteType X₀.hom]
  [quasiCompact : QuasiCompact X₀.hom]
  [separated : IsSeparated X₀.hom]
  dim : ℕ
  [smooth : SmoothOfRelativeDimension dim X₀.hom]
  compactification : Compactification
    (D.purityFrobeniusMap (Over.homMk X₀.hom : X₀ ⟶ base D))

attribute [instance] Model.finiteType Model.quasiCompact Model.separated Model.smooth

variable (D : FiniteFieldDatum.{u}) (m : Model D)

/-- The structure morphism as a morphism of finite-base models.
Source: a_0 in the statement (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
abbrev Model.arrow : m.X₀ ⟶ base D := Over.homMk m.X₀.hom

/-- The model's structural arrow is separated.
Source: separated a_0 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance Model.arrowSeparated : IsSeparated (m.arrow D).left := by
  change IsSeparated m.X₀.hom
  infer_instance

/-- The model's structural arrow is locally of finite type.
Source: finite-type a_0 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance Model.arrowFiniteType : LocallyOfFiniteType (m.arrow D).left := by
  change LocallyOfFiniteType m.X₀.hom
  infer_instance

/-- The model's structural arrow is quasi-compact.
Source: finite-type a_0 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance Model.arrowQuasiCompact : QuasiCompact (m.arrow D).left := by
  change QuasiCompact m.X₀.hom
  infer_instance

/-- Smoothness and its prescribed dimension survive geometric base change.
Source: statement's geometric fibre and def-sbc-smooth-morphisms
(blueprint: lem-pur-weil-smooth-dualizing-complex).
Proof: the base-change square for Over.pullback is Cartesian. Apply stability of
SmoothOfRelativeDimension under base change to m.X₀.hom; transport the target
through the canonical pullback of the identity. This also covers an empty X_0. -/
theorem Model.geometricSmooth :
    SmoothOfRelativeDimension m.dim (D.purityFrobeniusMap (m.arrow D)) := by
  sorry

attribute [instance] Model.geometricSmooth

/-- The smooth geometric index for precisely this structure morphism.
Source: coefficient-unit specialization of sk-thm-purity-transport
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def Model.index : SmoothDatum D :=
  PurityWeil.Condensed.smoothIndex D (m.arrow D) m.dim m.compactification

/-- The geometric base is quasi-compact, as the base change of an identity.
Source: s = Spec k (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance baseCompactSpace : CompactSpace (D.purityFrobeniusFiber (base D)).left :=
  QuasiCompact.compactSpace_of_compactSpace (D.purityFrobeniusFiber (base D)).hom

/-- The geometric base is Noetherian as a finite-type scheme over k.
Source: s = Spec k (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
instance baseNoetherian : IsNoetherian (D.purityFrobeniusFiber (base D)).left :=
  isNoetherian_of_locallyOfFiniteType (D.purityFrobeniusFiber (base D)).hom

variable (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (c : Coefficient ell)
  (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))

/-- The recorded normalized smooth adjunction at the structural index.
Source: sk-thm-purity-transport, integration normalization
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
abbrev explicit : ExplicitAdjunction ell D c (m.index D) :=
  PurityWeil.Condensed.normalizedFamily ell D hEll c (m.index D)

/-- The carrier compact-support functor, with only its membership proof restricted.
Source: Ra_! in the statement (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
abbrev lower :=
  support ell c m.compactification (explicit D m ell hEll c).support_closed

/-- The carrier a*(-)(d)[2d], with its literal pullback, tensor and shift.
Source: H in node proof Step 2 (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
abbrev higher :=
  source ell c (D.purityFrobeniusMap (m.arrow D)) m.dim
    (explicit D m ell hEll c).source_closed

/-- Exact termwise inverse image and left-derived inverse image are canonically equal
up to their published comparison. No change of site or coefficient ring is made.
Source: sk-def-sf-weil-complexes, exact geometric-Frobenius action
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def actionComparison (T₀ : Over (Spec (.of D.k₀))) :
    actualPull (c.obj ell) (D.purityGaloisMap T₀) ≅
      StrictWeil.action (c.obj ell) (StrictWeil.modelFrobenius D T₀) :=
  leftDerivedUpperStarIsoMapDerivedCategory (c.obj ell) (D.purityGaloisMap T₀)

/-- The actual canonical support exchange in exact-action coordinates.
Source: thm-pur-weil-equivariance-of-purity-and-trace, B_M
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def supportComponent (M : c.ctf ell (D.purityFrobeniusFiber m.X₀).left) :
    (StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D (base D))).obj
        ((lower D m ell hEll c).obj M) ≅
      (lower D m ell hEll c).obj
        ((StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)).obj M) :=
  ObjectProperty.isoMk _
    ((actionComparison D ell c (base D)).symm.app _ ≪≫
      (PurityWeil.Condensed.supportExchange D
        (PurityWeil.Condensed.coefficientCoherent ell D hEll E c hc)
        (f := SepFinType.homMk
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
            (m.arrow D)))
        (f' := SepFinType.homMk
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map
            (m.arrow D)))
        (PurityWeil.Condensed.galoisSquare D (m.arrow D))
        m.compactification m.compactification).app
          ((inclusion ell c (D.purityFrobeniusFiber m.X₀).left).obj M) ≪≫
      (rightDerivedLowerShriekOfCompactification (c.obj ell) m.compactification).mapIso
        ((actionComparison D ell c m.X₀).app M.obj))

/-- Naturality of the specified support components, in the recorded full subcategory.
Source: the canonical support exchange B in the equivariance theorem
(blueprint: lem-pur-weil-smooth-dualizing-complex).
Proof: supportExchange is a natural isomorphism. Whisker it by the canonical exact-action
comparisons on both sides; their naturality gives the equation. The Dctf inclusion is
fully faithful, so the carrier equality gives exactly this equality. -/
theorem supportComponent_naturality
    {M N : c.ctf ell (D.purityFrobeniusFiber m.X₀).left} (v : M ⟶ N) :
    ((lower D m ell hEll c) ⋙
        StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D (base D))).map v ≫
        (supportComponent D m ell hEll E c hc N).hom =
      (supportComponent D m ell hEll E c hc M).hom ≫
        ((StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)) ⋙
          (lower D m ell hEll c)).map v := by
  sorry

/-- B as a natural isomorphism; every component is the canonical compact-support map.
Source: the fixed-pair operation lift (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def supportExchange :
    (lower D m ell hEll c) ⋙
        StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ≅
      StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀) ⋙
        (lower D m ell hEll c) :=
  NatIso.ofComponents (supportComponent D m ell hEll E c hc)
    (supportComponent_naturality D m ell hEll E c hc)

/-- The specified compact-support functor on strict pairs, not an arbitrary lift.
Source: (K,theta) maps to (FK,F(theta) B_K)
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def supportWeil :
    StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D m.X₀) ⥤
      StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D (base D)) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (supportExchange D m ell hEll E c hc)

/-- The independent pullback, Tate and shift comparison b, in exact-action coordinates.
Source: thm-pur-weil-equivariance-of-purity-and-trace, b_K and tau_d
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def sourceComponent (K : c.ctf ell (D.purityFrobeniusFiber (base D)).left) :
    (StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)).obj
        ((higher D m ell hEll c).obj K) ≅
      (higher D m ell hEll c).obj
        ((StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D (base D))).obj K) :=
  ObjectProperty.isoMk _
    ((actionComparison D ell c m.X₀).symm.app _ ≪≫
      PurityWeil.Condensed.sourceComparison ell D hEll c (m.arrow D) m.dim K.obj ≪≫
      (c.smoothSource ell (D.purityFrobeniusMap (m.arrow D)) m.dim).mapIso
        ((actionComparison D ell c (base D)).app K.obj))

/-- Naturality of b, with no use of gamma to define b.
Source: independent smooth-source comparison in the equivariance theorem
(blueprint: lem-pur-weil-smooth-dualizing-complex).
Proof: pullback composition, the tensorator, the root-normalized Tate datum and the
pullback-shift comparison are natural. Compose their naturality equations, then use
faithfulness of the Dctf inclusion and of the exact-action comparison. -/
theorem sourceComponent_naturality
    {K L : c.ctf ell (D.purityFrobeniusFiber (base D)).left} (v : K ⟶ L) :
    ((higher D m ell hEll c) ⋙
        StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)).map v ≫
        (sourceComponent D m ell hEll c L).hom =
      (sourceComponent D m ell hEll c K).hom ≫
        (StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ⋙
          (higher D m ell hEll c)).map v := by
  sorry

/-- The canonical smooth-source exchange as a natural isomorphism.
Source: b in the strict-pair lift (blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def sourceExchange :
    (higher D m ell hEll c) ⋙
        StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀) ≅
      StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ⋙
        (higher D m ell hEll c) :=
  NatIso.ofComponents (sourceComponent D m ell hEll c)
    (sourceComponent_naturality D m ell hEll c)

/-- The smooth-source lift sends (K,phi) to (a*K(d)[2d], H(phi) b_K).
Source: the purity square and the stipulated shift convention
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def sourceWeil :
    StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ⥤
      StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D m.X₀) :=
  Endofunctor.IsoAlgebra.mapOfNatIso (sourceExchange D m ell hEll c)

/-- The coefficient-unit datum, obtained from the ordinary inverse-image unit map.
It is tau_0 = alpha_g under the recorded degree-zero comparison.
Source: sk-def-sf-weil-complexes, varphi_Lambda = tau_0
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def unitDatum :
    (StrictWeil.action (c.obj ell) (StrictWeil.modelFrobenius D (base D))).obj
        (unit ell c (D.purityFrobeniusFiber (base D)).left) ≅
      unit ell c (D.purityFrobeniusFiber (base D)).left :=
  ((upperStar (c.obj ell) (D.purityGaloisMap (base D))).mapDerivedCategorySingleFunctor 0).app
      (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Functor.Monoidal.εIso (upperStar (c.obj ell) (D.purityGaloisMap (base D)))).symm

/-- The canonical constant strict pair at s, using the existing coefficient unit.
Source: the unit (Lambda_s, varphi_Lambda)
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def unitPair : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D (base D)) :=
  Endofunctor.IsoAlgebra.mk
    ⟨unit ell c (D.purityFrobeniusFiber (base D)).left,
      AdicSmoothDualizing.Condensed.unit_mem ell c (D.purityFrobeniusFiber (base D)).left⟩
    (ObjectProperty.isoMk _ (unitDatum D ell c))

/-- The shifted Tate line belongs to Dctf, by the canonical source-unit identification.
Source: smooth-purity coefficient-unit specialization
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def lineObject : c.ctf ell (D.purityFrobeniusFiber m.X₀).left := by
  have := (constantModelConstructibleFiniteTor_wellDefined (c.obj ell)
    (D.purityFrobeniusFiber m.X₀).left).2.1
  have := (constantModelConstructibleFiniteTor_wellDefined (c.obj ell)
    (D.purityFrobeniusFiber m.X₀).left).2.2.2.1
  exact ⟨c.derivedLine ell (D.purityFrobeniusFiber m.X₀).left m.dim,
    (property ell c _).prop_of_iso
      (sourceUnit ell c (D.purityFrobeniusMap (m.arrow D)) m.dim)
      (((higher D m ell hEll c).obj (unitPair D ell c).carrier).property)⟩

/-- The canonical pullback-unit and tensor-unit coordinates on the carrier.
Source: a* Lambda_s = Lambda_X in the corollary proof
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def lineCoordinates :
    ((sourceWeil D m ell hEll c).obj (unitPair D ell c)).carrier ≅
      lineObject D m ell hEll c :=
  ObjectProperty.isoMk _ (sourceUnit ell c (D.purityFrobeniusMap (m.arrow D)) m.dim)

/-- Lambda_X(d)[2d] with its canonical strict datum. Transporting H(tau_0) b through
sourceUnit is exactly the pulled-back constant datum tensored with tau_d and shifted
through the canonical pullback-shift comparison. Purity is not used in this definition.
Source: target and shifted-pair convention of the node
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def tatePair : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D m.X₀) :=
  Endofunctor.IsoAlgebra.mk (lineObject D m ell hEll c)
    ((StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)).mapIso
        (lineCoordinates D m ell hEll c).symm ≪≫
      ((sourceWeil D m ell hEll c).obj (unitPair D ell c)).str ≪≫
      lineCoordinates D m ell hEll c)

/-- The smooth-source lift is right adjoint to the specified support lift, with exactly
its normalized smooth-trace counit. Counit compatibility determines the adjunction.
Source: node proof Step 2, lem-sf-fixed-pair-adjunction-lift and
thm-pur-weil-equivariance-of-purity-and-trace
(blueprint: lem-pur-weil-smooth-dualizing-complex).
Proof: the canonical support exchange has invertible exceptional mate since both
Frobenius actions are autoequivalences. Lift the carrier exceptional adjunction using
mapOfNatIsoAdjunction. The counit equivariance square identifies the exceptional
exchange with this mate by injectivity of transposition. The purity square makes
Gamma an isomorphism of strict pairs from the independent smooth-source lift to the
exceptional lift. Transport its adjunction through Gamma. The carrier counit is
therefore epsilon composed with F(Gamma), precisely explicit.trace. Faithfulness of
forgetting determines each counit component, and an adjunction is determined by its
counit with both functors fixed. -/
theorem strictAdjunction_existsUnique :
    ∃! adj : supportWeil D m ell hEll E c hc ⊣ sourceWeil D m ell hEll c,
      ∀ K, ((adj.counit.app K).hom.f).hom =
        (explicit D m ell hEll c).trace K.carrier := by
  sorry

/-- The actual strict smooth-purity adjunction, selected by its unique normalized counit.
Only a uniquely determined adjunction is selected; no arbitrary map is chosen.
Source: the fixed-pair adjunction and smooth trace of node proof Steps 2--3
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def strictAdjunction : supportWeil D m ell hEll E c hc ⊣ sourceWeil D m ell hEll c :=
  (strictAdjunction_existsUnique D m ell hEll E c hc).choose

/-- The canonical unit-coordinate isomorphism is a morphism of strict pairs.
Source: the explicitly transported Tate datum
(blueprint: lem-pur-weil-smooth-dualizing-complex).
Proof: expand tatePair. Functoriality and cancellation of the two inverse coordinate
isomorphisms give the fixed-pair morphism equation; the inverse satisfies the inverse
equation. This is the canonical transport of an algebra along an object isomorphism. -/
theorem lineCoordinates_equivariant :
    (StrictWeil.smallAction (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)).map
        (lineCoordinates D m ell hEll c).hom ≫ (tatePair D m ell hEll c).str.hom =
      ((sourceWeil D m ell hEll c).obj (unitPair D ell c)).str.hom ≫
        (lineCoordinates D m ell hEll c).hom := by
  sorry

/-- Source-unit coordinates as a strict-pair isomorphism.
Source: the target identification in node proof Step 1
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def lineIso : (sourceWeil D m ell hEll c).obj (unitPair D ell c) ≅
    tatePair D m ell hEll c :=
  ObjectProperty.isoMk _ (Endofunctor.Algebra.isoMk (lineCoordinates D m ell hEll c)
    (lineCoordinates_equivariant D m ell hEll c))

/-- The normalized integration morphism of strict pairs, in shifted Tate coordinates.
Its carrier is exactly the recorded smooth trace, precomposed with F(sourceUnit^-1).
Source: det-sp-trace-basic, and node proof Step 3
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def integration :
    (supportWeil D m ell hEll E c hc).obj (tatePair D m ell hEll c) ⟶
      unitPair D ell c :=
  (supportWeil D m ell hEll E c hc).map (lineIso D m ell hEll c).inv ≫
    (strictAdjunction D m ell hEll E c hc).counit.app (unitPair D ell c)

/-- Omega is the supplied chosen exceptional right adjoint applied to the canonical unit.
Source: omega_X0 = Ra_0^!(Lambda_s)
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def omega
    (J : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ⥤
      StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D m.X₀)) :=
  J.obj (unitPair D ell c)

/-- The canonical dualizing identification: unique counit-compatible comparison of
right adjoints, evaluated at the unit, followed by canonical source-unit coordinates.
Source: det-sp-unique-right-adjoint and node proof Step 2
(blueprint: lem-pur-weil-smooth-dualizing-complex). -/
def identification
    (J : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ⥤
      StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D m.X₀))
    (adj : supportWeil D m ell hEll E c hc ⊣ J) :
    omega D m ell c J ≅ tatePair D m ell hEll c :=
  (adj.rightAdjointUniq (strictAdjunction D m ell hEll E c hc)).app (unitPair D ell c) ≪≫
    lineIso D m ell hEll c

/-- The condensed smooth-dualizing identification and its trace, at every integral,
rational and algebraic-closure coefficient. The coefficient coordinates retain finite
reduction for all positive levels, inversion of ell and extension from a finite E.
The specified adjunction is the supplied chosen right adjoint and its given counit.
The isomorphism is in the strict fixed-pair category, not merely on its carrier.
Source: latest blueprint cor-pur-adic-and-rational-smooth-dualizing-complexes and proof;
strict equivariance as in prop-weil-operations
(blueprint: lem-pur-weil-smooth-dualizing-complex).
Proof: specialize sk-thm-purity-transport to the structural index and coefficient unit;
sourceUnit identifies its source with Lambda_X(d)[2d]. Use the exceptional mate of the
support exchange and lem-sf-fixed-pair-adjunction-lift. The three squares of
thm-pur-weil-equivariance-of-purity-and-trace make purity, the exceptional counit and
smooth trace strict morphisms. det-sp-unique-right-adjoint supplies the canonical
comparison with the supplied right adjoint, with its actual counit. Cancel this
comparison and the source-unit coordinates to obtain the displayed counit equation.
The carrier of integration is F(sourceUnit^-1) followed by explicit.trace, as in
cor-pur-adic-and-rational-smooth-dualizing-complexes and det-sp-trace-basic.
Finally apply lem-pur-condensed-purity-coefficient-change to the same normalized family
(uniqueness identifies its selected family). Its equations transport these counits
and purity maps through all O_E/pi_E^n reductions, localization and extension of
finite coefficient fields to Qbar. AffineNormalized identifies the finite counits
with normalized integration, as in thm-pur-trace-normalization-transitivity. -/
theorem smooth_dualizing_complex :
    ∃ P : PurityCoefficientChange.Coordinates.{u} ell,
      PurityCoefficientChange.Equations ell D hEll
        (PurityWeil.Condensed.normalizedFamily ell D hEll) P ∧
      PurityCoefficientChange.FrobeniusCompatible ell D P ∧
      AffineNormalized ell D (PurityWeil.Condensed.normalizedFamily ell D hEll) ∧
      ∀ (E : PadicAlgCl.FiniteIntermediateField ell) (c : Coefficient ell)
        (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell)),
        (c = .integral E ∨ c = .rational E ∨ c = .closure) →
        ∀ (m : Model D)
          (J : StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D (base D)) ⥤
            StrictWeil.Complex (c.obj ell) (StrictWeil.modelFrobenius D m.X₀))
          (adj : supportWeil D m ell hEll E c hc ⊣ J),
          Nonempty (omega D m ell c J ≅ tatePair D m ell hEll c) ∧
          (supportWeil D m ell hEll E c hc).map
              (identification D m ell hEll E c hc J adj).hom ≫
            integration D m ell hEll E c hc = adj.counit.app (unitPair D ell c) ∧
          ((integration D m ell hEll E c hc).hom.f).hom =
            AdicSmoothDualizing.Condensed.integration (explicit D m ell hEll c)
              (unitPair D ell c).carrier.property := by
  sorry

end WeilConjectures.CondensedWeilSmoothDualizing
