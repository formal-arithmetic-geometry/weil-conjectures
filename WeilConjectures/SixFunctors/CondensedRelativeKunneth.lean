/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.CondensedCtfSixFunctorStability
public import WeilConjectures.SecSmoothPurity.DetPropSfCbc
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.SixFunctors.CondensedOperationComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.CondensedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.CondensedProperProductTranspose
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Relative Künneth for ordinary condensed coefficients

Source: latest blueprint, sec-six-functors/sk-thm-sf-kunneth-relative/_section.md,
the six-arrow comparison and its coherence and closed-product paragraphs
(blueprint: sk-thm-sf-kunneth-relative).

The forward product arrow is the reverse of the displayed word: symmetry, projection,
symmetry, exchange, projection, composition. Its inverse characterizes the relative
Künneth comparison uniquely, with no choice of an unspecified endpoint isomorphism.

## Main definitions

* `RelativeKunneth.forward`: the specified reverse six-factor word.
* `RelativeKunneth.IsoFamily`: its uniquely normalized inverse isomorphisms.
* `RelativeKunneth.ProductTheorem`: those isomorphisms and all coherence clauses.

## Main statements

* `RelativeKunneth.condensedRelativeKunneth`: the complete relative product theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.RelativeKunneth

variable {k : Type u} [Field k]

/-- A realization of the relative product square; all schemes are separated and finite
 type over the field. Source: the unit's opening paragraph
(blueprint: sk-thm-sf-kunneth-relative). -/
structure Diagram (k : Type u) [Field k] where
  B : SepFinType k
  X : SepFinType k
  Y : SepFinType k
  T : SepFinType k
  f : X ⟶ B
  g : Y ⟶ B
  p : T ⟶ X
  q : T ⟶ Y
  cartesian : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left

/-- Compactification models for the four compact-support operations in the displayed
word. Source: the unit's six-arrow formula (blueprint: sk-thm-sf-kunneth-relative). -/
structure Models (d : Diagram k) where
  f : Compactification d.f.hom.left
  g : Compactification d.g.hom.left
  q : Compactification d.q.hom.left
  total : Compactification (d.q.hom.left ≫ d.g.hom.left)

variable (Λ : ScalarSixRing.{u})

/-- External product on the actual ordinary module-derived categories.
Source: K boxtimes L in the opening paragraph (blueprint: sk-thm-sf-kunneth-relative). -/
def exterior (d : Diagram k) (K : CompactificationReindexing.D Λ.X d.X.obj.left)
    (L : CompactificationReindexing.D Λ.X d.Y.obj.left) :
    CompactificationReindexing.D Λ.X d.T.obj.left :=
  (CompactificationReindexing.P Λ.X d.p.hom.left).obj K ⊗
    (CompactificationReindexing.P Λ.X d.q.hom.left).obj L

/-- The canonical inclusion in the localizing closure, used only to evaluate the
normalized composition and exchange supplied by their owning dependency.
Source: composition theorem, restriction to Dctf (blueprint: sk-thm-sf-kunneth-relative). -/
def localizingObject (X : Scheme.{u}) (K : ConstantModelConstructibleFiniteTor Λ.X X) :
    (localizingClosureProEtale Λ.X X).FullSubcategory :=
  ⟨K.obj, fun _P _hP hS ↦ hS K.obj K.property⟩

/-- The signed symmetry of the existing native derived tensor structure, with its
braided structure given explicitly because it is not a global instance upstream.
Source: the two sigma factors (blueprint: sk-thm-sf-kunneth-relative). -/
def symmetry (X : Scheme.{u}) (K L : CompactificationReindexing.D Λ.X X) : K ⊗ L ≅ L ⊗ K :=
  @BraidedCategory.braiding _ _ _ (DerivedCategory.braidedCategory' _) K L

/-- The reverse six-factor word. All its arrows are the existing canonical forward
maps, so its definition requires no invertibility assumption. The compositor and
exchange have the normalization laws of the recorded composition dependency.
Source: six-arrow formula read backwards (blueprint: sk-thm-sf-kunneth-relative). -/
def forward (H : CompactSupportComposition.CoherentData Λ.X k)
    (d : Diagram k) (c : Models d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left)
    (hE : localizingClosureProEtale Λ.X d.T.obj.left (exterior Λ d K.obj L.obj)) :
    (CompactificationReindexing.F Λ.X c.f).obj K.obj ⊗
        (CompactificationReindexing.F Λ.X c.g).obj L.obj ⟶
      (CompactificationReindexing.F Λ.X c.total).obj (exterior Λ d K.obj L.obj) :=
  (symmetry Λ _ _ _).hom ≫
    CompactificationReindexing.pf Λ.X c.g L.obj
      ((CompactificationReindexing.F Λ.X c.f).obj K.obj) ≫
    (CompactificationReindexing.F Λ.X c.g).map
      ((symmetry Λ _ _ _).hom ≫
        ((H.exchange (X := d.X) (Y := d.B) (X' := d.T) (Y' := d.Y)
          (f := d.f) (f' := d.q) d.cartesian c.f c.q).hom.app
            (localizingObject Λ d.X.obj.left K) ⊗ₘ 𝟙 L.obj) ≫
        CompactificationReindexing.pf Λ.X c.q
          ((CompactificationReindexing.P Λ.X d.p.hom.left).obj K.obj) L.obj) ≫
    (H.comp d.q d.g c.q c.g c.total).hom.app ⟨_, hE⟩



/-- The canonical tensor comparison of the native derived pullback.
Source: monoidality in coherence (iii) (blueprint: sk-thm-sf-kunneth-relative). -/
def pullTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : CompactificationReindexing.D Λ.X Y) :
    (CompactificationReindexing.P Λ.X f).obj (K ⊗ L) ≅
      (CompactificationReindexing.P Λ.X f).obj K ⊗
        (CompactificationReindexing.P Λ.X f).obj L :=
  (Functor.Monoidal.μIso (CompactificationReindexing.P Λ.X f) K L).symm

/-- Identify successive pullbacks with the pullback along the specified composite.
Source: pullback compositors in (ii)--(iii) (blueprint: sk-thm-sf-kunneth-relative). -/
def pullPath {T U X : Scheme.{u}} (a : T ⟶ U) (p : U ⟶ X) (r : T ⟶ X)
    (e : a ≫ p = r) (K : CompactificationReindexing.D Λ.X X) :
    (CompactificationReindexing.P Λ.X a).obj
        ((CompactificationReindexing.P Λ.X p).obj K) ≅
      (CompactificationReindexing.P Λ.X r).obj K :=
  ((leftDerivedUpperStarComp Λ.X a p).app K).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CompactificationReindexing.P Λ.X f).obj K) e)

/-- Interchange the two factors without changing the chosen realization of the product.
Its identification with the literal swapped fibre product is its universal property.
Source: coherence (i) (blueprint: sk-thm-sf-kunneth-relative). -/
def Diagram.swap (d : Diagram k) : Diagram k where
  B := d.B
  X := d.Y
  Y := d.X
  T := d.T
  f := d.g
  g := d.f
  p := d.q
  q := d.p
  cartesian := d.cartesian.flip

/-- Models for the swapped product, using the same total compactification with the
commutativity identification. Source: (i) (blueprint: sk-thm-sf-kunneth-relative). -/
def Models.swap {d : Diagram k} (c : Models d) : Models d.swap where
  f := c.g
  g := c.f
  q := compactificationOverField d.p.hom
  total := c.total.copy d.cartesian.w

/-- Base change between realizations of two product squares. The base map and its three
pullbacks are arbitrary scheme morphisms; they need not preserve the ground field.
Source: coherence (iii) (blueprint: sk-thm-sf-kunneth-relative). -/
structure BaseChange (d d' : Diagram k) where
  b : d'.B.obj.left ⟶ d.B.obj.left
  x : d'.X.obj.left ⟶ d.X.obj.left
  y : d'.Y.obj.left ⟶ d.Y.obj.left
  t : d'.T.obj.left ⟶ d.T.obj.left
  sf : IsPullback x d'.f.hom.left d.f.hom.left b
  sg : IsPullback y d'.g.hom.left d.g.hom.left b
  sp : CommSq t d'.p.hom.left d.p.hom.left x
  sq : CommSq t d'.q.hom.left d.q.hom.left y
  st : IsPullback t (d'.q.hom.left ≫ d'.g.hom.left)
    (d.q.hom.left ≫ d.g.hom.left) b

/-- The exterior-product identification in the base-change square, including its two
canonical pullback-composition comparisons. Source: (iii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def exteriorBaseChange {d d' : Diagram k} (s : BaseChange d d')
    (K : CompactificationReindexing.D Λ.X d.X.obj.left)
    (L : CompactificationReindexing.D Λ.X d.Y.obj.left) :
    (CompactificationReindexing.P Λ.X s.t).obj (exterior Λ d K L) ≅
      exterior Λ d' ((CompactificationReindexing.P Λ.X s.x).obj K)
        ((CompactificationReindexing.P Λ.X s.y).obj L) :=
  pullTensor Λ s.t _ _ ≪≫
    tensorIso ((pullbackSquareComparison Λ.X s.sp).app K).symm
      ((pullbackSquareComparison Λ.X s.sq).app L).symm

/-- Three product squares realizing the two bracketings of a triple fibre product.
The same final scheme realizes both bracketings, through the universal product
identification. Source: coherence (ii) (blueprint: sk-thm-sf-kunneth-relative). -/
structure Triple (k : Type u) [Field k] where
  B : SepFinType k
  X : SepFinType k
  Y : SepFinType k
  W : SepFinType k
  U : SepFinType k
  V : SepFinType k
  T : SepFinType k
  f : X ⟶ B
  g : Y ⟶ B
  h : W ⟶ B
  up : U ⟶ X
  uq : U ⟶ Y
  vp : V ⟶ Y
  vq : V ⟶ W
  a : T ⟶ U
  b : T ⟶ W
  c : T ⟶ X
  d : T ⟶ V
  xy : IsPullback up.hom.left uq.hom.left f.hom.left g.hom.left
  yw : IsPullback vp.hom.left vq.hom.left g.hom.left h.hom.left
  leftSquare : IsPullback a.hom.left b.hom.left
    (uq.hom.left ≫ g.hom.left) h.hom.left
  rightSquare : IsPullback c.hom.left d.hom.left f.hom.left
    (vq.hom.left ≫ h.hom.left)
  first : a.hom.left ≫ up.hom.left = c.hom.left
  middle : a.hom.left ≫ uq.hom.left = d.hom.left ≫ vp.hom.left
  last : b.hom.left = d.hom.left ≫ vq.hom.left

/-- The first pair in a triple product. Source: (ii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def Triple.xyDiagram (s : Triple k) : Diagram k :=
  ⟨s.B, s.X, s.Y, s.U, s.f, s.g, s.up, s.uq, s.xy⟩

/-- The last pair in a triple product. Source: (ii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def Triple.ywDiagram (s : Triple k) : Diagram k :=
  ⟨s.B, s.Y, s.W, s.V, s.g, s.h, s.vp, s.vq, s.yw⟩

/-- The left bracketing of a triple product. Source: (ii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def Triple.leftDiagram (s : Triple k) : Diagram k :=
  ⟨s.B, s.U, s.W, s.T, s.uq ≫ s.g, s.h, s.a, s.b, s.leftSquare⟩

/-- The right bracketing of a triple product. Source: (ii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def Triple.rightDiagram (s : Triple k) : Diagram k :=
  ⟨s.B, s.X, s.V, s.T, s.f, s.vq ≫ s.h, s.c, s.d, s.rightSquare⟩

/-- The actual pullback/tensor associator identifying the two triple exterior products.
Source: associativity identification in (ii) (blueprint: sk-thm-sf-kunneth-relative). -/
def tripleExterior (s : Triple k)
    (K : CompactificationReindexing.D Λ.X s.X.obj.left)
    (L : CompactificationReindexing.D Λ.X s.Y.obj.left)
    (M : CompactificationReindexing.D Λ.X s.W.obj.left) :
    exterior Λ s.leftDiagram (exterior Λ s.xyDiagram K L) M ≅
      exterior Λ s.rightDiagram K (exterior Λ s.ywDiagram L M) :=
  tensorIso (pullTensor Λ s.a.hom.left _ _ ≪≫
    tensorIso (pullPath Λ s.a.hom.left s.up.hom.left s.c.hom.left s.first K)
      (pullPath Λ s.a.hom.left s.uq.hom.left
        (s.d.hom.left ≫ s.vp.hom.left) s.middle L)) (Iso.refl _) ≪≫
    (α_ _ _ _) ≪≫ tensorIso (Iso.refl _)
      (tensorIso (Iso.refl _)
        (eqToIso (congrArg (fun f ↦ (CompactificationReindexing.P Λ.X f).obj M)
          s.last)) ≪≫
        (tensorIso ((leftDerivedUpperStarComp Λ.X s.d.hom.left s.vp.hom.left).app L)
          ((leftDerivedUpperStarComp Λ.X s.d.hom.left s.vq.hom.left).app M)) ≪≫
        (pullTensor Λ s.d.hom.left _ _).symm)



/-- Compatible compactification models for the four squares of a triple product.
Source: (ii), collected composition factors (blueprint: sk-thm-sf-kunneth-relative). -/
structure TripleModels (s : Triple k) where
  f : Compactification s.f.hom.left
  g : Compactification s.g.hom.left
  h : Compactification s.h.hom.left
  uq : Compactification s.uq.hom.left
  vq : Compactification s.vq.hom.left
  xy : Compactification (s.uq.hom.left ≫ s.g.hom.left)
  yw : Compactification (s.vq.hom.left ≫ s.h.hom.left)
  b : Compactification s.b.hom.left
  d : Compactification s.d.hom.left
  total : Compactification (s.b.hom.left ≫ s.h.hom.left)

/-- Models for the first pair. Source: (ii) (blueprint: sk-thm-sf-kunneth-relative). -/
def TripleModels.xyModels {s : Triple k} (c : TripleModels s) : Models s.xyDiagram :=
  ⟨c.f, c.g, c.uq, c.xy⟩

/-- Models for the last pair. Source: (ii) (blueprint: sk-thm-sf-kunneth-relative). -/
def TripleModels.ywModels {s : Triple k} (c : TripleModels s) : Models s.ywDiagram :=
  ⟨c.g, c.h, c.vq, c.yw⟩

/-- Models for the left bracketing. Source: (ii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def TripleModels.leftModels {s : Triple k} (c : TripleModels s) : Models s.leftDiagram :=
  ⟨c.xy, c.h, c.b, c.total⟩

/-- Models for the right bracketing. Source: (ii)
(blueprint: sk-thm-sf-kunneth-relative). -/
def TripleModels.rightModels {s : Triple k} (c : TripleModels s) : Models s.rightDiagram :=
  ⟨c.f, c.yw, c.d, c.total.copy
    ((congrArg (fun r ↦ r ≫ s.h.hom.left) s.last).trans
      (Category.assoc s.d.hom.left s.vq.hom.left s.h.hom.left)).symm⟩

/-- The identity second factor, realized on X itself. Source: (iv)
(blueprint: sk-thm-sf-kunneth-relative). -/
def identityDiagram {X B : SepFinType k} (f : X ⟶ B)
    (s : IsPullback (𝟙 X.obj.left) f.hom.left f.hom.left (𝟙 B.obj.left)) : Diagram k :=
  ⟨B, X, B, X, f, 𝟙 B, 𝟙 X, f, s⟩

/-- Identity compactification on the identity factor. Source: (iv)
(blueprint: sk-thm-sf-kunneth-relative). -/
def identityModels {X B : SepFinType k} (f : X ⟶ B)
    (s : IsPullback (𝟙 X.obj.left) f.hom.left f.hom.left (𝟙 B.obj.left))
    (c : Compactification f.hom.left) : Models (identityDiagram f s) :=
  ⟨c, Compactification.ofIsProper (𝟙 B.obj.left), c,
    c.copy (Category.comp_id f.hom.left)⟩

/-- The two inverse pullback images as actual Dctf objects. The membership is the
recorded composition dependency's arbitrary-pullback preservation clause.
Source: (iii), typing of the new inputs (blueprint: sk-thm-sf-kunneth-relative). -/
def pullObject (H : CompactSupportComposition.CoherentData Λ.X k)
    (X Y : SepFinType k) (f : X.obj.left ⟶ Y.obj.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ⟨(CompactificationReindexing.P Λ.X f).obj K.obj,
    (H.pullback_preserves X Y f).2 K.obj K.property⟩

/-- Canonical product isomorphisms for one coefficient ring. Inverse normalization fixes
all the isomorphisms by their six forward factors, and the factor clause says that each
inverse in the displayed definition exists. No arbitrary comparison is supplied.
Source: the main formula, naturality, and (i)--(iv)
(blueprint: sk-thm-sf-kunneth-relative). -/
structure IsoFamily (H : CompactSupportComposition.CoherentData Λ.X k) where
  exterior_ctf : ∀ (d : Diagram k)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    (constantModelBoundedConstructible Λ.X d.T.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (exterior Λ d K.obj L.obj)
  iso : ∀ (d : Diagram k) (c : Models d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    (CompactificationReindexing.F Λ.X c.total).obj (exterior Λ d K.obj L.obj) ≅
      (CompactificationReindexing.F Λ.X c.f).obj K.obj ⊗
        (CompactificationReindexing.F Λ.X c.g).obj L.obj
  inverse : ∀ (d : Diagram k) (c : Models d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    (iso d c K L).inv = forward Λ H d c K L
      (localizingObject Λ d.T.obj.left
        ⟨_, exterior_ctf d K L⟩).property
  factors : ∀ (d : Diagram k) (c : Models d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    IsIso (CompactificationReindexing.pf Λ.X c.q
      ((CompactificationReindexing.P Λ.X d.p.hom.left).obj K.obj) L.obj) ∧
    IsIso (CompactificationReindexing.pf Λ.X c.g L.obj
      ((CompactificationReindexing.F Λ.X c.f).obj K.obj))

/-- Regard an exterior product as Dctf using the domain assertion in the product theorem.
Source: (ii), intermediate inputs (blueprint: sk-thm-sf-kunneth-relative). -/
def IsoFamily.exteriorObject {H : CompactSupportComposition.CoherentData Λ.X k}
    (A : IsoFamily Λ H) (d : Diagram k)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left) :
    ConstantModelConstructibleFiniteTor Λ.X d.T.obj.left :=
  ⟨exterior Λ d K.obj L.obj, A.exterior_ctf d K L⟩

/-- Naturality in both coefficient complexes, as an equality of actual ambient arrows.
Source: naturality after the displayed isomorphism
(blueprint: sk-thm-sf-kunneth-relative). -/
def Naturality {H : CompactSupportComposition.CoherentData Λ.X k}
    (A : IsoFamily Λ H) : Prop :=
  ∀ (d : Diagram k) (c : Models d)
    (K K' : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L L' : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left)
    (a : K ⟶ K') (b : L ⟶ L'),
    (CompactificationReindexing.F Λ.X c.total).map
      ((CompactificationReindexing.P Λ.X d.p.hom.left).map a.hom ⊗ₘ
        (CompactificationReindexing.P Λ.X d.q.hom.left).map b.hom) ≫
      (A.iso d c K' L').hom =
    (A.iso d c K L).hom ≫
      ((CompactificationReindexing.F Λ.X c.f).map a.hom ⊗ₘ
        (CompactificationReindexing.F Λ.X c.g).map b.hom)

/-- Signed symmetry on the same product realization. The scheme swap is its unique
identification with the literal reversed fibre product.
Source: (i) (blueprint: sk-thm-sf-kunneth-relative). -/
def Symmetry {H : CompactSupportComposition.CoherentData Λ.X k} (A : IsoFamily Λ H) : Prop :=
  ∀ (d : Diagram k) (c : Models d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    (CompactificationReindexing.F Λ.X c.total).map ((symmetry Λ _ _ _).hom) ≫
        (A.iso d.swap c.swap L K).hom =
      (A.iso d c K L).hom ≫ (symmetry Λ _ _ _).hom

/-- The two bracketings of the actual triple-product comparison, with precisely the
native pullback/tensor associator and the signed tensor associator at the endpoints.
Source: (ii) (blueprint: sk-thm-sf-kunneth-relative). -/
def Associativity {H : CompactSupportComposition.CoherentData Λ.X k}
    (A : IsoFamily Λ H) : Prop :=
  ∀ (s : Triple k) (c : TripleModels s)
    (K : ConstantModelConstructibleFiniteTor Λ.X s.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X s.Y.obj.left)
    (M : ConstantModelConstructibleFiniteTor Λ.X s.W.obj.left),
    (CompactificationReindexing.F Λ.X c.total).map
        (tripleExterior Λ s K.obj L.obj M.obj).hom ≫
      (A.iso s.rightDiagram c.rightModels K (IsoFamily.exteriorObject Λ A s.ywDiagram L M)).hom ≫
      (𝟙 _ ⊗ₘ (A.iso s.ywDiagram c.ywModels L M).hom) =
    (A.iso s.leftDiagram c.leftModels (IsoFamily.exteriorObject Λ A s.xyDiagram K L) M).hom ≫
      ((A.iso s.xyDiagram c.xyModels K L).hom ⊗ₘ 𝟙 _) ≫ (α_ _ _ _).hom

/-- The base-change square for kappa, using all three normalized exchanges and the
native monoidality comparison. No base map is required to be over the field.
Source: (iii) (blueprint: sk-thm-sf-kunneth-relative). -/
def BaseChangeLaw {H : CompactSupportComposition.CoherentData Λ.X k}
    (A : IsoFamily Λ H) : Prop :=
  ∀ (d d' : Diagram k) (c : Models d) (c' : Models d') (s : BaseChange d d')
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    (CompactificationReindexing.P Λ.X s.b).map (A.iso d c K L).hom ≫
      (pullTensor Λ s.b _ _).hom ≫
      ((H.exchange (f := d.f) (f' := d'.f) s.sf c.f c'.f).hom.app
          (localizingObject Λ d.X.obj.left K) ⊗ₘ
        (H.exchange (f := d.g) (f' := d'.g) s.sg c.g c'.g).hom.app
          (localizingObject Λ d.Y.obj.left L)) =
    (H.exchange (f := d.q ≫ d.g) (f' := d'.q ≫ d'.g) s.st c.total c'.total).hom.app
        (localizingObject Λ d.T.obj.left (IsoFamily.exteriorObject Λ A d K L)) ≫
      (CompactificationReindexing.F Λ.X c'.total).map
        (exteriorBaseChange Λ s K.obj L.obj).hom ≫
      (A.iso d' c' (pullObject Λ H d'.X d.X s.x K)
        (pullObject Λ H d'.Y d.Y s.y L)).hom

/-- In the identity-factor case the inverse comparison is exactly PF, transported only
by the two canonical identity unitors. Equivalently, kappa is PF inverse.
Source: (iv) (blueprint: sk-thm-sf-kunneth-relative). -/
def ProjectionLaw {H : CompactSupportComposition.CoherentData Λ.X k}
    (A : IsoFamily Λ H) : Prop :=
  ∀ (X B : SepFinType k) (f : X ⟶ B)
    (s : IsPullback (𝟙 X.obj.left) f.hom.left f.hom.left (𝟙 B.obj.left))
    (c : Compactification f.hom.left)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X B.obj.left),
    (A.iso (identityDiagram f s) (identityModels f s c) K L).inv =
      (𝟙 _ ⊗ₘ (CompactSupportComposition.identity Λ.X B.obj.left).hom.app L.obj) ≫
        CompactificationReindexing.pf Λ.X c K.obj L.obj ≫
        (CompactificationReindexing.F Λ.X c).map
          ((leftDerivedUpperStarId Λ.X X.obj.left).inv.app K.obj ⊗ₘ 𝟙 _)



/-- The closed-subscheme product, including the unique induced map to the original
product. The projection equations specify that map by the product universal property.
Source: the supported-product paragraph (blueprint: sk-thm-sf-kunneth-relative). -/
structure ClosedProduct (d : Diagram k) where
  Z : SepFinType k
  W : SepFinType k
  U : SepFinType k
  i : Z ⟶ d.X
  j : W ⟶ d.Y
  rp : U ⟶ Z
  rq : U ⟶ W
  r : U ⟶ d.T
  closed_i : IsClosedImmersion i.hom.left
  closed_j : IsClosedImmersion j.hom.left
  cartesian : IsPullback rp.hom.left rq.hom.left
    (i.hom.left ≫ d.f.hom.left) (j.hom.left ≫ d.g.hom.left)
  fst : r.hom.left ≫ d.p.hom.left = rp.hom.left ≫ i.hom.left
  snd : r.hom.left ≫ d.q.hom.left = rq.hom.left ≫ j.hom.left

/-- Extension of restriction along a closed immersion, using the exact closed image's
ordinary total derived realization. This is i_*i^*, not i_*Ri^!.
Source: supported-product formula (blueprint: sk-thm-sf-kunneth-relative). -/
def closedRestriction {Z X : Scheme.{u}} (i : Z ⟶ X)
    (K : CompactificationReindexing.D Λ.X X) : CompactificationReindexing.D Λ.X X :=
  (CompactificationReindexing.R Λ.X i).obj ((CompactificationReindexing.P Λ.X i).obj K)

/-- The relative supported product isomorphism, retaining the original K and L as the
only coefficient-domain inputs. In particular no finite-Tor preservation is assumed as
an additional hypothesis for the closed extensions.
Source: final supported-product display (blueprint: sk-thm-sf-kunneth-relative). -/
def SupportedProduct : Prop :=
  ∀ (d : Diagram k) (c : Models d) (s : ClosedProduct d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    Nonempty ((CompactificationReindexing.F Λ.X c.f).obj
        (closedRestriction Λ s.i.hom.left K.obj) ⊗
      (CompactificationReindexing.F Λ.X c.g).obj
        (closedRestriction Λ s.j.hom.left L.obj) ≅
      (CompactificationReindexing.F Λ.X c.total).obj
        (closedRestriction Λ s.r.hom.left (exterior Λ d K.obj L.obj)))

/-- The compact-support product on the closed schemes themselves, before applying point
sections. This is its natural Galois-module-valued formulation when k is not closed.
Source: the B = Spec k specialization (blueprint: sk-thm-sf-kunneth-relative). -/
def CompactClosedProduct : Prop :=
  ∀ (X Y Z W U : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (p : U ⟶ Z) (q : U ⟶ W)
    (_s : IsPullback p q (i ≫ f) (j ≫ g))
    (cZ : Compactification (i ≫ f)) (cW : Compactification (j ≫ g))
    (cU : Compactification (q ≫ j ≫ g))
    (K : ConstantModelConstructibleFiniteTor Λ.X X)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y),
    Nonempty ((CompactificationReindexing.F Λ.X cZ).obj
        ((CompactificationReindexing.P Λ.X i).obj K.obj) ⊗
      (CompactificationReindexing.F Λ.X cW).obj
        ((CompactificationReindexing.P Λ.X j).obj L.obj) ≅
      (CompactificationReindexing.F Λ.X cU).obj
        ((CompactificationReindexing.P Λ.X (p ≫ i)).obj K.obj ⊗
          (CompactificationReindexing.P Λ.X (q ≫ j)).obj L.obj))

/-- The compact-support product after point sections, in the recorded ordinary derived
category of modules over the scalar sections of the condensed coefficient ring.
The theorem uses an algebraically closed ground field.
Source: the B = Spec k specialization (blueprint: sk-thm-sf-kunneth-relative). -/
def CompactCoefficientClosedProduct : Prop :=
  ∀ (X Y Z W U : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (p : U ⟶ Z) (q : U ⟶ W)
    (_s : IsPullback p q (i ≫ f) (j ≫ g))
    (cZ : Compactification (i ≫ f)) (cW : Compactification (j ≫ g))
    (cU : Compactification (q ≫ j ≫ g))
    (K : ConstantModelConstructibleFiniteTor Λ.X X)
    (L : ConstantModelConstructibleFiniteTor Λ.X Y),
    Nonempty ((condensedRingCompactCoefficientComplex Λ.X cZ).obj
        ((CompactificationReindexing.P Λ.X i).obj K.obj) ⊗
      (condensedRingCompactCoefficientComplex Λ.X cW).obj
        ((CompactificationReindexing.P Λ.X j).obj L.obj) ≅
      (condensedRingCompactCoefficientComplex Λ.X cU).obj
        ((CompactificationReindexing.P Λ.X (p ≫ i)).obj K.obj ⊗
          (CompactificationReindexing.P Λ.X (q ≫ j)).obj L.obj))

/-- Independence under the canonical compactification comparisons. On proper models
these identify compact support with the ordinary proper direct image, using identity
open immersions, so this includes the proper-coincidence compatibility in the unit.
Source: proper compatibility after the main display
(blueprint: sk-thm-sf-kunneth-relative). -/
def ModelIndependence {H : CompactSupportComposition.CoherentData Λ.X k}
    (A : IsoFamily Λ H) : Prop :=
  ∀ (d : Diagram k) (c c' : Models d)
    (K : ConstantModelConstructibleFiniteTor Λ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Λ.X d.Y.obj.left),
    (H.comparison (d.q ≫ d.g) c.total c'.total).hom.app
        (localizingObject Λ d.T.obj.left (IsoFamily.exteriorObject Λ A d K L)) ≫
      (A.iso d c' K L).hom =
    (A.iso d c K L).hom ≫
      ((H.comparison d.f c.f c'.f).hom.app (localizingObject Λ d.X.obj.left K) ⊗ₘ
        (H.comparison d.g c.g c'.g).hom.app (localizingObject Λ d.Y.obj.left L))

/-- The canonical scalar comparison for the exterior product, as the scalar tensorator
followed by the two normalized pullback comparisons. Source: coefficient compatibility
(blueprint: sk-thm-sf-kunneth-relative). -/
def scalarExterior {Γ Γ' : ScalarSixRing.{u}} (a : Γ ⟶ Γ') (d : Diagram k)
    (K : CompactificationReindexing.D Γ.X d.X.obj.left)
    (L : CompactificationReindexing.D Γ.X d.Y.obj.left) :
    (scalarSixChange a d.T.obj.left).obj (exterior Γ d K L) ≅
      exterior Γ' d ((scalarSixChange a d.X.obj.left).obj K)
        ((scalarSixChange a d.Y.obj.left).obj L) :=
  scalarSixTensorIso a d.T.obj.left _ _ ≪≫
    tensorIso ((OperationComparisons.scalarPull a d.p.hom.left).app K)
      ((OperationComparisons.scalarPull a d.q.hom.left).app L)

/-- Reduction and scalar extension commute with the relative product map, through the
specified proper/open scalar mates. The listed maps include positive finite reductions
and finite coefficient-field scalar extensions. The domain proofs here only certify
that the actual scalar images are Dctf; they do not select replacement objects or maps.
Source: coefficient compatibility (blueprint: sk-thm-sf-kunneth-relative). -/
def CoefficientLaw (ell : ℕ) [Fact ell.Prime]
    {Γ Γ' : ScalarSixRing.{u}}
    {H : CompactSupportComposition.CoherentData Γ.X k}
    {H' : CompactSupportComposition.CoherentData Γ'.X k}
    (A : IsoFamily Γ H) (A' : IsoFamily Γ' H') : Prop :=
  ∀ (a : Γ ⟶ Γ') (_ha : IsListedScalarCoefficientMap ell a)
    (d : Diagram k) (c : Models d)
    (K : ConstantModelConstructibleFiniteTor Γ.X d.X.obj.left)
    (L : ConstantModelConstructibleFiniteTor Γ.X d.Y.obj.left)
    (hK : (constantModelBoundedConstructible Γ'.X d.X.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) ((scalarSixChange a d.X.obj.left).obj K.obj))
    (hL : (constantModelBoundedConstructible Γ'.X d.Y.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) ((scalarSixChange a d.Y.obj.left).obj L.obj)),
    (scalarSixChange a d.B.obj.left).map (A.iso d c K L).hom ≫
        (scalarSixTensorIso a d.B.obj.left _ _).hom ≫
        ((scalarCompactSupportMap a c.f.i c.f.g).app K.obj ⊗ₘ
          (scalarCompactSupportMap a c.g.i c.g.g).app L.obj) =
      (scalarCompactSupportMap a c.total.i c.total.g).app
          (exterior Γ d K.obj L.obj) ≫
        (CompactificationReindexing.F Γ'.X c.total).map (scalarExterior a d K.obj L.obj).hom ≫
        (A'.iso d c ⟨_, hK⟩ ⟨_, hL⟩).hom

/-- The complete assertion for all native admissible coefficients simultaneously.
Every comparison is fixed by the normalized six-arrow formula, while the subsequent
fields are equations about those same comparisons. Closed supports use restriction.
Source: the complete unit statement (blueprint: sk-thm-sf-kunneth-relative). -/
structure ProductTheorem (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] where
  coherent : ∀ Γ : ScalarSixRing.{u}, IsLocalizingAdmissibleCoefficient ell Γ.X →
    CompactSupportComposition.CoherentData Γ.X k
  product : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    IsoFamily Γ (coherent Γ hΓ)
  naturality : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    Naturality Γ (product Γ hΓ)
  symmetry : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    Symmetry Γ (product Γ hΓ)
  associativity : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    Associativity Γ (product Γ hΓ)
  baseChange : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    BaseChangeLaw Γ (product Γ hΓ)
  projection : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    ProjectionLaw Γ (product Γ hΓ)
  models : ∀ (Γ : ScalarSixRing.{u}) (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X),
    ModelIndependence Γ (product Γ hΓ)
  supported : ∀ (Γ : ScalarSixRing.{u}), IsLocalizingAdmissibleCoefficient ell Γ.X →
    SupportedProduct Γ (k := k)
  compact : ∀ (Γ : ScalarSixRing.{u}), IsLocalizingAdmissibleCoefficient ell Γ.X →
    CompactClosedProduct Γ (k := k)
  compactCoefficients : ∀ (Γ : ScalarSixRing.{u}), IsLocalizingAdmissibleCoefficient ell Γ.X →
    CompactCoefficientClosedProduct Γ (k := k)
  scalar_ctf : ∀ (Γ Γ' : ScalarSixRing.{u})
    (_hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X)
    (_hΓ' : IsLocalizingAdmissibleCoefficient ell Γ'.X)
    (a : Γ ⟶ Γ') (_ha : IsListedScalarCoefficientMap ell a)
    (X : SepFinType k) (K : ConstantModelConstructibleFiniteTor Γ.X X.obj.left),
    (constantModelBoundedConstructible Γ'.X X.obj.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) ((scalarSixChange a X.obj.left).obj K.obj)
  coefficients : ∀ (Γ Γ' : ScalarSixRing.{u})
    (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X)
    (hΓ' : IsLocalizingAdmissibleCoefficient ell Γ'.X),
    CoefficientLaw ell (product Γ hΓ) (product Γ' hΓ')

/-- Relative Künneth for the ordinary, uncompleted condensed coefficient operations:
the specified six-arrow word is an isomorphism, natural and coherent, with its closed
subscheme products. Source: latest blueprint, unit sk-thm-sf-kunneth-relative
(blueprint: sk-thm-sf-kunneth-relative).

Proof, following the six DAG steps (dependency ids are recorded in the node):
1. Stability preserves finite-Tor constructibility under pullback, tensor and compact
support. The product projections and composites are separated of finite type; these
schemes are Noetherian, and finite constructible coefficients have etale origins.
2. Reverse the displayed six forward factors. Composition, projection formula and
Cartesian compact-support exchange make each factor invertible. Their scalar
comparisons preserve the word; proper models give proper coincidence.
3. For symmetry pass to product compactifications. The open comparison commutes with
swap. On proper models the forward word is adjoint to the tensor of the two pulled
back counits. Signed symmetry swaps the two counits, so their transposes agree.
4. Expand the two triple words. Projection associativity, composition associativity,
projection/exchange squares and exchange pasting identify them. Applying these same
squares over an arbitrary base map proves the base-change equation. Identity unitors
and the identity exchange leave precisely inverse projection in the identity case.
5. For closed i,j, three proper base changes and two projection formulas identify
exterior products of closed extensions with the closed extension of the restricted
exterior product. All these maps are the exact closed direct images.
6. Apply the relative formula to the closed extensions, or to fi and gj after
restriction. Composition and proper coincidence give the compact-support formula
at the point. The coefficients are restrictions; no exceptional-support formula occurs.
-/
theorem condensedRelativeKunneth
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hne : ringChar D.k ≠ ell) : Nonempty (ProductTheorem ell D.k) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.RelativeKunneth
