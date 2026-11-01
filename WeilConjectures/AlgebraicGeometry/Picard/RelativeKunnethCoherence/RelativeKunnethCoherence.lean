/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CurrentSixFunctorDatum
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormulaCoherence
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SmoothPurity.CompactificationProjectionComposition
import WeilConjectures.AlgebraicGeometry.SfIdentityProjectionNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.Picard.FiniteOpenProduct.FiniteOpenProductOperations
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange

/-! # Coherence of the canonical relative compact-support product

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-kunneth-relative/
lem-sf-kunneth-coherence.md, clauses (i)--(iv) and the finite-product consequence
(blueprint: lem-sf-kunneth-coherence).

The coefficient ring and operations are those of the current relative product theorem.
Cartesian squares are not tied to a particular choice of fibre product. Thus the swap and
associativity laws include the canonical identifications between different product models.
All comparison arrows below are actual composites of the published canonical operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace WeilConjectures.RelativeKunnethCoherence

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Tensor two isomorphisms using the existing derived tensor bifunctor.
Source: endpoint comparisons in (i)--(ii) (blueprint: lem-sf-kunneth-coherence). -/
def tensorIso {X : Scheme.{u}} {K K' L L' : CurrentDerived Λ X}
    (a : K ≅ K') (b : L ≅ L') :
    ((currentTensor X).obj K).obj L ≅ ((currentTensor X).obj K').obj L' :=
  ((currentTensor X).mapIso a).app L ≪≫ ((currentTensor X).obj K').mapIso b

/-- Compose pullbacks along a specified equality of scheme morphisms.
Source: canonical associativity identifications in (ii)
(blueprint: lem-sf-kunneth-coherence). -/
def pullPath {T U X : Scheme.{u}} (a : T ⟶ U) (p : U ⟶ X) (r : T ⟶ X)
    (w : a ≫ p = r) (K : CurrentDerived Λ X) :
    (currentPull a).obj ((currentPull p).obj K) ≅ (currentPull r).obj K :=
  ((AlgebraicGeometry.Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
    a p r w.symm).app K).symm

/-- A Cartesian product diagram, with the compactifications needed to evaluate the canonical
word in either order. The two total-map equalities retain one common structure morphism.
Source: (i), arbitrary realization of X times_B Y
(blueprint: lem-sf-kunneth-coherence). -/
structure Pair (B : Scheme.{u}) where
  X : Scheme.{u}
  Y : Scheme.{u}
  T : Scheme.{u}
  f : X ⟶ B
  g : Y ⟶ B
  p : T ⟶ X
  q : T ⟶ Y
  t : T ⟶ B
  square : IsPullback p q f g
  firstTotal : p ≫ f = t
  secondTotal : q ≫ g = t
  fSeparated : IsSeparated f
  fFiniteType : LocallyOfFiniteType f
  fQuasiCompact : QuasiCompact f
  gSeparated : IsSeparated g
  gFiniteType : LocallyOfFiniteType g
  gQuasiCompact : QuasiCompact g
  fCompactifiable : HasCompactification f
  gCompactifiable : HasCompactification g
  pCompactifiable : HasCompactification p
  qCompactifiable : HasCompactification q
  tCompactifiable : HasCompactification t
  pQuasiCompact : QuasiCompact p
  qQuasiCompact : QuasiCompact q
  tQuasiCompact : QuasiCompact t

attribute [instance] Pair.fSeparated Pair.fFiniteType Pair.fQuasiCompact
  Pair.gSeparated Pair.gFiniteType Pair.gQuasiCompact Pair.fCompactifiable
  Pair.gCompactifiable Pair.pCompactifiable Pair.qCompactifiable Pair.tCompactifiable
  Pair.pQuasiCompact Pair.qQuasiCompact Pair.tQuasiCompact

/-- The external product already defined by the project, on this Cartesian realization.
Source: the input of (i) (blueprint: lem-sf-kunneth-coherence). -/
def Pair.external {B : Scheme.{u}} (d : Pair B)
    (K : CurrentDerived Λ d.X) (L : CurrentDerived Λ d.Y) : CurrentDerived Λ d.T :=
  ((currentTensor d.T).obj ((currentPull d.p).obj K)).obj ((currentPull d.q).obj L)

/-- The six-factor comparison of the relative product theorem, with no new choice of map.
Source: the opening sentence of the coherence lemma
(blueprint: lem-sf-kunneth-coherence). -/
def Pair.kappa {B : Scheme.{u}} (d : Pair B)
    (K : CurrentDerived Λ d.X) (L : CurrentDerived Λ d.Y) :
    (currentShriek d.t).obj (d.external K L) ≅
      ((currentTensor B).obj ((currentShriek d.f).obj K)).obj ((currentShriek d.g).obj L) :=
  AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback Λ d.square d.t d.secondTotal K L

/-- The signed derived symmetry of the external product, on the common product model.
Source: (i), including the Koszul signs (blueprint: lem-sf-kunneth-coherence). -/
def Pair.sourceSwap {B : Scheme.{u}} (d : Pair B)
    (K : CurrentDerived Λ d.X) (L : CurrentDerived Λ d.Y) :
    (currentShriek d.t).obj (d.external K L) ≅
      (currentShriek d.t).obj (d.swap.external L K) :=
  (currentShriek d.t).mapIso
    (AlgebraicGeometry.Etale.derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) d.T _ _)

/-- The signed symmetry of the two compact-support images.
Source: (i), target symmetry (blueprint: lem-sf-kunneth-coherence). -/
def Pair.targetSwap {B : Scheme.{u}} (d : Pair B)
    (K : CurrentDerived Λ d.X) (L : CurrentDerived Λ d.Y) :
    ((currentTensor B).obj ((currentShriek d.f).obj K)).obj ((currentShriek d.g).obj L) ≅
      ((currentTensor B).obj ((currentShriek d.g).obj L)).obj ((currentShriek d.f).obj K) :=
  AlgebraicGeometry.Etale.derivedTensorBraidingIso (ModuleCat.{u + 1} Λ) B _ _

/-- Two binary products and their common triple-product realization. Equalities of projections
specify the canonical fibre-product associativity identification, rather than an arbitrary iso.
Source: (ii) (blueprint: lem-sf-kunneth-coherence). -/
structure Triple (B : Scheme.{u}) where
  xy : Pair B
  W : Scheme.{u}
  V : Scheme.{u}
  T : Scheme.{u}
  h : W ⟶ B
  vp : V ⟶ xy.Y
  vq : V ⟶ W
  a : T ⟶ xy.T
  b : T ⟶ W
  c : T ⟶ xy.X
  d : T ⟶ V
  total : T ⟶ B
  ywSquare : IsPullback vp vq xy.g h
  leftSquare : IsPullback a b xy.t h
  rightSquare : IsPullback c d xy.f (vq ≫ h)
  first : a ≫ xy.p = c
  middle : a ≫ xy.q = d ≫ vp
  last : b = d ≫ vq
  leftTotal : a ≫ xy.t = total
  lastTotal : b ≫ h = total
  firstTotal : c ≫ xy.f = total
  rightTotal : d ≫ (vq ≫ h) = total
  hSeparated : IsSeparated h
  hFiniteType : LocallyOfFiniteType h
  hQuasiCompact : QuasiCompact h
  hCompactifiable : HasCompactification h
  vpCompactifiable : HasCompactification vp
  vqCompactifiable : HasCompactification vq
  aCompactifiable : HasCompactification a
  bCompactifiable : HasCompactification b
  cCompactifiable : HasCompactification c
  dCompactifiable : HasCompactification d
  vTotalCompactifiable : HasCompactification (vq ≫ h)
  totalCompactifiable : HasCompactification total
  vpQuasiCompact : QuasiCompact vp
  vqQuasiCompact : QuasiCompact vq
  aQuasiCompact : QuasiCompact a
  bQuasiCompact : QuasiCompact b
  cQuasiCompact : QuasiCompact c
  dQuasiCompact : QuasiCompact d
  totalQuasiCompact : QuasiCompact total

attribute [instance] Triple.hSeparated Triple.hFiniteType Triple.hQuasiCompact
  Triple.hCompactifiable Triple.vpCompactifiable Triple.vqCompactifiable
  Triple.aCompactifiable Triple.bCompactifiable Triple.cCompactifiable Triple.dCompactifiable
  Triple.vTotalCompactifiable Triple.totalCompactifiable Triple.vpQuasiCompact
  Triple.vqQuasiCompact Triple.aQuasiCompact Triple.bQuasiCompact Triple.cQuasiCompact
  Triple.dQuasiCompact Triple.totalQuasiCompact

/-- The external tensor on the last two factors.
Source: (ii), L boxtimes M (blueprint: lem-sf-kunneth-coherence). -/
def Triple.ywExternal {B : Scheme.{u}} (s : Triple B)
    (L : CurrentDerived Λ s.xy.Y) (M : CurrentDerived Λ s.W) : CurrentDerived Λ s.V :=
  ((currentTensor s.V).obj ((currentPull s.vp).obj L)).obj ((currentPull s.vq).obj M)

/-- The left-associated external product on the common triple product.
Source: (ii) (blueprint: lem-sf-kunneth-coherence). -/
def Triple.leftExternal {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) : CurrentDerived Λ s.T :=
  ((currentTensor s.T).obj ((currentPull s.a).obj (s.xy.external K L))).obj
    ((currentPull s.b).obj M)

/-- The right-associated external product on the common triple product.
Source: (ii) (blueprint: lem-sf-kunneth-coherence). -/
def Triple.rightExternal {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) : CurrentDerived Λ s.T :=
  ((currentTensor s.T).obj ((currentPull s.c).obj K)).obj
    ((currentPull s.d).obj (s.ywExternal L M))

/-- The canonical external-product associator: distribute pullback over tensor, compose the
three pullbacks, apply the signed derived associator, and collect the last two factors.
Source: (ii), canonical source identification (blueprint: lem-sf-kunneth-coherence). -/
def Triple.externalAssoc {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) : s.leftExternal K L M ≅ s.rightExternal K L M :=
  tensorIso
    (AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) s.a _ _ ≪≫
      tensorIso (pullPath s.a s.xy.p s.c s.first K)
        (pullPath s.a s.xy.q (s.d ≫ s.vp) s.middle L))
    (eqToIso (congrArg (fun r ↦ (currentPull r).obj M) s.last)) ≪≫
    AlgebraicGeometry.Etale.derivedTensorAssociator (ModuleCat.{u + 1} Λ) s.T _ _ _ ≪≫
    tensorIso (Iso.refl _)
      (tensorIso (pullPath s.d s.vp (s.d ≫ s.vp) rfl L).symm
        (pullPath s.d s.vq (s.d ≫ s.vq) rfl M).symm ≪≫
        (AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso
          (ModuleCat.{u + 1} Λ) s.d _ _).symm)

/-- First apply kappa to (X times Y, W), then to (X,Y).
Source: (ii), left iterate (blueprint: lem-sf-kunneth-coherence). -/
def Triple.leftKappa {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) :=
  AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback Λ s.leftSquare
      s.total s.lastTotal (s.xy.external K L) M ≪≫
    tensorIso (s.xy.kappa K L) (Iso.refl _)

/-- First apply kappa to (X, Y times W), then to (Y,W).
Source: (ii), right iterate (blueprint: lem-sf-kunneth-coherence). -/
def Triple.rightKappa {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) :=
  AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback Λ s.rightSquare
      s.total s.rightTotal K (s.ywExternal L M) ≪≫
    tensorIso (Iso.refl _)
      (AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback Λ s.ywSquare
        (s.vq ≫ s.h) rfl L M)

/-- The source associativity identification after compact-support image.
Source: (ii) (blueprint: lem-sf-kunneth-coherence). -/
def Triple.sourceAssoc {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) :=
  (currentShriek s.total).mapIso (s.externalAssoc K L M)

/-- The target associator on the three compact-support images.
Source: (ii) (blueprint: lem-sf-kunneth-coherence). -/
def Triple.targetAssoc {B : Scheme.{u}} (s : Triple B)
    (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
    (M : CurrentDerived Λ s.W) :=
  AlgebraicGeometry.Etale.derivedTensorAssociator (ModuleCat.{u + 1} Λ) B
    ((currentShriek s.xy.f).obj K) ((currentShriek s.xy.g).obj L)
    ((currentShriek s.h).obj M)

/-- Functoriality in both inputs on the source of kappa.
Source: naturality in thm-sf-kunneth-relative, used in the finite-product consequence
(blueprint: lem-sf-kunneth-coherence). -/
def Pair.sourceInputIso {B : Scheme.{u}} (d : Pair B)
    {K K' : CurrentDerived Λ d.X} {L L' : CurrentDerived Λ d.Y}
    (a : K ≅ K') (b : L ≅ L') :=
  (currentShriek d.t).mapIso
    (tensorIso ((currentPull d.p).mapIso a) ((currentPull d.q).mapIso b))

/-- Functoriality in both inputs on the target of kappa.
Source: naturality in thm-sf-kunneth-relative, used in the finite-product consequence
(blueprint: lem-sf-kunneth-coherence). -/
def Pair.targetInputIso {B : Scheme.{u}} (d : Pair B)
    {K K' : CurrentDerived Λ d.X} {L L' : CurrentDerived Λ d.Y}
    (a : K ≅ K') (b : L ≅ L') :=
  tensorIso ((currentShriek d.f).mapIso a) ((currentShriek d.g).mapIso b)

/-- The generating comparison squares for changes of bracketing and order, with the
naturality of the recorded relative product map for insertion into larger products. A generator
contains geometric data and finite-Tor inputs, never the desired commutativity equation.
Source: finite-product consequence, rotations and adjacent swaps
(blueprint: lem-sf-kunneth-coherence). -/
inductive Elementary (k : Type u) [Field k] :
    {B : Scheme.{u}} → {A₀ A₁ Z₀ Z₁ : CurrentDerived Λ B} →
      (A₀ ⟶ Z₀) → (A₁ ⟶ Z₁) → (A₀ ≅ A₁) → (Z₀ ≅ Z₁) → Prop
  | swap {B : Scheme.{u}} (aB : B ⟶ Spec (.of k))
      [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
      (d : Pair B) (K : CurrentDerived Λ d.X) (L : CurrentDerived Λ d.Y)
      (hK : currentCtf Λ d.X K) (hL : currentCtf Λ d.Y L) :
      Elementary k (d.kappa K L).hom (d.swap.kappa L K).hom
        (d.sourceSwap K L) (d.targetSwap K L)
  | assoc {B : Scheme.{u}} (aB : B ⟶ Spec (.of k))
      [IsSeparated aB] [LocallyOfFiniteType aB] [QuasiCompact aB]
      (s : Triple B) (K : CurrentDerived Λ s.xy.X) (L : CurrentDerived Λ s.xy.Y)
      (M : CurrentDerived Λ s.W) (hK : currentCtf Λ s.xy.X K)
      (hL : currentCtf Λ s.xy.Y L) (hM : currentCtf Λ s.W M) :
      Elementary k (s.leftKappa K L M).hom (s.rightKappa K L M).hom
        (s.sourceAssoc K L M) (s.targetAssoc K L M)
  | naturality {B : Scheme.{u}} (d : Pair B)
      {K K' : CurrentDerived Λ d.X} {L L' : CurrentDerived Λ d.Y}
      (a : K ≅ K') (b : L ≅ L') :
      Elementary k (d.kappa K L).hom (d.kappa K' L').hom
        (d.sourceInputIso a b) (d.targetInputIso a b)

/-- Tensor two morphisms using the same bifunctor as in every comparison above.
Source: insertion of a local comparison into a finite product
(blueprint: lem-sf-kunneth-coherence). -/
def tensorMap {B : Scheme.{u}} {A A' Z Z' : CurrentDerived Λ B}
    (f : A ⟶ A') (g : Z ⟶ Z') :
    ((currentTensor B).obj A).obj Z ⟶ ((currentTensor B).obj A').obj Z' :=
  ((currentTensor B).map f).app Z ≫ ((currentTensor B).obj A').map g

/-- Finite words of canonical rotations and swaps, including their inverses, compositions,
functorial images, and insertion into tensor factors. Horizontal pasting inserts a comparison
inside an iterated Kunneth composite; vertical pasting changes its bracketing or order repeatedly.
The identity word includes the one-factor product. The endpoint isomorphisms are computed by
these constructors, not chosen to make the comparison commute.
Source: the finite-product consequence (blueprint: lem-sf-kunneth-coherence). -/
inductive Word (k : Type u) [Field k] :
    {B : Scheme.{u}} → {A₀ A₁ Z₀ Z₁ : CurrentDerived Λ B} →
      (A₀ ⟶ Z₀) → (A₁ ⟶ Z₁) → (A₀ ≅ A₁) → (Z₀ ≅ Z₁) → Prop
  | elementary {B : Scheme.{u}} {A₀ A₁ Z₀ Z₁ : CurrentDerived Λ B}
      {f : A₀ ⟶ Z₀} {g : A₁ ⟶ Z₁} {a : A₀ ≅ A₁} {z : Z₀ ≅ Z₁}
      (e : Elementary k f g a z) : Word k f g a z
  | refl {B : Scheme.{u}} {A Z : CurrentDerived Λ B} (f : A ⟶ Z) :
      Word k f f (Iso.refl A) (Iso.refl Z)
  | symm {B : Scheme.{u}} {A₀ A₁ Z₀ Z₁ : CurrentDerived Λ B}
      {f : A₀ ⟶ Z₀} {g : A₁ ⟶ Z₁} {a : A₀ ≅ A₁} {z : Z₀ ≅ Z₁}
      (w : Word k f g a z) : Word k g f a.symm z.symm
  | trans {B : Scheme.{u}} {A₀ A₁ A₂ Z₀ Z₁ Z₂ : CurrentDerived Λ B}
      {f : A₀ ⟶ Z₀} {g : A₁ ⟶ Z₁} {h : A₂ ⟶ Z₂}
      {a : A₀ ≅ A₁} {b : A₁ ≅ A₂} {z : Z₀ ≅ Z₁} {v : Z₁ ≅ Z₂}
      (w₁ : Word k f g a z) (w₂ : Word k g h b v) :
      Word k f h (a ≪≫ b) (z ≪≫ v)
  | paste {B : Scheme.{u}} {A₀ A₁ Z₀ Z₁ T₀ T₁ : CurrentDerived Λ B}
      {f : A₀ ⟶ Z₀} {g : A₁ ⟶ Z₁} {h : Z₀ ⟶ T₀} {j : Z₁ ⟶ T₁}
      {a : A₀ ≅ A₁} {z : Z₀ ≅ Z₁} {t : T₀ ≅ T₁}
      (w₁ : Word k f g a z) (w₂ : Word k h j z t) :
      Word k (f ≫ h) (g ≫ j) a t
  | map {B B' : Scheme.{u}} {A₀ A₁ Z₀ Z₁ : CurrentDerived Λ B}
      {f : A₀ ⟶ Z₀} {g : A₁ ⟶ Z₁} {a : A₀ ≅ A₁} {z : Z₀ ≅ Z₁}
      (F : CurrentDerived Λ B ⥤ CurrentDerived Λ B') (w : Word k f g a z) :
      Word k (F.map f) (F.map g) (F.mapIso a) (F.mapIso z)
  | tensor {B : Scheme.{u}} {A₀ A₁ Z₀ Z₁ T₀ T₁ U₀ U₁ : CurrentDerived Λ B}
      {f : A₀ ⟶ Z₀} {g : A₁ ⟶ Z₁} {h : T₀ ⟶ U₀} {j : T₁ ⟶ U₁}
      {a : A₀ ≅ A₁} {z : Z₀ ≅ Z₁} {t : T₀ ≅ T₁} {v : U₀ ≅ U₁}
      (w₁ : Word k f g a z) (w₂ : Word k h j t v) :
      Word k (tensorMap f h) (tensorMap g j) (tensorIso a t) (tensorIso z v)

/-- Every finite comparison word commutes. Rotations and adjacent swaps generate all
parenthesizations and orders; tensor and functor contexts cover changes inside any subtree.
Closed-subscheme compact-support products use exactly the same words after ordinary
restriction to the closed subschemes, as in the recorded relative-product theorem.
Source: final sentence (blueprint: lem-sf-kunneth-coherence). -/
def FiniteCoherence (k : Type u) [Field k] : Prop :=
  ∀ {B : Scheme.{u}} {A₀ A₁ Z₀ Z₁ : CurrentDerived Λ B}
    (f : A₀ ⟶ Z₀) (g : A₁ ⟶ Z₁) (a : A₀ ≅ A₁) (z : Z₀ ≅ Z₁),
    Word k f g a z → a.hom ≫ g = f ≫ z.hom

end WeilConjectures.RelativeKunnethCoherence
