# AlgebraicGeometry.ProEtale.FiniteTripleProductNormalForms

## Reason

The proof needs binary restriction pasting and ordinary-product naturality as independent
statements. They must use the exact coordinate maps without importing the theorem they
support. Move the existing coordinate declarations verbatim into a definitions module,
publicly reexported by the original module. This is an import-cycle separation, not a
change of mathematical objects or a response to a compile-time limit.

## Old

The coordinate declarations occurred in
`lean/Sheaf/Paper/FiniteTripleProductNormalForms.lean` with the following verbatim text.

```lean
module

public import Sheaf.Paper.FiniteProductCompactification
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.Paper.FiniteOpenProductSwap
public import Sheaf.Paper.FiniteProperProductTranspose
public import Sheaf.Paper.CompactificationCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleCompositionTowerNormalization
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.Paper.FiniteDirectImageComposition
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence

/-! # Separate finite triple-product normal forms

Source: blueprint latest, sec-six-functors/sk-thm-sf-kunneth-relative,
lem-sf-kunneth-coherence.proof.md, clause (ii) and compactification reduction;
the concrete finite-level calculation in the DAG proof.
(blueprint: lem-pur-finite-triple-product-normal-forms).

The two bracketed products are evaluated on their respective actual iterated
Mathlib pullbacks. Thus no reassociation isomorphism is suppressed inside an
ill-typed equality. The conclusions are separate for these two representatives of
the triple product, exactly as in the node. Original compactifications are independent
of the displayed product compactifications. Both identities are asserted in every
original source and target coordinate system, expressing normalized change compatibility.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open SheafOfModules.OpenTensorNormalization

namespace AlgebraicGeometry.ProEtale
namespace FiniteTripleProduct

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Specialization of the existing ordinary unbounded category of fixed-scalar modules.
Source: finite purity conventions (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev D (X : Scheme.{u}) := FiniteD A X

/-- The recorded K-flat tensor, in its existing curried coordinates.
Source: finite derived operations (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev tensor (X : Scheme.{u}) (M N : D A X) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj N

/-- The exact open extension already used by the binary compactification statement.
Source: Stacks 03DI (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev extend {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory

/-- The recorded compact-support candidate, with no choice of a new functor.
Source: compactification conventions
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The recorded bounded-below etale-origin property on an ambient object.
Source: tensor-domain hypothesis (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev origin (X : Scheme.{u}) (M : D A X) :=
  DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M

/-- The actual binary external tensor, using the recorded pullback and tensor.
Source: the node's boxtimes (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev external {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (G : FiniteProductGeometry f g) (M : D A X) (N : D A Y) :=
  finiteProductExternal G (ModuleCat.{u + 1} A) M N

/-- Action on both inputs of external tensor, using its two actual projections.
Source: e12 boxtimes identity in the node
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def externalMap {X Y : Scheme.{u}}
    {T : Scheme.{u}} (r : T ⟶ X) (t : T ⟶ Y)
    {M M' : D A X} {N N' : D A Y} (m : M ⟶ M') (n : N ⟶ N') :=
  ((derivedTensor (ModuleCat.{u + 1} A) T).map
    (L(upperStar (ModuleCat.{u + 1} A) r).map m)).app
      (L(upperStar (ModuleCat.{u + 1} A) t).obj N) ≫
  ((derivedTensor (ModuleCat.{u + 1} A) T).obj
    (L(upperStar (ModuleCat.{u + 1} A) r).obj M')).map
      (L(upperStar (ModuleCat.{u + 1} A) t).map n)

/-- Xi with independently specified endpoint compactifications. The body is exactly
finiteProductChosenForward, hence includes both signed symmetries, PF, exchange and alpha.
Source: the displayed Xi (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def xi {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    [QuasiCompact f] [QuasiCompact g] (G : FiniteProductGeometry f g)
    (c : Compactification f) (d : Compactification g)
    (e : Compactification (G.q ≫ g)) (M : D A X) (N : D A Y)
    (h : origin A G.P (external A G M N)) :=
  letI : HasCompactification f := ⟨⟨c⟩⟩
  letI : HasCompactification g := ⟨⟨d⟩⟩
  letI : HasCompactification (G.q ≫ g) := ⟨⟨e⟩⟩
  finiteProductChosenForward G A c d e M N h

/-- Canonical comparison of arbitrary compact-support choices, retaining the origin domain:
the component of towerCandidateComparison (def-sf-origin-candidate-comparison).
Source: normalized refinement comparisons and their cocycle
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev compare {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (M : D A X) (h : origin A X M) :=
  (towerCandidateComparison A c d).app ⟨M, h⟩

variable {B X₁ X₂ X₃ : Scheme.{u}}
variable {f₁ : X₁ ⟶ B} {f₂ : X₂ ⟶ B} {f₃ : X₃ ⟶ B}
variable (c₁ : Compactification f₁) (c₂ : Compactification f₂) (c₃ : Compactification f₃)

/-- The displayed binary product geometry for factors 1 and 2.
Source: proof step 1 (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev g12 := finiteProductGeometry c₁ c₂

/-- The displayed binary product geometry for factors 2 and 3.
Source: proof step 1 (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev g23 := finiteProductGeometry c₂ c₃

/-- The displayed left outer product, compactifying the actual map from X12 to B.
Source: proof step 1 (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev gL := finiteProductGeometry (finiteProductCompactification (g12 c₁ c₂)) c₃

/-- The displayed right outer product, compactifying the actual map from X23 to B.
Source: proof step 1 (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev gR := finiteProductGeometry c₁ (finiteProductCompactification (g23 c₂ c₃))

variable (M₁ : D A X₁) (M₂ : D A X₂) (M₃ : D A X₃)

/-- D12=M1 boxtimes M2 on the actual binary product.
Source: node's left iterate (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev d12 := external A (g12 c₁ c₂) M₁ M₂

/-- D23=M2 boxtimes M3 on the actual binary product.
Source: node's right iterate (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev d23 := external A (g23 c₂ c₃) M₂ M₃

/-- Left-bracketed triple external tensor on its actual iterated fibre product.
Source: Theta_L (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev dL := external A (gL c₁ c₂ c₃) (d12 A c₁ c₂ M₁ M₂) M₃

/-- Right-bracketed triple external tensor on its actual iterated fibre product.
Source: Theta_R (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev dR := external A (gR c₁ c₂ c₃) M₁ (d23 A c₂ c₃ M₂ M₃)

/-- The ambient E12=H1 boxtimes H2, with H_i the actual open extension of M_i.
Source: proof steps 2 and 3 (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev e12Source := finiteProductExtendedTensor (g12 c₁ c₂) (ModuleCat.{u + 1} A) M₁ M₂

/-- The ambient E23=H2 boxtimes H3.
Source: proof steps 2 and 4 (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev e23Source := finiteProductExtendedTensor (g23 c₂ c₃) (ModuleCat.{u + 1} A) M₂ M₃

/-- The left ambient triple tensor, before the e12 comparison.
Source: e_L source (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev eLSource :=
  tensor A (gL c₁ c₂ c₃).T
    (L(upperStar (ModuleCat.{u + 1} A) (gL c₁ c₂ c₃).r).obj
      (e12Source A c₁ c₂ M₁ M₂))
    (L(upperStar (ModuleCat.{u + 1} A) (gL c₁ c₂ c₃).t).obj
      ((extend A c₃.i).obj M₃))

/-- The right ambient triple tensor, before the e23 comparison.
Source: e_R source (blueprint: lem-pur-finite-triple-product-normal-forms). -/
abbrev eRSource :=
  tensor A (gR c₁ c₂ c₃).T
    (L(upperStar (ModuleCat.{u + 1} A) (gR c₁ c₂ c₃).r).obj
      ((extend A c₁.i).obj M₁))
    (L(upperStar (ModuleCat.{u + 1} A) (gR c₁ c₂ c₃).t).obj
      (e23Source A c₂ c₃ M₂ M₃))

/-- Exactly e_L: external tensor of e12 with identity, followed by the outer normalized e.
The existing binary maps include the extension-by-zero compositors.
Source: the displayed e_L (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def eL :=
  externalMap A (gL c₁ c₂ c₃).r (gL c₁ c₂ c₃).t
    (finiteProductOpenTensor (g12 c₁ c₂) (ModuleCat.{u + 1} A) M₁ M₂) (𝟙 _) ≫
  finiteProductOpenTensor (gL c₁ c₂ c₃) (ModuleCat.{u + 1} A)
    (d12 A c₁ c₂ M₁ M₂) M₃

/-- Exactly e_R: external tensor of identity with e23, followed by the outer normalized e.
Source: the displayed e_R (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def eR :=
  externalMap A (gR c₁ c₂ c₃).r (gR c₁ c₂ c₃).t
    (𝟙 _) (finiteProductOpenTensor (g23 c₂ c₃) (ModuleCat.{u + 1} A) M₂ M₃) ≫
  finiteProductOpenTensor (gR c₁ c₂ c₃) (ModuleCat.{u + 1} A)
    M₁ (d23 A c₂ c₃ M₂ M₃)

/-- The open adjunction in total-left-derived pullback coordinates.
Source: section-unit normalization (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def openAdj {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    extend A j ⊣ L(upperStar (ModuleCat.{u + 1} A) j) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm

/-- Restrict an ambient external tensor along the product open, using supplied
restriction identifications of its two factors. Only pullback composition and the
canonical tensor comparison occur, making this usable recursively for triple products.
Source: restrictions of e_L and e_R to identity in proof step 2
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def restrictPair {B X Y : Scheme.{u}} {f : X ⟶ B} {g : Y ⟶ B}
    (G : FiniteProductGeometry f g) (M : D A X) (N : D A Y)
    (H : D A G.cf.Z) (J : D A G.cg.Z)
    (s : M ⟶ L(upperStar (ModuleCat.{u + 1} A) G.cf.i).obj H)
    (t : N ⟶ L(upperStar (ModuleCat.{u + 1} A) G.cg.i).obj J) :=
  let u := (finiteProductCompactification G).i
  let l := (finiteProductPullTriangle (ModuleCat.{u + 1} A) u G.r
    (G.p ≫ G.cf.i) (by
      change (finiteProductFirstOpen G ≫ finiteProductSecondOpen G) ≫ G.r = _
      rw [Category.assoc, finiteProductSecondOpen, IsPullback.lift_fst,
        ← Category.assoc, finiteProductFirstOpen_fst])).app H
  let r := (finiteProductPullTriangle (ModuleCat.{u + 1} A) u G.t
    (G.q ≫ G.cg.i) (by
      change (finiteProductFirstOpen G ≫ finiteProductSecondOpen G) ≫ G.t = _
      rw [Category.assoc, finiteProductSecondOpen_snd,
        finiteProductFirstOpen, IsPullback.lift_snd])).app J
  externalMap A G.p G.q s t ≫
    ((derivedTensor (ModuleCat.{u + 1} A) G.P).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) G.p G.cf.i).inv.app H ≫
        l.inv)).app _ ≫
    ((derivedTensor (ModuleCat.{u + 1} A) G.P).obj _).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) G.q G.cg.i).inv.app J ≫
        r.inv) ≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) u _ _).inv

/-- Restriction identification for the binary open product, using the two open units.
Source: normalized binary e (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def restriction12 :=
  restrictPair A (g12 c₁ c₂) M₁ M₂
    ((extend A c₁.i).obj M₁) ((extend A c₂.i).obj M₂)
    ((openAdj A c₁.i).unit.app M₁) ((openAdj A c₂.i).unit.app M₂)

/-- The analogous binary restriction for factors 2 and 3.
Source: normalized binary e (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def restriction23 :=
  restrictPair A (g23 c₂ c₃) M₂ M₃
    ((extend A c₂.i).obj M₂) ((extend A c₃.i).obj M₃)
    ((openAdj A c₂.i).unit.app M₂) ((openAdj A c₃.i).unit.app M₃)

/-- The left triple restriction identification, recursively using precisely the three units.
Source: e_L restricts to identity (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def restrictionL :=
  restrictPair A (gL c₁ c₂ c₃) (d12 A c₁ c₂ M₁ M₂) M₃
    (e12Source A c₁ c₂ M₁ M₂) ((extend A c₃.i).obj M₃)
    (restriction12 A c₁ c₂ M₁ M₂) ((openAdj A c₃.i).unit.app M₃)

/-- The right triple restriction identification, with the same three section units.
Source: e_R restricts to identity (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def restrictionR :=
  restrictPair A (gR c₁ c₂ c₃) M₁ (d23 A c₂ c₃ M₂ M₃)
    ((extend A c₁.i).obj M₁) (e23Source A c₂ c₃ M₂ M₃)
    ((openAdj A c₁.i).unit.app M₁) (restriction23 A c₂ c₃ M₂ M₃)

variable [QuasiCompact f₁] [QuasiCompact f₂] [QuasiCompact f₃]

/-- Left forward iterate, with arbitrary original compactifications, then the
normalized comparison to the displayed triple compactification.
Source: Theta_L(Xi) and Rh! = Rc*u! in the node
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def thetaL (o₁ : Compactification f₁) (o₂ : Compactification f₂)
    (o₃ : Compactification f₃)
    (o₁₂ : Compactification ((g12 c₁ c₂).q ≫ f₂))
    (oL : Compactification ((gL c₁ c₂ c₃).q ≫ f₃))
    (h₁₂ : origin A _ (d12 A c₁ c₂ M₁ M₂))
    (hL : origin A _ (dL A c₁ c₂ c₃ M₁ M₂ M₃)) :=
  finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
    (xi A (g12 c₁ c₂) o₁ o₂ o₁₂ M₁ M₂ h₁₂) ((support A o₃).obj M₃) ≫
  xi A (gL c₁ c₂ c₃) o₁₂ o₃ oL (d12 A c₁ c₂ M₁ M₂) M₃ hL ≫
  (compare A oL (finiteProductCompactification (gL c₁ c₂ c₃)) _ hL).hom

/-- Right forward iterate, separately in its actual bracketed triple coordinates.
Source: Theta_R(Xi) (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def thetaR (o₁ : Compactification f₁) (o₂ : Compactification f₂)
    (o₃ : Compactification f₃)
    (o₂₃ : Compactification ((g23 c₂ c₃).q ≫ f₃))
    (oR : Compactification ((gR c₁ c₂ c₃).q ≫ ((g23 c₂ c₃).q ≫ f₃)))
    (h₂₃ : origin A _ (d23 A c₂ c₃ M₂ M₃))
    (hR : origin A _ (dR A c₁ c₂ c₃ M₁ M₂ M₃)) :=
  finiteProductTensorMapRight (ModuleCat.{u + 1} A) B ((support A o₁).obj M₁)
    (xi A (g23 c₂ c₃) o₂ o₃ o₂₃ M₂ M₃ h₂₃) ≫
  xi A (gR c₁ c₂ c₃) o₁ o₂₃ oR M₁ (d23 A c₂ c₃ M₂ M₃) hR ≫
  (compare A oR (finiteProductCompactification (gR c₁ c₂ c₃)) _ hR).hom

/-- Three normalized source comparisons, with left tensor brackets.
Source: compactification-change clause
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def sourceL (o₁ : Compactification f₁) (o₂ : Compactification f₂)
    (o₃ : Compactification f₃) (h₁ : origin A X₁ M₁)
    (h₂ : origin A X₂ M₂) (h₃ : origin A X₃ M₃) :=
  finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
    (finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
      (compare A o₁ c₁ M₁ h₁).hom ((support A o₂).obj M₂) ≫
    finiteProductTensorMapRight (ModuleCat.{u + 1} A) B ((support A c₁).obj M₁)
      (compare A o₂ c₂ M₂ h₂).hom) ((support A o₃).obj M₃) ≫
  finiteProductTensorMapRight (ModuleCat.{u + 1} A) B
    (tensor A B ((support A c₁).obj M₁) ((support A c₂).obj M₂))
    (compare A o₃ c₃ M₃ h₃).hom

/-- Three normalized source comparisons, with right tensor brackets.
Source: compactification-change clause
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def sourceR (o₁ : Compactification f₁) (o₂ : Compactification f₂)
    (o₃ : Compactification f₃) (h₁ : origin A X₁ M₁)
    (h₂ : origin A X₂ M₂) (h₃ : origin A X₃ M₃) :=
  finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
    (compare A o₁ c₁ M₁ h₁).hom
      (tensor A B ((support A o₂).obj M₂) ((support A o₃).obj M₃)) ≫
  finiteProductTensorMapRight (ModuleCat.{u + 1} A) B ((support A c₁).obj M₁)
    (finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
      (compare A o₂ c₂ M₂ h₂).hom ((support A o₃).obj M₃) ≫
    finiteProductTensorMapRight (ModuleCat.{u + 1} A) B ((support A c₂).obj M₂)
      (compare A o₃ c₃ M₃ h₃).hom)

/-- Left ordinary triple word: Omega12 tensor identity, Omega12,3, then Rc*(e_L).
Source: first normal form (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def ordinaryL :=
  finiteProductTensorMapLeft (ModuleCat.{u + 1} A) B
    (finiteProductOrdinary A c₁.g c₂.g (g12 c₁ c₂).sqT
      ((extend A c₁.i).obj M₁) ((extend A c₂.i).obj M₂)) ((support A c₃).obj M₃) ≫
  finiteProductOrdinary A (finiteProductCompactification (g12 c₁ c₂)).g c₃.g
    (gL c₁ c₂ c₃).sqT (e12Source A c₁ c₂ M₁ M₂) ((extend A c₃.i).obj M₃) ≫
  R(lowerStar (ModuleCat.{u + 1} A)
    ((gL c₁ c₂ c₃).t ≫ c₃.g)).map (eL A c₁ c₂ c₃ M₁ M₂ M₃)

/-- Right ordinary triple word: identity tensor Omega23, Omega1,23, then Rc*(e_R).
Source: second normal form (blueprint: lem-pur-finite-triple-product-normal-forms). -/
def ordinaryR :=
  finiteProductTensorMapRight (ModuleCat.{u + 1} A) B ((support A c₁).obj M₁)
    (finiteProductOrdinary A c₂.g c₃.g (g23 c₂ c₃).sqT
      ((extend A c₂.i).obj M₂) ((extend A c₃.i).obj M₃)) ≫
  finiteProductOrdinary A c₁.g (finiteProductCompactification (g23 c₂ c₃)).g
    (gR c₁ c₂ c₃).sqT ((extend A c₁.i).obj M₁) (e23Source A c₂ c₃ M₂ M₃) ≫
  R(lowerStar (ModuleCat.{u + 1} A)
    ((gR c₁ c₂ c₃).t ≫ (finiteProductCompactification (g23 c₂ c₃)).g)).map
      (eR A c₁ c₂ c₃ M₁ M₂ M₃)

/-- Both equations in arbitrary original and displayed compactification coordinates.
The four domain conditions list exactly all tensors in the two binary and two outer
forward words. Each original endpoint may be changed independently: the comparisons
on both sides are the normalized common-refinement comparisons, not arbitrary maps.
Source: both displayed equalities, open-unit normalization and final change clause
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def Equations (o₁ : Compactification f₁) (o₂ : Compactification f₂)
    (o₃ : Compactification f₃)
    (o₁₂ : Compactification ((g12 c₁ c₂).q ≫ f₂))
    (o₂₃ : Compactification ((g23 c₂ c₃).q ≫ f₃))
    (oL : Compactification ((gL c₁ c₂ c₃).q ≫ f₃))
    (oR : Compactification ((gR c₁ c₂ c₃).q ≫ ((g23 c₂ c₃).q ≫ f₃)))
    (h₁ : origin A X₁ M₁) (h₂ : origin A X₂ M₂) (h₃ : origin A X₃ M₃)
    (b₁₂ : FiniteProductCompactificationDomain (g12 c₁ c₂) A o₁ o₂ M₁ M₂)
    (b₂₃ : FiniteProductCompactificationDomain (g23 c₂ c₃) A o₂ o₃ M₂ M₃)
    (bL : FiniteProductCompactificationDomain (gL c₁ c₂ c₃) A o₁₂ o₃
      (d12 A c₁ c₂ M₁ M₂) M₃)
    (bR : FiniteProductCompactificationDomain (gR c₁ c₂ c₃) A o₁ o₂₃
      M₁ (d23 A c₂ c₃ M₂ M₃)) : Prop :=
  IsIso (eL A c₁ c₂ c₃ M₁ M₂ M₃) ∧
  IsIso (eR A c₁ c₂ c₃ M₁ M₂ M₃) ∧
  (restrictionL A c₁ c₂ c₃ M₁ M₂ M₃ ≫
    L(upperStar (ModuleCat.{u + 1} A)
      (finiteProductCompactification (gL c₁ c₂ c₃)).i).map
        (eL A c₁ c₂ c₃ M₁ M₂ M₃) =
    (openAdj A (finiteProductCompactification (gL c₁ c₂ c₃)).i).unit.app
      (dL A c₁ c₂ c₃ M₁ M₂ M₃)) ∧
  (restrictionR A c₁ c₂ c₃ M₁ M₂ M₃ ≫
    L(upperStar (ModuleCat.{u + 1} A)
      (finiteProductCompactification (gR c₁ c₂ c₃)).i).map
        (eR A c₁ c₂ c₃ M₁ M₂ M₃) =
    (openAdj A (finiteProductCompactification (gR c₁ c₂ c₃)).i).unit.app
      (dR A c₁ c₂ c₃ M₁ M₂ M₃)) ∧
  thetaL A c₁ c₂ c₃ M₁ M₂ M₃ o₁ o₂ o₃ o₁₂ oL
    b₁₂.the project server.2 bL.the project server.2 =
      sourceL A c₁ c₂ c₃ M₁ M₂ M₃ o₁ o₂ o₃ h₁ h₂ h₃ ≫
        ordinaryL A c₁ c₂ c₃ M₁ M₂ M₃ ∧
  thetaR A c₁ c₂ c₃ M₁ M₂ M₃ o₁ o₂ o₃ o₂₃ oR
    b₂₃.the project server.2 bR.the project server.2 =
      sourceR A c₁ c₂ c₃ M₁ M₂ M₃ o₁ o₂ o₃ h₁ h₂ h₃ ≫
        ordinaryR A c₁ c₂ c₃ M₁ M₂ M₃

end FiniteTripleProduct

/-- The finite-level triple normal-form assertion, with the standing geometric
hypotheses and retained D+ antecedents. The local qcqs instances are consequences
of the finite-type structure maps, not additional hypotheses. All displayed and
original compactifications are universally quantified, including intermediate and
final ones; thus the equations are compatible with every normalized refinement.
Source: complete statement of the node
(blueprint: lem-pur-finite-triple-product-normal-forms). -/
def FiniteTripleProductNormalForms (C : WeilConjectures.PurityFiniteSetting.{u})
    {B X₁ X₂ X₃ : Scheme.{u}}
    [B.Over (Spec (.of C.field.k))] [X₁.Over (Spec (.of C.field.k))]
    [X₂.Over (Spec (.of C.field.k))] [X₃.Over (Spec (.of C.field.k))]
    [IsSeparated (B ↘ Spec (.of C.field.k))]
    [IsSeparated (X₁ ↘ Spec (.of C.field.k))]
    [IsSeparated (X₂ ↘ Spec (.of C.field.k))]
    [IsSeparated (X₃ ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (B ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X₂ ↘ Spec (.of C.field.k))]
    [LocallyOfFiniteType (X₃ ↘ Spec (.of C.field.k))]
    [QuasiCompact (B ↘ Spec (.of C.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of C.field.k))]
    [QuasiCompact (X₂ ↘ Spec (.of C.field.k))]
    [QuasiCompact (X₃ ↘ Spec (.of C.field.k))]
    (f₁ : X₁ ⟶ B) (f₂ : X₂ ⟶ B) (f₃ : X₃ ⟶ B)
    [f₁.IsOver (Spec (.of C.field.k))] [f₂.IsOver (Spec (.of C.field.k))]
    [f₃.IsOver (Spec (.of C.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    [IsSeparated f₂] [LocallyOfFiniteType f₂] [QuasiCompact f₂]
    [IsSeparated f₃] [LocallyOfFiniteType f₃] [QuasiCompact f₃]
    (M₁ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} C.Coefficient)))
    (M₂ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} C.Coefficient)))
    (M₃ : _root_.DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X₃) (ModuleCat.{u + 1} C.Coefficient)))
    (w₁ : Scheme.FixedEtaleOriginWitness X₁ C.Coefficient M₁)
    (w₂ : Scheme.FixedEtaleOriginWitness X₂ C.Coefficient M₂)
    (w₃ : Scheme.FixedEtaleOriginWitness X₃ C.Coefficient M₃) : Prop :=
  letI : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace
    (B ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace B := quasiSeparatedSpace_of_quasiSeparated
    (B ↘ Spec (.of C.field.k))
  letI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace
    (X₁ ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated
    (X₁ ↘ Spec (.of C.field.k))
  letI : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace
    (X₂ ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace X₂ := quasiSeparatedSpace_of_quasiSeparated
    (X₂ ↘ Spec (.of C.field.k))
  letI : CompactSpace X₃ := QuasiCompact.compactSpace_of_compactSpace
    (X₃ ↘ Spec (.of C.field.k))
  letI : QuasiSeparatedSpace X₃ := quasiSeparatedSpace_of_quasiSeparated
    (X₃ ↘ Spec (.of C.field.k))
  ∀ (c₁ : Compactification f₁) (c₂ : Compactification f₂) (c₃ : Compactification f₃)
    (o₁ : Compactification f₁) (o₂ : Compactification f₂) (o₃ : Compactification f₃)
    (o₁₂ : Compactification ((FiniteTripleProduct.g12 c₁ c₂).q ≫ f₂))
    (o₂₃ : Compactification ((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃))
    (oL : Compactification ((FiniteTripleProduct.gL c₁ c₂ c₃).q ≫ f₃))
    (oR : Compactification ((FiniteTripleProduct.gR c₁ c₂ c₃).q ≫
      ((FiniteTripleProduct.g23 c₂ c₃).q ≫ f₃)))
    (_sL : FiniteTripleProduct.origin C.Coefficient B
      (FiniteTripleProduct.tensor C.Coefficient B
        (FiniteTripleProduct.tensor C.Coefficient B
          ((FiniteTripleProduct.support C.Coefficient o₁).obj M₁.obj)
          ((FiniteTripleProduct.support C.Coefficient o₂).obj M₂.obj))
        ((FiniteTripleProduct.support C.Coefficient o₃).obj M₃.obj)))
    (_sR : FiniteTripleProduct.origin C.Coefficient B
      (FiniteTripleProduct.tensor C.Coefficient B
        ((FiniteTripleProduct.support C.Coefficient o₁).obj M₁.obj)
        (FiniteTripleProduct.tensor C.Coefficient B
          ((FiniteTripleProduct.support C.Coefficient o₂).obj M₂.obj)
          ((FiniteTripleProduct.support C.Coefficient o₃).obj M₃.obj))))
    (b₁₂ : FiniteProductCompactificationDomain (FiniteTripleProduct.g12 c₁ c₂)
      C.Coefficient o₁ o₂ M₁.obj M₂.obj)
    (b₂₃ : FiniteProductCompactificationDomain (FiniteTripleProduct.g23 c₂ c₃)
      C.Coefficient o₂ o₃ M₂.obj M₃.obj)
    (bL : FiniteProductCompactificationDomain (FiniteTripleProduct.gL c₁ c₂ c₃)
      C.Coefficient o₁₂ o₃ (FiniteTripleProduct.d12 C.Coefficient c₁ c₂ M₁.obj M₂.obj) M₃.obj)
    (bR : FiniteProductCompactificationDomain (FiniteTripleProduct.gR c₁ c₂ c₃)
      C.Coefficient o₁ o₂₃ M₁.obj (FiniteTripleProduct.d23 C.Coefficient c₂ c₃ M₂.obj M₃.obj)),
    FiniteTripleProduct.Equations C.Coefficient c₁ c₂ c₃ M₁.obj M₂.obj M₃.obj
      o₁ o₂ o₃ o₁₂ o₂₃ oL oR
      ⟨w₁.complex.obj, w₁.complex.property, ⟨w₁.iso⟩⟩
      ⟨w₂.complex.obj, w₂.complex.property, ⟨w₂.iso⟩⟩
      ⟨w₃.complex.obj, w₃.complex.property, ⟨w₃.iso⟩⟩ b₁₂ b₂₃ bL bR

```

## New

The same text occurs verbatim in `lean/Sheaf/Paper/FiniteTripleProductDefinitions.lean`,
followed by the namespace close and a module comment attaching the new definition node. The original module begins with
`public import Sheaf.Paper.FiniteTripleProductDefinitions` and retains its theorem.
No declaration name, signature, visibility, instance or mathematical definition changes.
The new definition node owns the moved declarations. The original node continues to
own `AlgebraicGeometry.ProEtale.finiteTripleProduct_normalForms`.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteTripleProductNormalForms --uses
AlgebraicGeometry.ProEtale.FiniteTripleProductNormalForms` reports no downstream modules,
and the original module itself as the sole textual user. No quarantined parent or
DAG parent is withdrawn: the theorem and every coordinate declaration remain available.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteTripleProductNormalForms | D4 | Public reexport of identical coordinate data |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | new in this delivery | Uses coordinate definitions |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | new in this delivery | Uses coordinate definitions |

## Status

landed 20261025T205910-L-3396657 2026-10-25 (merge of deliver/D4/Sheaf.Paper.FiniteTripleProductNormalForms)
