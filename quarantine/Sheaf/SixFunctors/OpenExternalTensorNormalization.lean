/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.SixFunctorDualNotation
public import Sheaf.Paper.FiniteOpenProductSwap
import Sheaf.SixFunctors.OpenTensorNormalization
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Unique
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-!
# Normalized open external tensor comparison

Source: the symmetry paragraph of the proof of `lem-sf-kunneth-coherence`,
`sec-six-functors/sk-thm-sf-kunneth-relative`, blueprint main-20261015;
Stacks Project, Tags 0GL1, 03S6, 0B65
(blueprint: lem-sf-open-external-tensor-normalization).

The auxiliary constructions use ordinary unbounded finite-coefficient categories.
All comparisons are the canonical adjunction, base-change and projection maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace AlgebraicGeometry.ProEtale.OpenExternalTensor

open WeilConjectures

/-- The canonical derived associator, evaluated before coefficient specialization.
It is induced by the signed total tensor, as is the existing derived tensor itself.
Source: Stacks 06YS and the associator in proof step 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
def proetAssociator (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalClosed V]
    [MonoidalPreadditive V] [SymmetricCategory V] [Abelian.HasFunctorialFlatResolution V]
    (Z : Scheme.{u}) (K L M : DerivedCategory (Sheaf (ProEt.topology Z) V)) :
    ((ProEtale.derivedTensor V Z).obj (((ProEtale.derivedTensor V Z).obj K).obj L)).obj M ≅
      ((ProEtale.derivedTensor V Z).obj K).obj (((ProEtale.derivedTensor V Z).obj L).obj M) :=
  α_ K L M

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Transport open extension along equality of its geometric map. Source: Stacks 03DI
(blueprint: lem-sf-open-external-tensor-normalization). -/
def shriekCongr {U V : Scheme.{u}} {f g : U ⟶ V}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) :
    finiteShriek A f ≅ finiteShriek A g :=
  eqToIso (by cases h; rfl)

/-- The two chosen intermediate products and all their canonical projection squares.
The outer product cones are specified separately by the final statement. These fields
only record choices of the two factorizations of the product open, with their equations.
Source: the two factorizations in the node's statement and proof steps 3, 4, 6
(blueprint: lem-sf-open-external-tensor-normalization). -/
structure Diagram {X Y Xb Yb : Scheme.{u}} (j : X ⟶ Xb) (k : Y ⟶ Yb)
    (T Tb : Scheme.{u}) [IsOpenImmersion j] [IsOpenImmersion k] where
  S : Scheme.{u}
  S' : Scheme.{u}
  pb : Tb ⟶ Xb
  qb : Tb ⟶ Yb
  p : T ⟶ X
  q : T ⟶ Y
  u : T ⟶ Tb
  r : S ⟶ X
  s : S ⟶ Yb
  j₁ : S ⟶ Tb
  k₁ : T ⟶ S
  r' : S' ⟶ Xb
  s' : S' ⟶ Y
  k₂ : S' ⟶ Tb
  j₂ : T ⟶ S'
  [open_j₁ : IsOpenImmersion j₁]
  [open_k₁ : IsOpenImmersion k₁]
  [open_k₂ : IsOpenImmersion k₂]
  [open_j₂ : IsOpenImmersion j₂]
  [open_u : IsOpenImmersion u]
  first : IsPullback r j₁ j pb
  second : IsPullback q k₁ k s
  first' : IsPullback s' k₂ k qb
  second' : IsPullback p j₂ j r'
  j₁_qb : j₁ ≫ qb = s
  k₁_r : k₁ ≫ r = p
  k₂_pb : k₂ ≫ pb = r'
  j₂_s' : j₂ ≫ s' = q
  factor : k₁ ≫ j₁ = u
  factor' : j₂ ≫ k₂ = u
  left : u ≫ pb = p ≫ j
  right : u ≫ qb = q ≫ k

attribute [instance] Diagram.open_j₁ Diagram.open_k₁
  Diagram.open_k₂ Diagram.open_j₂ Diagram.open_u

variable {X Y Xb Yb T Tb : Scheme.{u}} {j : X ⟶ Xb} {k : Y ⟶ Yb}
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- Swap the factors, on the same chosen fiber product. This means that the swapped
product has already been transported back along its canonical swap isomorphism.
Source: proof step 7 (blueprint: lem-sf-open-external-tensor-normalization). -/
def Diagram.swap (d : Diagram j k T Tb) : Diagram k j T Tb where
  S := d.S'
  S' := d.S
  pb := d.qb
  qb := d.pb
  p := d.q
  q := d.p
  u := d.u
  r := d.s'
  s := d.r'
  j₁ := d.k₂
  k₁ := d.j₂
  r' := d.s
  s' := d.r
  k₂ := d.j₁
  j₂ := d.k₁
  first := d.first'
  second := d.second'
  first' := d.first
  second' := d.second
  j₁_qb := d.k₂_pb
  k₁_r := d.j₂_s'
  k₂_pb := d.j₁_qb
  j₂_s' := d.k₁_r
  factor := d.factor'
  factor' := d.factor
  left := d.right
  right := d.left

/-- The ambient external product of the two extensions.
Source: the definition of H in proof step 6
(blueprint: lem-sf-open-external-tensor-normalization). -/
def ambient (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) : FiniteD A Tb :=
  FiniteOpenProduct.tensor A Tb
    ((FiniteOpenProduct.pull A d.pb).obj ((finiteShriek A j).obj K))
    ((FiniteOpenProduct.pull A d.qb).obj ((finiteShriek A k).obj L))

/-- The external product on the open.
Source: D in the statement (blueprint: lem-sf-open-external-tensor-normalization). -/
def inside (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) : FiniteD A T :=
  FiniteOpenProduct.tensor A T
    ((FiniteOpenProduct.pull A d.p).obj K) ((FiniteOpenProduct.pull A d.q).obj L)

/-- The prescribed first-factor construction: beta for j, gamma for j₁, beta for k,
then signed symmetry, gamma for k₁, signed symmetry inside k₁!, and the normalized
composition comparison. All equalities are transported by pullback composition.
Source: proof steps 3 and 4, Stacks 03S6 and 0GL1
(blueprint: lem-sf-open-external-tensor-normalization). -/
def comparison (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensorMap A Tb
      ((ProEtale.ordinaryOpenExtensionBaseChangeIso A
        d.r d.j₁ j d.pb d.first).hom.app K) (𝟙 _) ≫
    FiniteOpenProduct.gamma A d.j₁ ((FiniteOpenProduct.pull A d.r).obj K)
      ((FiniteOpenProduct.pull A d.qb).obj ((finiteShriek A k).obj L)) ≫
    (finiteShriek A d.j₁).map
      (FiniteOpenProduct.tensorMap A d.S (𝟙 _)
        (((FiniteOpenProduct.pullComp A d.j₁ d.qb).symm ≪≫
          eqToIso (congrArg (FiniteOpenProduct.pull A) d.j₁_qb)).hom.app
            ((finiteShriek A k).obj L))) ≫
    (finiteShriek A d.j₁).map
      (FiniteOpenProduct.tensorMap A d.S (𝟙 _)
        ((ProEtale.ordinaryOpenExtensionBaseChangeIso A
          d.q d.k₁ k d.s d.second).hom.app L)) ≫
    (finiteShriek A d.j₁).map
      (FiniteOpenProduct.rho A d.k₁
        ((FiniteOpenProduct.pull A d.r).obj K) ((FiniteOpenProduct.pull A d.q).obj L) ≫
        (finiteShriek A d.k₁).map
          (FiniteOpenProduct.tensorMap A T
            (((FiniteOpenProduct.pullComp A d.k₁ d.r).symm ≪≫
              eqToIso (congrArg (FiniteOpenProduct.pull A) d.k₁_r)).hom.app K) (𝟙 _))) ≫
    ((FiniteOpenProduct.comp A d.k₁ d.j₁) ≪≫
      shriekCongr A d.factor).hom.app (inside A d K L)

/-- Identify D with the restriction of H by the inverse tensor comparison, the two
projection squares and the section-normalized open units.
Source: proof step 5 (blueprint: lem-sf-open-external-tensor-normalization). -/
def restriction (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.tensorMap A T
    ((FiniteOpenProduct.pull A d.p).map ((FiniteOpenProduct.adj A j).unit.app K) ≫
      (FiniteOpenProduct.square A _ _ _ _ d.left).inv.app ((finiteShriek A j).obj K))
    ((FiniteOpenProduct.pull A d.q).map ((FiniteOpenProduct.adj A k).unit.app L) ≫
      (FiniteOpenProduct.square A _ _ _ _ d.right).inv.app ((finiteShriek A k).obj L)) ≫
    (FiniteOpenProduct.tensorPullIso A d.u _ _).inv

/-- The other factorization, with both signed interchanges in the specified places.
Source: proof step 6 (blueprint: lem-sf-open-external-tensor-normalization). -/
def oppositeComparison (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) :=
  FiniteOpenProduct.sigma A Tb _ _ ≫ comparison A d.swap L K ≫
    (finiteShriek A d.u).map (FiniteOpenProduct.sigma A T _ _)

/-- Morphisms of the ambient external product. Source: the naturality clause
(blueprint: lem-sf-open-external-tensor-normalization). -/
def ambientMap (d : Diagram j k T Tb) {K K' : FiniteD A X} {L L' : FiniteD A Y}
    (a : K ⟶ K') (b : L ⟶ L') : ambient A d K L ⟶ ambient A d K' L' :=
  FiniteOpenProduct.tensorMap A Tb
    ((FiniteOpenProduct.pull A d.pb).map ((finiteShriek A j).map a))
    ((FiniteOpenProduct.pull A d.qb).map ((finiteShriek A k).map b))

/-- Morphisms of the open external product. Source: the naturality clause
(blueprint: lem-sf-open-external-tensor-normalization). -/
def insideMap (d : Diagram j k T Tb) {K K' : FiniteD A X} {L L' : FiniteD A Y}
    (a : K ⟶ K') (b : L ⟶ L') : inside A d K L ⟶ inside A d K' L' :=
  FiniteOpenProduct.tensorMap A T
    ((FiniteOpenProduct.pull A d.p).map a) ((FiniteOpenProduct.pull A d.q).map b)

/-- The binary normalization, opposite-factorization and signed-symmetry equations.
The symmetry is written after transporting the swapped products to the same cones.
Source: proof steps 5--7 (blueprint: lem-sf-open-external-tensor-normalization). -/
def BinaryAssertion (d : Diagram j k T Tb) (K : FiniteD A X) (L : FiniteD A Y) : Prop :=
  IsIso (comparison A d K L) ∧ IsIso (oppositeComparison A d K L) ∧
    (restriction A d K L ≫ (FiniteOpenProduct.pull A d.u).map (comparison A d K L) =
      (FiniteOpenProduct.adj A d.u).unit.app (inside A d K L)) ∧
    (oppositeComparison A d K L = comparison A d K L) ∧
    (comparison A d K L ≫ (finiteShriek A d.u).map
        (FiniteOpenProduct.sigma A T
          ((FiniteOpenProduct.pull A d.p).obj K) ((FiniteOpenProduct.pull A d.q).obj L)) =
      FiniteOpenProduct.sigma A Tb
          ((FiniteOpenProduct.pull A d.pb).obj ((finiteShriek A j).obj K))
          ((FiniteOpenProduct.pull A d.qb).obj ((finiteShriek A k).obj L)) ≫
        comparison A d.swap L K)

variable {W Wb T₁₂ T₂₃ Tb₁₂ Tb₂₃ : Scheme.{u}} {l : W ⟶ Wb}
  [IsOpenImmersion l]

/-- The projection equations for the two bracketings of the same triple product.
No comparison is chosen as extra data: the equations are used only with the canonical
pullback-composition maps. Source: proof step 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
structure Triple
    (d₁₂ : Diagram j k T₁₂ Tb₁₂) (d₂₃ : Diagram k l T₂₃ Tb₂₃)
    (dL : Diagram d₁₂.u l T Tb) (dR : Diagram j d₂₃.u T Tb) : Prop where
  outer₁ : dL.pb ≫ d₁₂.pb = dR.pb
  outer₂ : dL.pb ≫ d₁₂.qb = dR.qb ≫ d₂₃.pb
  outer₃ : dL.qb = dR.qb ≫ d₂₃.qb
  inner₁ : dL.p ≫ d₁₂.p = dR.p
  inner₂ : dL.p ≫ d₁₂.q = dR.q ≫ d₂₃.p
  inner₃ : dL.q = dR.q ≫ d₂₃.q
  sameOpen : dR.u = dL.u

/-- The triple ambient object, with left bracketing and composed projection pullbacks.
Source: H₃ in proof step 8 (blueprint: lem-sf-open-external-tensor-normalization). -/
def tripleAmbient (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) : FiniteD A Tb :=
  FiniteOpenProduct.tensor A Tb
    (FiniteOpenProduct.tensor A Tb
      ((FiniteOpenProduct.pull A dL.pb).obj
        ((FiniteOpenProduct.pull A d₁₂.pb).obj ((finiteShriek A j).obj K)))
      ((FiniteOpenProduct.pull A dL.pb).obj
        ((FiniteOpenProduct.pull A d₁₂.qb).obj ((finiteShriek A k).obj L))))
    ((FiniteOpenProduct.pull A dL.qb).obj ((finiteShriek A l).obj M))

/-- The triple open object with the same left bracketing.
Source: D₃ in proof step 8 (blueprint: lem-sf-open-external-tensor-normalization). -/
def tripleInside (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) : FiniteD A T :=
  FiniteOpenProduct.tensor A T
    (FiniteOpenProduct.tensor A T
      ((FiniteOpenProduct.pull A dL.p).obj ((FiniteOpenProduct.pull A d₁₂.p).obj K))
      ((FiniteOpenProduct.pull A dL.p).obj ((FiniteOpenProduct.pull A d₁₂.q).obj L)))
    ((FiniteOpenProduct.pull A dL.q).obj M)

/-- First compare the first two factors, then their product with the third.
Source: F in proof step 8 (blueprint: lem-sf-open-external-tensor-normalization). -/
def tripleLeft (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) :=
  (FiniteOpenProduct.tensorIsoMap A _
    (FiniteOpenProduct.tensorPullIso A dL.pb _ _).symm (Iso.refl _)).hom ≫
    FiniteOpenProduct.tensorMap A Tb
      ((FiniteOpenProduct.pull A dL.pb).map (comparison A d₁₂ K L)) (𝟙 _) ≫
    comparison A dL (inside A d₁₂ K L) M ≫
    (finiteShriek A dL.u).map
      (FiniteOpenProduct.tensorIsoMap A _
        (FiniteOpenProduct.tensorPullIso A dL.p _ _) (Iso.refl _)).hom

/-- The canonical outer reassociation and projection-composition identification.
Source: the ambient associator in proof step 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
def outerAssociator
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) :
    tripleAmbient A d₁₂ dL K L M ≅
      FiniteOpenProduct.tensor A Tb
        ((FiniteOpenProduct.pull A dR.pb).obj ((finiteShriek A j).obj K))
        ((FiniteOpenProduct.pull A dR.qb).obj (ambient A d₂₃ L M)) :=
  FiniteOpenProduct.tensorIsoMap A _ (FiniteOpenProduct.tensorIsoMap A _
      (((FiniteOpenProduct.pullComp A dL.pb d₁₂.pb).symm ≪≫
        eqToIso (congrArg (FiniteOpenProduct.pull A) t.outer₁)).app ((finiteShriek A j).obj K))
      ((FiniteOpenProduct.square A _ _ _ _ t.outer₂).app ((finiteShriek A k).obj L)))
    ((eqToIso (congrArg (FiniteOpenProduct.pull A) t.outer₃) ≪≫
      FiniteOpenProduct.pullComp A dR.qb d₂₃.qb).app ((finiteShriek A l).obj M)) ≪≫
    (proetAssociator (ModuleCat.{u + 1} A) Tb _ _ _) ≪≫
      FiniteOpenProduct.tensorIsoMap A _ (Iso.refl _)
      (FiniteOpenProduct.tensorPullIso A dR.qb _ _).symm

/-- Reassociate the open factors using exactly the same projection-composition maps.
Source: the open associator in proof step 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
def innerAssociator
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) :
    inside A dR K (inside A d₂₃ L M) ≅ tripleInside A d₁₂ dL K L M :=
  FiniteOpenProduct.tensorIsoMap A _ (Iso.refl _) (FiniteOpenProduct.tensorPullIso A dR.q _ _) ≪≫
    FiniteOpenProduct.tensorIsoMap A _
      (((eqToIso (congrArg (FiniteOpenProduct.pull A) t.inner₁)).symm ≪≫
        FiniteOpenProduct.pullComp A dL.p d₁₂.p).app K)
      (FiniteOpenProduct.tensorIsoMap A _ ((FiniteOpenProduct.square A _ _ _ _ t.inner₂).symm.app L)
        (((FiniteOpenProduct.pullComp A dR.q d₂₃.q).symm ≪≫
          eqToIso (congrArg (FiniteOpenProduct.pull A) t.inner₃.symm)).app M)) ≪≫
    (proetAssociator (ModuleCat.{u + 1} A) T _ _ _).symm

/-- First compare the last two factors, then the first factor with their product.
The final transport is the identity of the common product open, followed by its
canonical associator. Source: G in proof step 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
def tripleRight
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) :=
  (outerAssociator A t K L M).hom ≫
    FiniteOpenProduct.tensorMap A Tb (𝟙 _)
      ((FiniteOpenProduct.pull A dR.qb).map (comparison A d₂₃ L M)) ≫
    comparison A dR K (inside A d₂₃ L M) ≫
    (finiteShriek A dR.u).map (innerAssociator A t K L M).hom ≫
    (shriekCongr A t.sameOpen).hom.app (tripleInside A d₁₂ dL K L M)

/-- The triple restriction uses the same section units and tensor comparisons on
both sides; it contains no occurrence of either triple comparison.
Source: the identity-on-the-open clause in proof step 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
def tripleRestriction (d₁₂ : Diagram j k T₁₂ Tb₁₂) (dL : Diagram d₁₂.u l T Tb)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) :=
  FiniteOpenProduct.tensorMap A T
    ((FiniteOpenProduct.tensorPullIso A dL.p _ _).inv ≫
      (FiniteOpenProduct.pull A dL.p).map (restriction A d₁₂ K L) ≫
        (FiniteOpenProduct.square A _ _ _ _ dL.left).inv.app (ambient A d₁₂ K L))
    ((FiniteOpenProduct.pull A dL.q).map ((FiniteOpenProduct.adj A l).unit.app M) ≫
      (FiniteOpenProduct.square A _ _ _ _ dL.right).inv.app ((finiteShriek A l).obj M)) ≫
    (FiniteOpenProduct.tensorPullIso A dL.u _ _).inv ≫
    (FiniteOpenProduct.pull A dL.u).map
      (FiniteOpenProduct.tensorIsoMap A _
        (FiniteOpenProduct.tensorPullIso A dL.pb _ _) (Iso.refl _)).hom

/-- Equality of the two triple composites, and their separate identity restrictions.
Source: proof step 8 (blueprint: lem-sf-open-external-tensor-normalization). -/
def TripleAssertion
    {d₁₂ : Diagram j k T₁₂ Tb₁₂} {d₂₃ : Diagram k l T₂₃ Tb₂₃}
    {dL : Diagram d₁₂.u l T Tb} {dR : Diagram j d₂₃.u T Tb}
    (t : Triple d₁₂ d₂₃ dL dR)
    (K : FiniteD A X) (L : FiniteD A Y) (M : FiniteD A W) : Prop :=
  tripleLeft A d₁₂ dL K L M = tripleRight A t K L M ∧
    (tripleRestriction A d₁₂ dL K L M ≫
      (FiniteOpenProduct.pull A dL.u).map (tripleLeft A d₁₂ dL K L M) =
        (FiniteOpenProduct.adj A dL.u).unit.app
          (tripleInside A d₁₂ dL K L M)) ∧
    (tripleRestriction A d₁₂ dL K L M ≫
      (FiniteOpenProduct.pull A dL.u).map (tripleRight A t K L M) =
        (FiniteOpenProduct.adj A dL.u).unit.app
          (tripleInside A d₁₂ dL K L M))

open WeilConjectures

/-- The finite-level assertion in the six-functor setting. Inputs are exactly the
recorded bounded constructible finite-Tor objects; their fixed-scalar coordinates
are given by the inverse of the recorded intrinsic realization equivalence.
The binary and triple constructions themselves are defined on the ambient categories,
so their intermediate tensors need no extra constructibility hypotheses.
Source: the node's finite-coefficient setting and proof steps 1 and 8
(blueprint: lem-sf-open-external-tensor-normalization). -/
def FiniteAssertion
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (_S : SixFunctorDatum D C E n hn)
    {B X₀ Y₀ Xb₀ Yb₀ : SixFunctorSpace D}
    (j₀ : X₀ ⟶ Xb₀) (k₀ : Y₀ ⟶ Yb₀)
    [IsOpenImmersion j₀.hom.left] [IsOpenImmersion k₀.hom.left]
    (f : Xb₀ ⟶ B) (g : Yb₀ ⟶ B)
    {T₀ Tb₀ : Scheme.{u}} (d : Diagram j₀.hom.left k₀.hom.left T₀ Tb₀)
    (K : finiteTorConstructibleCategory C.l E n hn X₀.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y₀.obj.left) : Prop :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  let A₀ := ULift.{u + 1, u} (Padic.coefficientExtensionRing C.l E n)
  let K₀ := (sixFunctorFiniteRealization D C E n hn X₀).inverse.obj K.obj
  let L₀ := (sixFunctorFiniteRealization D C E n hn Y₀).inverse.obj L.obj
  BinaryAssertion A₀ d K₀ L₀ ∧
    (∀ (K' : finiteTorConstructibleCategory C.l E n hn X₀.obj.left)
      (L' : finiteTorConstructibleCategory C.l E n hn Y₀.obj.left)
      (a : K ⟶ K') (b : L ⟶ L'),
      comparison A₀ d K₀ L₀ ≫ (finiteShriek A₀ d.u).map
          (insideMap A₀ d
            ((sixFunctorFiniteRealization D C E n hn X₀).inverse.map a.hom)
            ((sixFunctorFiniteRealization D C E n hn Y₀).inverse.map b.hom)) =
        ambientMap A₀ d
            ((sixFunctorFiniteRealization D C E n hn X₀).inverse.map a.hom)
            ((sixFunctorFiniteRealization D C E n hn Y₀).inverse.map b.hom) ≫
          (comparison A₀ d
            ((sixFunctorFiniteRealization D C E n hn X₀).inverse.obj K'.obj)
            ((sixFunctorFiniteRealization D C E n hn Y₀).inverse.obj L'.obj))) ∧
    (∀ (W₀ Wb₀ : SixFunctorSpace D) (_ : IsSeparated W₀.obj.hom)
      (_ : IsSeparated Wb₀.obj.hom) (l₀ : W₀ ⟶ Wb₀)
      [IsOpenImmersion l₀.hom.left] (h : Wb₀ ⟶ B)
      (_ : IsSeparated h.hom.left) (_ : LocallyOfFiniteType h.hom.left)
      (_ : QuasiCompact h.hom.left)
      (M : finiteTorConstructibleCategory C.l E n hn W₀.obj.left)
      (T₂₃ Tb₂₃ T₃ Tb₃ : Scheme.{u})
      (d₂₃ : Diagram k₀.hom.left l₀.hom.left T₂₃ Tb₂₃)
      (dL : Diagram d.u l₀.hom.left T₃ Tb₃)
      (dR : Diagram j₀.hom.left d₂₃.u T₃ Tb₃)
      (t : Triple d d₂₃ dL dR),
      IsPullback d₂₃.pb d₂₃.qb g.hom.left h.hom.left →
      IsPullback d₂₃.p d₂₃.q (k₀.hom.left ≫ g.hom.left) (l₀.hom.left ≫ h.hom.left) →
      IsPullback dL.pb dL.qb (d.pb ≫ f.hom.left) h.hom.left →
      IsPullback dL.p dL.q (d.p ≫ j₀.hom.left ≫ f.hom.left)
        (l₀.hom.left ≫ h.hom.left) →
      IsPullback dR.pb dR.qb f.hom.left (d₂₃.pb ≫ g.hom.left) →
      IsPullback dR.p dR.q (j₀.hom.left ≫ f.hom.left)
        (d₂₃.p ≫ k₀.hom.left ≫ g.hom.left) →
      TripleAssertion A₀ t K₀ L₀
        ((sixFunctorFiniteRealization D C E n hn W₀).inverse.obj M.obj))

/-- The normalized finite open external-tensor comparison, with naturality, independence
of the order of the two opens, signed symmetry and triple associativity.

Source: blueprint main-20261015, `sec-six-functors/sk-thm-sf-kunneth-relative/`
`lem-sf-kunneth-coherence.proof.md`, symmetry paragraph; Stacks 0GL1, 03S6, 0B65
(blueprint: lem-sf-open-external-tensor-normalization).

Proof plan, following the node's eight steps:
1. Specialize `openTensorNormalization` to the finite constant coefficient ring. Its
   beta and gamma agree with the recorded finite maps, have identity restrictions,
   and its open extensions have invertible section units and are fully faithful.
2. Compose open adjunctions. The comparison `FiniteOpenProduct.comp` is `leftAdjointUniq` with
   the specified pullback compositor, so it preserves the pasted units. Uniqueness
   gives the coherent normalized comparison for three opens (0DV0 and 0B65).
3. Base-change j along the first projection and apply gamma for j₁.
4. Base-change k along the remaining projection. Apply signed symmetry, gamma for
   k₁ and signed symmetry inside k₁!, then the normalized composition comparison.
   This is exactly `comparison`. Every factor is a natural isomorphism.
5. Restrict to the product open. Beta, gamma and the composition comparison are
   identities under `restriction` and `openUnit`. The two signed symmetries cancel:
   (-1)^(ij) times (-1)^(ji) is 1. Pullback/tensor compatibility is computed on the
   same K-flat total tensor models by the tensor-pullback and descent dependencies.
6. The opposite-factorization map has the same restriction. Compose both maps
   with the inverse of `comparison` and use full faithfulness of open extension to equate them.
7. For the factor swap, transport both product cones to the original product. Both
   vertical maps restrict to the same signed symmetry, so the same faithfulness
   argument proves the displayed square, including its Koszul sign.
8. Form `tripleLeft` and `tripleRight` on the same triple cones. Their associators
   and projection comparisons restrict to the same pure-tensor associator. Every
   binary comparison restricts to the identity, so both restrict via
   `tripleRestriction` to the identity. Full faithfulness gives their equality.
   Naturality follows from naturality of each factor in the binary construction.
-/
theorem finite_open_external_tensor_normalization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorDatum D C E n hn)
    {B X₀ Y₀ Xb₀ Yb₀ : SixFunctorSpace D}
    [IsSeparated B.obj.hom] [IsSeparated X₀.obj.hom] [IsSeparated Y₀.obj.hom]
    [IsSeparated Xb₀.obj.hom] [IsSeparated Yb₀.obj.hom]
    (j₀ : X₀ ⟶ Xb₀) (k₀ : Y₀ ⟶ Yb₀)
    [IsOpenImmersion j₀.hom.left] [IsOpenImmersion k₀.hom.left]
    (f : Xb₀ ⟶ B) (g : Yb₀ ⟶ B)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    {T₀ Tb₀ : Scheme.{u}} (d : Diagram j₀.hom.left k₀.hom.left T₀ Tb₀)
    (_barProduct : IsPullback d.pb d.qb f.hom.left g.hom.left)
    (_product : IsPullback d.p d.q (j₀.hom.left ≫ f.hom.left) (k₀.hom.left ≫ g.hom.left))
    (K : finiteTorConstructibleCategory C.l E n hn X₀.obj.left)
    (L : finiteTorConstructibleCategory C.l E n hn Y₀.obj.left) :
    FiniteAssertion S j₀ k₀ f g d K L := by
  sorry

end AlgebraicGeometry.ProEtale.OpenExternalTensor
