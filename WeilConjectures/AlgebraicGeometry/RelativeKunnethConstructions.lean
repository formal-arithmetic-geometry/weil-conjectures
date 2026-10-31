/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProductFactors
public import WeilConjectures.AlgebraicGeometry.CommonStageCompactWeilCohomology
public import WeilConjectures.AlgebraicGeometry.SupportCohomology
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Constructions for relative compact-support Künneth

Source: current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
the six-factor relative map and its closed-subscheme specialization
(blueprint: def-sf-relative-kunneth-constructions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

/-- Compose the six specified factors, in their displayed order. Every component
retains the normalization to A2--A4 and to signed tensor symmetry imposed by R.
Source: displayed relative map (blueprint: def-sf-relative-kunneth-constructions). -/
def relativeKunnethIso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :=
  R.factors cg ch 0 ≪≫ R.factors cg ch 1 ≪≫ R.factors cg ch 2 ≪≫
    R.factors cg ch 3 ≪≫ R.factors cg ch 4 ≪≫ R.factors cg ch 5

/-- The canonical relative map, with the source-to-target direction in the paper.
Source: displayed relative map (blueprint: def-sf-relative-kunneth-constructions). -/
def relativeKunnethMap
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left) :=
  (relativeKunnethIso R cg ch).hom


/-- Canonical pullback composition around a commutative square, with the supplied
A4 pullback compositors. Source: base-change clause
(blueprint: def-sf-relative-kunneth-constructions). -/
def relativeKunnethPullSquare
    {D : FiniteFieldDatum.{u}} {A : SixFunctorSpace D → Type v}
    [∀ X, Category.{w} (A X)] (O : SixFunctorPushStage D A)
    {V W X Y : SixFunctorSpace D} (a : V ⟶ W) (b : W ⟶ Y)
    (c : V ⟶ X) (d : X ⟶ Y) (h : a ≫ b = c ≫ d) :=
  (O.pullComposition a b).symm ≪≫ eqToIso (congrArg (fun f ↦ O.pull f) h) ≪≫
    O.pullComposition c d

/-- The finite tensor-pullback comparison after the prescribed tensor model and
pullback comparisons. Source: canonical monoidal pullback in the base-change
clause (blueprint: def-sf-relative-kunneth-constructions). -/
def relativeKunnethFiniteTensorComparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {Q Q' : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    [IsSeparated Q'.g.hom.left] [IsSeparated Q'.g'.hom.left] [IsSeparated Q'.f'.hom.left]
    (R : RelativeProductPresentation S .finite Q)
    (R' : RelativeProductPresentation S .finite Q')
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left)
    (K L : (S.finiteTorDomain Y).FullSubcategory) :
    ((S.finite.pull f).obj ((R.coordinates.tensor Y).obj (K, L)).obj).obj ≅
      (((R'.coordinates.tensor X).obj
        ((R'.coordinates.operations.pull f hf).obj K,
         (R'.coordinates.operations.pull f hf).obj L)).obj).obj := by
  cases n with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 hn)
  | succ j =>
    letI := Padic.finite_coefficientExtensionRing C.l E (j + 1) hn
    letI : (sfIntrinsicPullback (Padic.coefficientExtensionRing C.l E (j + 1))
        f.hom.left).Additive :=
      sfIntrinsicPullback_additive (Padic.coefficientExtensionRing C.l E (j + 1)) f.hom.left
    letI := sfIntrinsicPullback_preservesFiniteLimits
      (Padic.coefficientExtensionRing C.l E (j + 1)) f.hom.left
    letI := sfIntrinsicPullback_preservesFiniteColimits
      (Padic.coefficientExtensionRing C.l E (j + 1)) f.hom.left
    let e := Functor.mapDerivedCategoryNatIso
      (pullbackTensorFiniteRealization C.l E f.hom.left j)
    let k := (R'.coordinates.operations.pull f hf).obj K
    let l := (R'.coordinates.operations.pull f hf).obj L
    have hk : k.obj = (S.finite.pull f).obj K.obj := by
      exact congrArg (fun F ↦ F.obj K) (R'.coordinates.pullNormalization f hf)
    have hl : l.obj = (S.finite.pull f).obj L.obj := by
      exact congrArg (fun F ↦ F.obj L) (R'.coordinates.pullNormalization f hf)
    exact (S.finitePullback f).app ((R.coordinates.tensor Y).obj (K, L)).obj ≪≫
      (sixFunctorFinitePullback D C E (j + 1) hn f).mapIso
        (relativeProductFiniteTensorIso R Y K L) ≪≫
      (e.app ((S.finiteModel Y).closed.tensor.obj (K.obj.obj, L.obj.obj))).symm ≪≫
      (Scheme.proEtaleCanonicalTensorComparison f.hom.left
        (Scheme.proEtaleConstantRing Y.obj.left (Padic.coefficientExtensionRing C.l E (j + 1)))
        (Scheme.proEtaleConstantRing X.obj.left (Padic.coefficientExtensionRing C.l E (j + 1)))
        (Scheme.proEtaleConstantRingComparison f.hom.left
          (Padic.coefficientExtensionRing C.l E (j + 1)))
        (relativeProductFiniteTensorModel S Y) (relativeProductFiniteTensorModel S X)).app
          (K.obj.obj, L.obj.obj) ≪≫
      (S.finiteModel X).closed.tensor.mapIso
        (((e.app K.obj.obj ≪≫ ((S.finitePullback f).app K.obj).symm ≪≫
          eqToIso (congrArg (fun Z ↦ Z.obj) hk.symm))).prod
          (e.app L.obj.obj ≪≫ ((S.finitePullback f).app L.obj).symm ≪≫
            eqToIso (congrArg (fun Z ↦ Z.obj) hl.symm))) ≪≫
      (relativeProductFiniteTensorIso R' X k l).symm

/-- Pin monoidal pullback to its canonical coefficient-model comparison; finite
coefficients include the specified model transports, rather than an equality
between unrelated tensor presentations. Source: Stacks 07A4 and the base-change
clause (blueprint: def-sf-relative-kunneth-constructions). -/
def relativeKunnethTensorNormalized
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q Q' : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    [IsSeparated Q'.g.hom.left] [IsSeparated Q'.g'.hom.left] [IsSeparated Q'.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (R' : RelativeProductPresentation S s Q')
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)]
    (K L : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Y).FullSubcategory)
    (a : R.coordinates.tensor Y ⋙ R'.coordinates.operations.pull f hf ≅
      ((R'.coordinates.operations.pull f hf).prod
        (R'.coordinates.operations.pull f hf)) ⋙ R'.coordinates.tensor X) : Prop := by
  cases s with
  | finite =>
      exact HEq (((S.finiteTorDomain X).ι ⋙
        (intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).ι).map
          (a.hom.app (K, L)))
        (relativeKunnethFiniteTensorComparison R R' f hf K L).hom
  | integral =>
      exact HEq ((S.integralFiniteTorDomain X).ι.map (a.hom.app (K, L)))
        ((canonicalIntegralPullbackTensor C.l E f.hom.left K.obj L.obj).hom)
  | rational =>
      exact HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum .rational X).ι.map
        (a.hom.app (K, L)))
        ((canonicalRationalPullbackTensor C.l E f.hom.left K.obj L.obj).hom)
  | common =>
      exact HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum .common X).ι.map
        (a.hom.app (K, L)))
        ((canonicalCommonStagePullbackTensor C.l C.Qbar f.hom.left K.obj L.obj).hom)

/-- A geometric base-change cube. The three compactified squares are the actual
squares for f, g and h; their corner, arrow and compactification equalities pin
the supplied exchange maps. No equation for the relative product is a field.
Source: base-change clause (blueprint: def-sf-relative-kunneth-constructions). -/
structure RelativeKunnethCube
    {D : FiniteFieldDatum.{u}} (Q Q' : SixFunctorCompactifiedSquare D)
    (cg : Compactification Q.g.hom.left)
    (ch : Compactification (Q.f' ≫ Q.g).hom.left)
    (cg' : Compactification Q'.g.hom.left)
    (ch' : Compactification (Q'.f' ≫ Q'.g).hom.left) where
  b : Q'.Y ⟶ Q.Y
  x : Q'.X ⟶ Q.X
  y : Q'.Y' ⟶ Q.Y'
  t : Q'.X' ⟶ Q.X'
  separated_b : IsSeparated b.hom.left
  separated_x : IsSeparated x.hom.left
  separated_y : IsSeparated y.hom.left
  separated_t : IsSeparated t.hom.left
  separated_base : IsSeparated Q'.Y.obj.hom
  leftComm : t ≫ Q.g' = Q'.g' ≫ x
  rightComm : t ≫ Q.f' = Q'.f' ≫ y
  fSquare : IsPullback x.hom.left Q'.f.hom.left Q.f.hom.left b.hom.left
  gSquare : IsPullback y.hom.left Q'.g.hom.left Q.g.hom.left b.hom.left
  hSquare : IsPullback t.hom.left (Q'.f' ≫ Q'.g).hom.left
    (Q.f' ≫ Q.g).hom.left b.hom.left
  squares : Fin 3 → SixFunctorCompactifiedSquare D
  sourceCorners : (squares 0).X = Q.X ∧ (squares 1).X = Q.Y' ∧
    (squares 2).X = Q.X'
  targetCorners : ∀ i, (squares i).Y = Q.Y ∧ (squares i).Y' = Q'.Y
  changedCorners : (squares 0).X' = Q'.X ∧ (squares 1).X' = Q'.Y' ∧
    (squares 2).X' = Q'.X'
  verticals : HEq (squares 0).f Q.f ∧ HEq (squares 1).f Q.g ∧
    HEq (squares 2).f (Q.f' ≫ Q.g)
  changedVerticals : HEq (squares 0).f' Q'.f ∧ HEq (squares 1).f' Q'.g ∧
    HEq (squares 2).f' (Q'.f' ≫ Q'.g)
  horizontals : ∀ i, HEq (squares i).g b
  upperHorizontals : HEq (squares 0).g' x ∧ HEq (squares 1).g' y ∧
    HEq (squares 2).g' t
  compactifications : HEq (squares 0).compactification Q.compactification ∧
    HEq (squares 1).compactification cg ∧ HEq (squares 2).compactification ch
  changedCompactifications : HEq (squares 0).compactification' Q'.compactification ∧
    HEq (squares 1).compactification' cg' ∧ HEq (squares 2).compactification' ch'

/-- Primitive comparisons of a geometric cube, all normalized to the original
datum and canonical tensor-pullback maps. In particular, exchange_h is the actual
exchange for h, not a chosen comparison of the final product endpoints.
Source: base-change clause (blueprint: def-sf-relative-kunneth-constructions). -/
structure RelativeKunnethCubeComparisons
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q Q' : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    [IsSeparated Q'.g.hom.left] [IsSeparated Q'.g'.hom.left] [IsSeparated Q'.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (R' : RelativeProductPresentation S s Q')
    {cg ch cg' ch'} (G : RelativeKunnethCube Q Q' cg ch cg' ch') where
  /-- Canonical tensor pullback on every separated map, after full inclusion. -/
  tensor : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (hf : IsSeparated f.hom.left),
    R.coordinates.tensor Y ⋙ R'.coordinates.operations.pull f hf ≅
      ((R'.coordinates.operations.pull f hf).prod
        (R'.coordinates.operations.pull f hf)) ⋙ R'.coordinates.tensor X
  tensorNormalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (hf : IsSeparated f.hom.left)
    [∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
    [∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] K L,
    relativeKunnethTensorNormalized R R' f hf K L (tensor f hf)
  leftComposition : ∀ K,
    (R'.coordinates.operations.pull G.t G.separated_t).obj
        ((R.coordinates.operations.pull Q.g' inferInstance).obj K) ≅
      (R'.coordinates.operations.pull Q'.g' inferInstance).obj
        ((R'.coordinates.operations.pull G.x G.separated_x).obj K)
  rightComposition : ∀ L,
    (R'.coordinates.operations.pull G.t G.separated_t).obj
        ((R.coordinates.operations.pull Q.f' inferInstance).obj L) ≅
      (R'.coordinates.operations.pull Q'.f' inferInstance).obj
        ((R'.coordinates.operations.pull G.y G.separated_y).obj L)
  leftCompositionNormalization : ∀ K,
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q'.X').ι.map
      (leftComposition K).hom)
      ((relativeKunnethPullSquare (PodCoefficientStage.operations S.toSixFunctorOperationDatum s)
        G.t Q.g' Q'.g' G.x G.leftComm).hom.app K.obj)
  rightCompositionNormalization : ∀ L,
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q'.X').ι.map
      (rightComposition L).hom)
      ((relativeKunnethPullSquare (PodCoefficientStage.operations S.toSixFunctorOperationDatum s)
        G.t Q.f' Q'.f' G.y G.rightComm).hom.app L.obj)
  exchange_f : ∀ K,
    (R'.coordinates.operations.pull G.b G.separated_b).obj
        ((R.coordinates.operations.support Q.f Q.compactification).obj K) ≅
      (R'.coordinates.operations.support Q'.f Q'.compactification).obj
        ((R'.coordinates.operations.pull G.x G.separated_x).obj K)
  exchange_g : ∀ L,
    (R'.coordinates.operations.pull G.b G.separated_b).obj
        ((R.coordinates.operations.support Q.g cg).obj L) ≅
      (R'.coordinates.operations.support Q'.g cg').obj
        ((R'.coordinates.operations.pull G.y G.separated_y).obj L)
  exchange_h : ∀ H,
    (R'.coordinates.operations.pull G.b G.separated_b).obj
        ((R.coordinates.operations.support (Q.f' ≫ Q.g) ch).obj H) ≅
      (R'.coordinates.operations.support (Q'.f' ≫ Q'.g) ch').obj
        ((R'.coordinates.operations.pull G.t G.separated_t).obj H)
  exchange_f_normalization : ∀ K M, HEq K.obj M.obj →
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q'.Y).ι.map
      (exchange_f K).hom) (relativeProductExchange S s (G.squares 0) M).hom
  exchange_g_normalization : ∀ L M, HEq L.obj M.obj →
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q'.Y).ι.map
      (exchange_g L).hom) (relativeProductExchange S s (G.squares 1) M).hom
  exchange_h_normalization : ∀ H M, HEq H.obj M.obj →
    HEq ((PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q'.Y).ι.map
      (exchange_h H).hom) (relativeProductExchange S s (G.squares 2) M).hom

namespace RelativeKunnethCubeComparisons
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
  {Q Q' : SixFunctorCompactifiedSquare D}
  [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
  [IsSeparated Q'.g.hom.left] [IsSeparated Q'.g'.hom.left] [IsSeparated Q'.f'.hom.left]
  {R : RelativeProductPresentation S s Q} {R' : RelativeProductPresentation S s Q'}
  {cg ch cg' ch'} {G : RelativeKunnethCube Q Q' cg ch cg' ch'}
  (A : RelativeKunnethCubeComparisons R R' G)

/-- Pullback of the external tensor, with ordinary pullback of both inputs.
Source: base-change input comparison (blueprint: def-sf-relative-kunneth-constructions). -/
def externalIso (K L) :=
  (A.tensor G.t G.separated_t).app
      ((R.coordinates.operations.pull Q.g' inferInstance).obj K,
        (R.coordinates.operations.pull Q.f' inferInstance).obj L) ≪≫
    (R'.coordinates.tensor Q'.X').mapIso
      ((A.leftComposition K).prod (A.rightComposition L))

/-- The source vertical comparison: exchange for h followed by pullback of the
external tensor. Source: base-change square (blueprint: def-sf-relative-kunneth-constructions). -/
def sourceIso (K L) :=
  A.exchange_h ((R.coordinates.tensor Q.X').obj
      ((R.coordinates.operations.pull Q.g' inferInstance).obj K,
        (R.coordinates.operations.pull Q.f' inferInstance).obj L)) ≪≫
    (R'.coordinates.operations.support (Q'.f' ≫ Q'.g) ch').mapIso (A.externalIso K L)

/-- The target vertical comparison: canonical monoidal pullback, then exchange
for f and g in that order. Source: base-change square
(blueprint: def-sf-relative-kunneth-constructions). -/
def targetIso (K L) :=
  (A.tensor G.b G.separated_b).app
      ((R.coordinates.operations.support Q.f Q.compactification).obj K,
        (R.coordinates.operations.support Q.g cg).obj L) ≪≫
    (R'.coordinates.tensor Q'.Y).mapIso ((A.exchange_f K).prod (A.exchange_g L))
end RelativeKunnethCubeComparisons


/-- A closed-subscheme specialization of a square over the geometric point.
The maps i and j are ordinary closed immersions, and r is their product, pinned
by both projection equations. Source: final display
(blueprint: def-sf-relative-kunneth-constructions). -/
structure RelativeKunnethClosedSquare
    {D : FiniteFieldDatum.{u}} (Q Q' : SixFunctorCompactifiedSquare D) where
  base : Q.Y = sixFunctorPoint D
  base' : Q'.Y = sixFunctorPoint D
  i : Q'.X ⟶ Q.X
  j : Q'.Y' ⟶ Q.Y'
  r : Q'.X' ⟶ Q.X'
  closed_i : IsClosedImmersion i.hom.left
  closed_j : IsClosedImmersion j.hom.left
  closed_r : IsClosedImmersion r.hom.left
  leftComm : r ≫ Q.g' = Q'.g' ≫ i
  rightComm : r ≫ Q.f' = Q'.f' ≫ j
  sepZ : IsSeparated Q'.X.obj.hom
  sepW : IsSeparated Q'.Y'.obj.hom
  sepProduct : IsSeparated Q'.X'.obj.hom

/-- Ordinary restriction to the two closed subschemes and their product, retaining
the actual pullback functors supplied by the datum. Source: final display
(blueprint: def-sf-relative-kunneth-constructions). -/
def relativeKunnethClosedFormula
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    {S : SixFunctorDatum D C E n hn} {s : PodCoefficientStage}
    {Q Q' : SixFunctorCompactifiedSquare D}
    [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left] [IsSeparated Q.f'.hom.left]
    (R : RelativeProductPresentation S s Q) (J : RelativeKunnethClosedSquare Q Q') : Prop := by
  letI := J.closed_i
  letI := J.closed_j
  letI := J.closed_r
  letI := J.sepZ
  letI := J.sepW
  letI := J.sepProduct
  letI : Q'.X.obj.left.Over (Spec (.of D.k)) := ⟨Q'.X.obj.hom⟩
  letI : Q'.Y'.obj.left.Over (Spec (.of D.k)) := ⟨Q'.Y'.obj.hom⟩
  letI : Q'.X'.obj.left.Over (Spec (.of D.k)) := ⟨Q'.X'.obj.hom⟩
  letI : LocallyOfFiniteType (Q'.X.obj.left ↘ Spec (.of D.k)) := Q'.X.property.1
  letI : LocallyOfFiniteType (Q'.Y'.obj.left ↘ Spec (.of D.k)) := Q'.Y'.property.1
  letI : LocallyOfFiniteType (Q'.X'.obj.left ↘ Spec (.of D.k)) := Q'.X'.property.1
  letI : QuasiCompact (Q'.X.obj.left ↘ Spec (.of D.k)) := Q'.X.property.2
  letI : QuasiCompact (Q'.Y'.obj.left ↘ Spec (.of D.k)) := Q'.Y'.property.2
  letI : QuasiCompact (Q'.X'.obj.left ↘ Spec (.of D.k)) := Q'.X'.property.2
  letI : IsSeparated (Q'.X.obj.left ↘ Spec (.of D.k)) := J.sepZ
  letI : IsSeparated (Q'.Y'.obj.left ↘ Spec (.of D.k)) := J.sepW
  letI : IsSeparated (Q'.X'.obj.left ↘ Spec (.of D.k)) := J.sepProduct
  let inputs := fun
    (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q.X).FullSubcategory)
    (L : (PodCoefficientStage.domain S.toSixFunctorOperationDatum s Q.Y').FullSubcategory) ↦
      (((R.coordinates.operations.pull J.i inferInstance).obj K).obj,
       ((R.coordinates.operations.pull J.j inferInstance).obj L).obj,
       ((R.coordinates.operations.pull J.r inferInstance).obj
         ((R.coordinates.tensor Q.X').obj
           ((R.coordinates.operations.pull Q.g' inferInstance).obj K,
            (R.coordinates.operations.pull Q.f' inferInstance).obj L))).obj)
  cases s with
  | finite =>
      exact ∀ (cz : Compactification Q'.X.obj.hom)
        (cw : Compactification Q'.Y'.obj.hom) (ct : Compactification Q'.X'.obj.hom)
        (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum .finite Q.X).FullSubcategory)
        (L :
          (PodCoefficientStage.domain S.toSixFunctorOperationDatum .finite Q.Y').FullSubcategory),
        Nonempty ((finiteCompactSections D C.l E Q'.X.obj.left cz n hn ((inputs K L).1).obj) ⊗
          (finiteCompactSections D C.l E Q'.Y'.obj.left cw n hn ((inputs K L).2.1).obj) ≅
          finiteCompactSections D C.l E Q'.X'.obj.left ct n hn ((inputs K L).2.2).obj)
  | integral =>
      exact ∀ (cz : Compactification Q'.X.obj.hom)
        (cw : Compactification Q'.Y'.obj.hom) (ct : Compactification Q'.X'.obj.hom)
        (K :
          (PodCoefficientStage.domain S.toSixFunctorOperationDatum .integral Q.X).FullSubcategory)
        (L :
          (PodCoefficientStage.domain S.toSixFunctorOperationDatum .integral Q.Y').FullSubcategory),
        Nonempty ((
          (integralCompactSections D C.l C.different E Q'.X.obj.left cz ((inputs K L).1)).obj) ⊗
          ((integralCompactSections D C.l C.different E Q'.Y'.obj.left cw ((inputs K L).2.1)).obj) ≅
          (integralCompactSections D C.l C.different E Q'.X'.obj.left ct ((inputs K L).2.2)).obj)
  | rational =>
      exact ∀ (cz : Compactification Q'.X.obj.hom)
        (cw : Compactification Q'.Y'.obj.hom) (ct : Compactification Q'.X'.obj.hom)
        (K :
          (PodCoefficientStage.domain S.toSixFunctorOperationDatum .rational Q.X).FullSubcategory)
        (L :
          (PodCoefficientStage.domain S.toSixFunctorOperationDatum .rational Q.Y').FullSubcategory),
        Nonempty ((
          (rationalCompactSections D C.l C.different E Q'.X.obj.left cz ((inputs K L).1)).obj) ⊗
          ((rationalCompactSections D C.l C.different E Q'.Y'.obj.left cw ((inputs K L).2.1)).obj) ≅
          (rationalCompactSections D C.l C.different E Q'.X'.obj.left ct ((inputs K L).2.2)).obj)
  | common =>
      exact ∀ (cz : Compactification Q'.X.obj.hom)
        (cw : Compactification Q'.Y'.obj.hom) (ct : Compactification Q'.X'.obj.hom)
        (K : (PodCoefficientStage.domain S.toSixFunctorOperationDatum .common Q.X).FullSubcategory)
        (L :
          (PodCoefficientStage.domain S.toSixFunctorOperationDatum .common Q.Y').FullSubcategory),
        Nonempty (((DerivedCategory.pointFdQbarRealization C.l C.Qbar).obj
            (qbarCompactSections D C.l C.different Q'.X.obj.left C.Qbar cz ((inputs K L).1))) ⊗
          ((DerivedCategory.pointFdQbarRealization C.l C.Qbar).obj
            (qbarCompactSections D C.l C.different Q'.Y'.obj.left C.Qbar cw ((inputs K L).2.1))) ≅
          (DerivedCategory.pointFdQbarRealization C.l C.Qbar).obj
            (qbarCompactSections D C.l C.different Q'.X'.obj.left C.Qbar ct ((inputs K L).2.2)))

end WeilConjectures
