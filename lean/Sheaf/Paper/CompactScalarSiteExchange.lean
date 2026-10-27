/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CompactScalarSiteCompositors

/-! # Open mates of normalized restriction exchanges
Source: Stacks 07A7 and blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-exchange).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.checkUnivs false
universe u v w z
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CompactScalarSite

/-- The inverse-image exchange is fixed on every underlying module section.
Source: Stacks 03D2 and 07A7
(blueprint: def-pur-compact-scalar-site-exchange). -/
def NormalizedExchange {X T Y S : Presentation.{u, v}} {R : Type (max u v)} [CommRing R]
    {p : GeometricMorphism (Sheaf T.J (Type (max u v))) (Sheaf S.J (Type (max u v)))}
    {j : GeometricMorphism (Sheaf X.J (Type (max u v))) (Sheaf T.J (Type (max u v)))}
    {k : GeometricMorphism (Sheaf Y.J (Type (max u v))) (Sheaf S.J (Type (max u v)))}
    {q : GeometricMorphism (Sheaf X.J (Type (max u v))) (Sheaf Y.J (Type (max u v)))}
    (Lp : InverseModel T S R p) (Lj : InverseModel X T R j)
    (Lk : InverseModel Y S R k) (Lq : InverseModel X Y R q)
    (s : p.inverse ⋙ j.inverse ≅ k.inverse ⋙ q.inverse)
    (a : Lp.lift.modules ⋙ Lj.lift.modules ≅ Lk.lift.modules ⋙ Lq.lift.modules) : Prop :=
  ∀ M : modules S R,
    (underlying X R).map (a.hom.app M) ≫
        Lq.lift.moduleUnderlying.hom.app (Lk.lift.modules.obj M) ≫
        q.inverse.map (Lk.lift.moduleUnderlying.hom.app M) =
      Lj.lift.moduleUnderlying.hom.app (Lp.lift.modules.obj M) ≫
        j.inverse.map (Lp.lift.moduleUnderlying.hom.app M) ≫
        s.hom.app ((underlying S R).obj M)

variable {A B : Type (max u v)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The ordinary restriction exchange and its coherent tilde counterpart. The set
cube expresses the specified pullback composition identities; normalization fixes
all four module exchanges before passing to derived categories.
Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-exchange). -/
structure ExchangeIdentification {X T Y S : Vertex.{u, v} φ}
    (j : OpenSquare φ X T) (k : OpenSquare φ Y S)
    (p : DirectLetter φ T S) (q : DirectLetter φ X Y) where
  sets : p.square.p.inverse ⋙ j.square.p.inverse ≅
    k.square.p.inverse ⋙ q.square.p.inverse
  tildeSets : p.square.tildeP.inverse ⋙ j.square.tildeP.inverse ≅
    k.square.tildeP.inverse ⋙ q.square.tildeP.inverse
  cube : (pasteInverseIso p.square.sets j.square.sets).hom ≫
      Functor.whiskerRight sets.hom X.ν.inverse =
    Functor.whiskerLeft S.ν.inverse tildeSets.hom ≫
      (pasteInverseIso k.square.sets q.square.sets).hom
  A : p.square.LA.lift.modules ⋙ j.square.LA.lift.modules ≅
    k.square.LA.lift.modules ⋙ q.square.LA.lift.modules
  B : p.square.LB.lift.modules ⋙ j.square.LB.lift.modules ≅
    k.square.LB.lift.modules ⋙ q.square.LB.lift.modules
  tildeA : p.square.tildeLA.lift.modules ⋙ j.square.tildeLA.lift.modules ≅
    k.square.tildeLA.lift.modules ⋙ q.square.tildeLA.lift.modules
  tildeB : p.square.tildeLB.lift.modules ⋙ j.square.tildeLB.lift.modules ≅
    k.square.tildeLB.lift.modules ⋙ q.square.tildeLB.lift.modules
  normalizedA : NormalizedExchange p.square.LA j.square.LA k.square.LA q.square.LA sets A
  normalizedB : NormalizedExchange p.square.LB j.square.LB k.square.LB q.square.LB sets B
  tildeNormalizedA : NormalizedExchange p.square.tildeLA j.square.tildeLA
    k.square.tildeLA q.square.tildeLA tildeSets tildeA
  tildeNormalizedB : NormalizedExchange p.square.tildeLB j.square.tildeLB
    k.square.tildeLB q.square.tildeLB tildeSets tildeB

/-- A natural candidate for the inverse restriction exchange. Its actual inverse
normalization is required only at the inputs used, by ValidAt below. This retains
inputwise inversion, without strengthening it to a global base-change theorem.
Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-exchange). -/
structure ExchangeInverse {X T Y S : Vertex.{u, v} φ}
    (j : OpenSquare φ X T) (k : OpenSquare φ Y S)
    (p : DirectLetter φ T S) (q : DirectLetter φ X Y) where
  A : inverse j.square.LA ⋙ q.RA.functor ⟶ p.RA.functor ⋙ inverse k.square.LA
  B : inverse j.square.LB ⋙ q.RB.functor ⟶ p.RB.functor ⋙ inverse k.square.LB
  tildeA : inverse j.square.tildeLA ⋙ q.tildeRA.functor ⟶
    p.tildeRA.functor ⋙ inverse k.square.tildeLA
  tildeB : inverse j.square.tildeLB ⋙ q.tildeRB.functor ⟶
    p.tildeRB.functor ⋙ inverse k.square.tildeLB

/-- Being mutually inverse at one object; neither transformation must be globally
invertible. Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-exchange). -/
def InverseAt {C D : Type w} [Category.{z} C]
    [Category.{z} D] {F G : C ⥤ D} (a : F ⟶ G) (b : G ⟶ F) (M : C) : Prop :=
  a.app M ≫ b.app M = 𝟙 _ ∧ b.app M ≫ a.app M = 𝟙 _

/-- Pointwise normalization of all inverse exchanges needed by the two open mates.
Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-exchange). -/
def ExchangeInverse.ValidAt {X T Y S : Vertex.{u, v} φ}
    {j : OpenSquare φ X T} {k : OpenSquare φ Y S}
    {p : DirectLetter φ T S} {q : DirectLetter φ X Y}
    (b : ExchangeInverse φ j k p q) (a : ExchangeIdentification φ j k p q)
    (MA : derived X.W A) (MB : derived X.W B) : Prop :=
  InverseAt (mateEquiv p.RA.adj q.RA.adj (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso a.A).inv)).natTrans b.A (j.IA.functor.obj MA) ∧
  InverseAt (mateEquiv p.RB.adj q.RB.adj (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso a.B).inv)).natTrans b.B (j.IB.functor.obj MB) ∧
  InverseAt (mateEquiv p.tildeRA.adj q.tildeRA.adj (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso a.tildeA).inv)).natTrans b.tildeA
    (j.tildeIA.functor.obj ((inverse X.NA).obj MA)) ∧
  InverseAt (mateEquiv p.tildeRB.adj q.tildeRB.adj (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso a.tildeB).inv)).natTrans b.tildeB
    (j.tildeIB.functor.obj ((inverse X.NB).obj MB))

/-- The actual open-adjunction mate of the inverse exchange. The mate bijections
fix its direction and its unit and counit normalization.
Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-exchange). -/
def exchangeComparison {X T Y S : Vertex.{u, v} φ}
    {j : OpenSquare φ X T} {k : OpenSquare φ Y S}
    {p : DirectLetter φ T S} {q : DirectLetter φ X Y}
    (b : ExchangeInverse φ j k p q) :
    Comparison φ (composeValue φ q.value (openValue φ k))
      (composeValue φ (openValue φ j) p.value) where
  A := ((mateEquiv j.IA.adj k.IA.adj).symm (TwoSquare.mk _ _ _ _ b.A)).natTrans
  B := ((mateEquiv j.IB.adj k.IB.adj).symm (TwoSquare.mk _ _ _ _ b.B)).natTrans
  tildeA := ((mateEquiv j.tildeIA.adj k.tildeIA.adj).symm
    (TwoSquare.mk _ _ _ _ b.tildeA)).natTrans
  tildeB := ((mateEquiv j.tildeIB.adj k.tildeIB.adj).symm
    (TwoSquare.mk _ _ _ _ b.tildeB)).natTrans

/-- Vertical pasting of four transformations.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-exchange). -/
def Comparison.comp {X Y : Vertex.{u, v} φ} {H K L : Value φ X Y}
    (θ : Comparison φ H K) (ψ : Comparison φ K L) : Comparison φ H L where
  A := θ.A ≫ ψ.A
  B := θ.B ≫ ψ.B
  tildeA := θ.tildeA ≫ ψ.tildeA
  tildeB := θ.tildeB ≫ ψ.tildeB

/-- Horizontal pasting, in execution order.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-exchange). -/
def Comparison.horizontal {X Y Z : Vertex.{u, v} φ}
    {H H' : Value φ X Y} {K K' : Value φ Y Z}
    (θ : Comparison φ H H') (ψ : Comparison φ K K') :
    Comparison φ (composeValue φ H K) (composeValue φ H' K') where
  A := Functor.whiskerRight θ.A K.FA ≫ Functor.whiskerLeft H'.FA ψ.A
  B := Functor.whiskerRight θ.B K.FB ≫ Functor.whiskerLeft H'.FB ψ.B
  tildeA := Functor.whiskerRight θ.tildeA K.tildeFA ≫
    Functor.whiskerLeft H'.tildeFA ψ.tildeA
  tildeB := Functor.whiskerRight θ.tildeB K.tildeFB ≫
    Functor.whiskerLeft H'.tildeFB ψ.tildeB

/-- Identity comparison, including the empty-word case.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-exchange). -/
def Comparison.identity {X Y : Vertex.{u, v} φ} (H : Value φ X Y) : Comparison φ H H :=
  ⟨𝟙 _, 𝟙 _, 𝟙 _, 𝟙 _⟩

/-- A reverse comparison is inverse at exactly the four inputs used in the square.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-exchange). -/
def Comparison.InverseAt {X Y : Vertex.{u, v} φ} {H H' : Value φ X Y}
    (θ : Comparison φ H H') (ψ : Comparison φ H' H)
    (MA : derived X.W A) (MB : derived X.W B) : Prop :=
  CategoryTheory.CompactScalarSite.InverseAt θ.A ψ.A MA ∧
    CategoryTheory.CompactScalarSite.InverseAt θ.B ψ.B MB ∧
    CategoryTheory.CompactScalarSite.InverseAt
      θ.tildeA ψ.tildeA ((inverse X.NA).obj MA) ∧
    CategoryTheory.CompactScalarSite.InverseAt
      θ.tildeB ψ.tildeB ((inverse X.NB).obj MB)

/-- Finite pastes of the specified normalized generators, with inputwise inverse
exchanges and inverse comparisons. This is syntax for the actual arrows; no site
or scalar square is a constructor hypothesis.
Source: Stacks 07A7, 0E46, 0E47 and blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-exchange). -/
inductive PasteAt : {X Y : Vertex.{u, v} φ} → {H H' : Value φ X Y} →
    Comparison φ H H' → derived X.W A → derived X.W B → Prop where
  | identity {X Y : Vertex.{u, v} φ} (H : Value φ X Y)
      (MA : derived X.W A) (MB : derived X.W B) :
      PasteAt (Comparison.identity φ H) MA MB
  | direct {X Y Z : Vertex.{u, v} φ}
      (p : DirectLetter φ X Y) (q : DirectLetter φ Y Z) (r : DirectLetter φ X Z)
      (c : CompositionIdentification φ p.square q.square r.square)
      (MA : derived X.W A) (MB : derived X.W B) :
      PasteAt (directCompositor φ p q r c).hom MA MB
  | openExtension {X Y Z : Vertex.{u, v} φ}
      (p : OpenSquare φ X Y) (q : OpenSquare φ Y Z) (r : OpenSquare φ X Z)
      (c : CompositionIdentification φ p.square q.square r.square)
      (MA : derived X.W A) (MB : derived X.W B) :
      PasteAt (openCompositor φ p q r c).hom MA MB
  | exchange {X T Y S : Vertex.{u, v} φ}
      {j : OpenSquare φ X T} {k : OpenSquare φ Y S}
      {p : DirectLetter φ T S} {q : DirectLetter φ X Y}
      (a : ExchangeIdentification φ j k p q) (b : ExchangeInverse φ j k p q)
      (MA : derived X.W A) (MB : derived X.W B)
      (h : b.ValidAt φ a MA MB) : PasteAt (exchangeComparison φ b) MA MB
  | comp {X Y : Vertex.{u, v} φ} {H K L : Value φ X Y}
      {θ : Comparison φ H K} {ψ : Comparison φ K L}
      {MA : derived X.W A} {MB : derived X.W B}
      (hθ : PasteAt θ MA MB) (hψ : PasteAt ψ MA MB) :
      PasteAt (θ.comp φ ψ) MA MB
  | horizontal {X Y Z : Vertex.{u, v} φ}
      {H H' : Value φ X Y} {K K' : Value φ Y Z}
      {θ : Comparison φ H H'} {ψ : Comparison φ K K'}
      {MA : derived X.W A} {MB : derived X.W B}
      (hθ : PasteAt θ MA MB)
      (hψ : PasteAt ψ (H'.FA.obj MA) (H'.FB.obj MB)) :
      PasteAt (θ.horizontal φ ψ) MA MB
  | inverse {X Y : Vertex.{u, v} φ} {H H' : Value φ X Y}
      {θ : Comparison φ H H'} {ψ : Comparison φ H' H}
      {MA : derived X.W A} {MB : derived X.W B}
      (hθ : PasteAt θ MA MB) (hψ : θ.InverseAt φ ψ MA MB) : PasteAt ψ MA MB

end CategoryTheory.CompactScalarSite
