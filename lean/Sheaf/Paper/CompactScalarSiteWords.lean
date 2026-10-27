/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CompactScalarSiteDiagram

/-! # Words of normalized direct images and open extensions
Source: blueprint main-20261015, sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option linter.checkUnivs false

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CompactScalarSite
variable {A B : Type (max u v)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The value of a word, retaining its actual coefficient and site arrows.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
structure Value (X Y : Vertex.{u, v} φ) where
  FA : derived X.W A ⥤ derived Y.W A
  FB : derived X.W B ⥤ derived Y.W B
  tildeFA : derived X.tildeW A ⥤ derived Y.tildeW A
  tildeFB : derived X.tildeW B ⥤ derived Y.tildeW B
  c : FA ⋙ Y.scalar.model.T ⟶ X.scalar.model.T ⋙ FB
  tildeC : tildeFA ⋙ Y.tildeScalar.model.T ⟶ X.tildeScalar.model.T ⋙ tildeFB
  siteA : FA ⋙ inverse Y.NA ⟶ inverse X.NA ⋙ tildeFA
  siteB : FB ⋙ inverse Y.NB ⟶ inverse X.NB ⋙ tildeFB

/-- Empty-word value; its four comparisons are the canonical unitors.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def identityValue (X : Vertex.{u, v} φ) : Value φ X X where
  FA := 𝟭 _
  FB := 𝟭 _
  tildeFA := 𝟭 _
  tildeFB := 𝟭 _
  c := (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv
  tildeC := (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv
  siteA := (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv
  siteB := (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv

/-- Direct-image letter, with counit-normalized maps chi and d.
Source: Stacks 07A7 (blueprint: def-pur-compact-scalar-site-words). -/
def directValue {X Y : Vertex.{u, v} φ} (p : InverseSquare φ X Y)
    (RA : DirectModel p.LA) (RB : DirectModel p.LB)
    (tildeRA : DirectModel p.tildeLA) (tildeRB : DirectModel p.tildeLB) : Value φ X Y where
  FA := RA.functor
  FB := RB.functor
  tildeFA := tildeRA.functor
  tildeFB := tildeRB.functor
  c := directScalar φ p.scalar RA RB
  tildeC := directScalar φ p.tildeScalar tildeRA tildeRB
  siteA := directSiteA φ p RA tildeRA
  siteB := directSiteB φ p RB tildeRB

/-- Open-extension letter, with unit-normalized maps beta and e.
Source: Stacks 0E8I and 0GL1 (blueprint: def-pur-compact-scalar-site-words). -/
def openValue {X Y : Vertex.{u, v} φ} (j : OpenSquare φ X Y) : Value φ X Y where
  FA := j.IA.functor
  FB := j.IB.functor
  tildeFA := j.tildeIA.functor
  tildeFB := j.tildeIB.functor
  c := j.beta.hom
  tildeC := j.tildeBeta.hom
  siteA := j.eA.hom
  siteB := j.eB.hom

/-- Concatenation; every comparison is the paste of the two specified comparisons.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def composeValue {X Y Z : Vertex.{u, v} φ} (K : Value φ X Y) (G : Value φ Y Z) :
    Value φ X Z where
  FA := K.FA ⋙ G.FA
  FB := K.FB ⋙ G.FB
  tildeFA := K.tildeFA ⋙ G.tildeFA
  tildeFB := K.tildeFB ⋙ G.tildeFB
  c := (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft K.FA G.c ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight K.c G.FB ≫
    (Functor.associator _ _ _).hom
  tildeC := (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft K.tildeFA G.tildeC ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight K.tildeC G.tildeFB ≫
    (Functor.associator _ _ _).hom
  siteA := (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft K.FA G.siteA ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight K.siteA G.tildeFA ≫
    (Functor.associator _ _ _).hom
  siteB := (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft K.FB G.siteB ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight K.siteB G.tildeFB ≫
    (Functor.associator _ _ _).hom

/-- Finite parenthesized words in direct images and open extensions. All objects,
coefficients, adjunctions and site comparisons are retained by the letters.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
inductive Word : Vertex.{u, v} φ → Vertex.{u, v} φ → Type (max u v + 2) where
  | identity (X : Vertex.{u, v} φ) : Word X X
  | direct {X Y : Vertex.{u, v} φ} (p : InverseSquare φ X Y)
      (RA : DirectModel p.LA) (RB : DirectModel p.LB)
      (tildeRA : DirectModel p.tildeLA) (tildeRB : DirectModel p.tildeLB) : Word X Y
  | openExtension {X Y : Vertex.{u, v} φ} (j : OpenSquare φ X Y) : Word X Y
  | compose {X Y Z : Vertex.{u, v} φ} (K : Word X Y) (G : Word Y Z) : Word X Z

/-- Evaluate a finite word by the displayed constituent pastes.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def Word.value {X Y : Vertex.{u, v} φ} : Word φ X Y → Value φ X Y
  | .identity X => identityValue φ X
  | .direct p RA RB tildeRA tildeRB => directValue φ p RA RB tildeRA tildeRB
  | .openExtension j => openValue φ j
  | .compose K G => composeValue φ (K.value) (G.value)

/-- Pointwise invertibility at precisely the intermediate inputs of a word.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def Word.SiteInvertibleAt {X Y : Vertex.{u, v} φ} (H : Word φ X Y)
    (MA : derived X.W A) (MB : derived X.W B) : Prop :=
  match H with
  | .identity _ => True
  | .direct p RA RB tildeRA tildeRB =>
    IsIso ((directSiteA φ p RA tildeRA).app MA) ∧
      IsIso ((directSiteB φ p RB tildeRB).app MB)
  | .openExtension _ => True
  | .compose K G => K.SiteInvertibleAt MA MB ∧
    G.SiteInvertibleAt (K.value.FA.obj MA) (K.value.FB.obj MB)

/-- Four actual transformations between the values of two words.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
structure Comparison {X Y : Vertex.{u, v} φ} (H H' : Value φ X Y) where
  A : H.FA ⟶ H'.FA
  B : H.FB ⟶ H'.FB
  tildeA : H.tildeFA ⟶ H'.tildeFA
  tildeB : H.tildeFB ⟶ H'.tildeFB

/-- The normalized site square in each coefficient, at a specified input.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def Comparison.SiteAt {X Y : Vertex.{u, v} φ} {H H' : Value φ X Y}
    (θ : Comparison φ H H') (MA : derived X.W A) (MB : derived X.W B) : Prop :=
  (inverse Y.NA).map (θ.A.app MA) ≫ H'.siteA.app MA =
    H.siteA.app MA ≫ θ.tildeA.app ((inverse X.NA).obj MA) ∧
  (inverse Y.NB).map (θ.B.app MB) ≫ H'.siteB.app MB =
    H.siteB.app MB ≫ θ.tildeB.app ((inverse X.NB).obj MB)

/-- The scalar square on the untilde system, at a specified input.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def Comparison.ScalarAt {X Y : Vertex.{u, v} φ} {H H' : Value φ X Y}
    (θ : Comparison φ H H') (M : derived X.W A) : Prop :=
  Y.scalar.model.T.map (θ.A.app M) ≫ H'.c.app M =
    H.c.app M ≫ θ.B.app (X.scalar.model.T.obj M)

/-- The scalar square on the tilde system, at an arbitrary tilde input.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def Comparison.TildeScalarAt {X Y : Vertex.{u, v} φ} {H H' : Value φ X Y}
    (θ : Comparison φ H H') (K : derived X.tildeW A) : Prop :=
  Y.tildeScalar.model.T.map (θ.tildeA.app K) ≫ H'.tildeC.app K =
    H.tildeC.app K ≫ θ.tildeB.app (X.tildeScalar.model.T.obj K)

/-- The mixed square for a word. All arrows are its evaluated constituent pastes.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-words). -/
def Value.MixedAt {X Y : Vertex.{u, v} φ} (H : Value φ X Y)
    (M : derived X.W A) : Prop :=
  Y.tildeScalar.model.T.map (H.siteA.app M) ≫
      H.tildeC.app ((inverse X.NA).obj M) ≫
      H.tildeFB.map (X.scalarPullback.comparison.inv.app M) =
    Y.scalarPullback.comparison.inv.app (H.FA.obj M) ≫
      (inverse Y.NB).map (H.c.app M) ≫ H.siteB.app (X.scalar.model.T.obj M)

end CategoryTheory.CompactScalarSite
