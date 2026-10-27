/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering

/-! # Typed functor expressions and their prescribed comparisons

Source: blueprint main-20261015, fix-prop-coherence.proof.md, coefficient comparisons
and inherited equations, as expanded in lem-sf-expression-contextual-intertwining
(blueprint: def-sf-finite-functor-expressions).
-/

@[expose] public section
set_option autoImplicit false
universe s j w u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.FiniteFunctorExpressions

variable {S : Type s} (C : S → Type u₁) (D : S → Type u₂)
  [∀ a, Category.{v₁} (C a)] [∀ a, Category.{v₂} (D a)]

/-- Typed operation symbols with independently specified barred functors and comparisons.
Source: fix-prop-coherence, coefficient-comparison sentence, expanded in the contextual lemma
(blueprint: def-sf-finite-functor-expressions). -/
structure Operations (E : ∀ a, C a ≌ D a) where
  Unary : S → S → Type w
  Binary : S → S → S → Type w
  A : ∀ {a b}, Unary a b → D a ⥤ D b
  barA : ∀ {a b}, Unary a b → C a ⥤ C b
  B : ∀ {a b c}, Binary a b c → D a × D b ⥤ D c
  barB : ∀ {a b c}, Binary a b c → C a × C b ⥤ C c
  dA : ∀ {a b} (f : Unary a b),
    (E a).functor ⋙ A f ⋙ (E b).inverse ≅ barA f
  dB : ∀ {a b c} (f : Binary a b c),
    ((E a).functor.prod (E b).functor) ⋙ B f ⋙ (E c).inverse ≅ barB f

variable {C D} {E : ∀ a, C a ≌ D a} (O : Operations.{s, w, u₁, u₂, v₁, v₂} C D E)
  {J : Type j} (loc : J → S)

/-- Finite parenthesized expressions; repeated inputs and arbitrary symbol sets are allowed.
Source: fix-prop-coherence, finite-expression induction
(blueprint: def-sf-finite-functor-expressions). -/
inductive Expression : S → Type (max s j w) where
  | input (i : J) : Expression (loc i)
  | unary {a b : S} (f : O.Unary a b) (V : Expression a) : Expression b
  | binary {a b c : S} (f : O.Binary a b c) (V : Expression a) (T : Expression b) :
      Expression c

/-- Evaluation as a functor on the entire family of D-inputs, retaining parentheses.
Source: contextual lemma, definition of M_V (blueprint: def-sf-finite-functor-expressions). -/
def Expression.evalD {a : S} : Expression O loc a → ((∀ i, D (loc i)) ⥤ D a)
  | .input i => Pi.eval _ i
  | .unary f V => V.evalD ⋙ O.A f
  | .binary f V T => (V.evalD.prod' T.evalD) ⋙ O.B f

/-- Independently barred evaluation on C-inputs.
Source: contextual lemma, barred evaluation (blueprint: def-sf-finite-functor-expressions). -/
def Expression.evalC {a : S} : Expression O loc a → ((∀ i, C (loc i)) ⥤ C a)
  | .input i => Pi.eval _ i
  | .unary f V => V.evalC ⋙ O.barA f
  | .binary f V T => (V.evalC.prod' T.evalC) ⋙ O.barB f

/-- Reduction of input families by the specified equivalence functors.
Source: contextual lemma, RK_i (blueprint: def-sf-finite-functor-expressions). -/
def reducedInputs : (∀ i, C (loc i)) ⥤ ∀ i, D (loc i) :=
  Functor.pi (fun i => (E (loc i)).functor)

/-- The unary comparison a_A(M) = d_A(LM) (LA(e_M))⁻¹.
Source: contextual lemma, displayed a_A (blueprint: def-sf-finite-functor-expressions). -/
def Operations.unaryComparison {a b : S} (f : O.Unary a b) (M : D a) :
    (E b).inverse.obj ((O.A f).obj M) ≅ (O.barA f).obj ((E a).inverse.obj M) :=
  ((O.A f ⋙ (E b).inverse).mapIso ((E a).counitIso.app M)).symm ≪≫
    (O.dA f).app ((E a).inverse.obj M)

/-- The binary comparison a_B(M,N), with both specified counits.
Source: contextual lemma, displayed a_B (blueprint: def-sf-finite-functor-expressions). -/
def Operations.binaryComparison {a b c : S} (f : O.Binary a b c) (M : D a) (N : D b) :
    (E c).inverse.obj ((O.B f).obj (M, N)) ≅
      (O.barB f).obj ((E a).inverse.obj M, (E b).inverse.obj N) :=
  ((O.B f ⋙ (E c).inverse).mapIso
    (((E a).counitIso.app M).prod ((E b).counitIso.app N))).symm ≪≫
      (O.dB f).app ((E a).inverse.obj M, (E b).inverse.obj N)

/-- The prescribed recursive c_V, with no change of parenthesization.
Source: contextual lemma, three recursion equations
(blueprint: def-sf-finite-functor-expressions). -/
def Expression.comparison {a : S} (V : Expression O loc a) (K : ∀ i, C (loc i)) :
    (E a).inverse.obj (V.evalD.obj ((reducedInputs (E := E) loc).obj K)) ≅ V.evalC.obj K :=
  match V with
  | .input i => ((E (loc i)).unitIso.app (K i)).symm
  | .unary f V => O.unaryComparison f _ ≪≫ (O.barA f).mapIso (Expression.comparison V K)
  | .binary f V T => O.binaryComparison f _ _ ≪≫
      (O.barB f).mapIso ((Expression.comparison V K).prod (Expression.comparison T K))

/-- The specified r_V = e_(M_V) R(c_V⁻¹).
Source: contextual lemma, displayed r_V (blueprint: def-sf-finite-functor-expressions). -/
def Expression.coefficientComparison {a : S} (V : Expression O loc a)
    (K : ∀ i, C (loc i)) :
    (E a).functor.obj (V.evalC.obj K) ≅ V.evalD.obj ((reducedInputs (E := E) loc).obj K) :=
  (E a).functor.mapIso (Expression.comparison O loc V K).symm ≪≫
    (E a).counitIso.app (V.evalD.obj ((reducedInputs (E := E) loc).obj K))

/-- Paired expression transformations generated by coefficient equations, identities,
composition, inverses, and arbitrary unary/binary contexts. Binary contexts may change
both children and may repeat any input or transformation. Barred arrows are independent data.
Source: contextual lemma, generator and closure clauses
(blueprint: def-sf-finite-functor-expressions). -/
inductive Paired : {a : S} → (V T : Expression O loc a) →
    (V.evalD ⟶ T.evalD) → (V.evalC ⟶ T.evalC) → Prop where
  | generator {a : S} {V T : Expression O loc a}
      (h : V.evalD ⟶ T.evalD) (k : V.evalC ⟶ T.evalC)
      (coefficient : ∀ K, (Expression.coefficientComparison O loc V K).hom ≫
        h.app ((reducedInputs (E := E) loc).obj K) =
        (E a).functor.map (k.app K) ≫ (Expression.coefficientComparison O loc T K).hom) :
        Paired V T h k
  | identity {a : S} (V : Expression O loc a) : Paired V V (𝟙 _) (𝟙 _)
  | comp {a : S} {V T U : Expression O loc a}
      {h : V.evalD ⟶ T.evalD} {k : V.evalC ⟶ T.evalC}
      {h' : T.evalD ⟶ U.evalD} {k' : T.evalC ⟶ U.evalC}
      (p : Paired V T h k) (q : Paired T U h' k') : Paired V U (h ≫ h') (k ≫ k')
  | inverse {a : S} {V T : Expression O loc a}
      (h : V.evalD ≅ T.evalD) (k : V.evalC ≅ T.evalC)
      (p : Paired V T h.hom k.hom) : Paired T V h.inv k.inv
  | unary {a b : S} (f : O.Unary a b) {V T : Expression O loc a}
      {h : V.evalD ⟶ T.evalD} {k : V.evalC ⟶ T.evalC}
      (p : Paired V T h k) : Paired (.unary f V) (.unary f T)
        (whiskerRight h (O.A f)) (whiskerRight k (O.barA f))
  | binary {a b c : S} (f : O.Binary a b c)
      {V T : Expression O loc a} {W U : Expression O loc b}
      {h : V.evalD ⟶ T.evalD} {k : V.evalC ⟶ T.evalC}
      {h' : W.evalD ⟶ U.evalD} {k' : W.evalC ⟶ U.evalC}
      (p : Paired V T h k) (q : Paired W U h' k') :
      Paired (.binary f V W) (.binary f T U)
        (whiskerRight (h.prod' h') (O.B f)) (whiskerRight (k.prod' k') (O.barB f))

end CategoryTheory.FiniteFunctorExpressions
