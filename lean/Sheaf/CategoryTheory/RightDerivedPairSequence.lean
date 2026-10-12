/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Exact.Basic

/-!
# Derived sequence from a sequence exact on injectives

Source: Stacks Project, Tag 0A50, passage from the injective section sequence to
its long exact homology sequence; Homology, Tag 0117.
(blueprint: lem-weil-pbc-right-derived-pair-sequence)
-/

@[expose] public section

universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Source: Stacks Project, Tag 0A50, final paragraph, and Homology Tag 0117.
(blueprint: lem-weil-pbc-right-derived-pair-sequence)

Proof: For an injective resolution P of M, evaluate A, B, D, E termwise.
The maps (a,b) and c-d commute with differentials by naturality. Injectivity,
exactness and surjectivity in the hypotheses make the resulting sequence
A(P) → B(P) × D(P) → E(P) degreewise short exact. Apply the homology long
exact sequence. Finite products of abelian groups are exact, so their
complex homology is the product of homologies, with the two projections
identifying the induced maps with (Rⁿa,Rⁿb) and Rⁿc-Rⁿd. Transport by the
canonical isoRightDerivedObj for P. Lift a coefficient morphism to a map of
injective resolutions:
it gives a morphism of the short exact sequences, so naturality of the
homology boundary gives the naturality equation for the transported δ.
Homotopy uniqueness makes this independent of the lift. Taking the
canonical resolutions yields the asserted natural transformations.
Empty and zero categories cause no exception; zero functors and split
sequences give the expected zero boundaries. -/
theorem rightDerived_pair_sequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    (A B D E : C ⥤ AddCommGrpCat.{w})
    [A.Additive] [B.Additive] [D.Additive] [E.Additive]
    (a : A ⟶ B) (b : A ⟶ D) (c : B ⟶ E) (d : D ⟶ E)
    (hinj : ∀ (I : C), Injective I →
      Function.Injective (fun x => (a.app I x, b.app I x)))
    (hexact : ∀ (I : C), Injective I →
      Function.Exact (fun x => (a.app I x, b.app I x))
        (fun x => c.app I x.1 - d.app I x.2))
    (hsurj : ∀ (I : C), Injective I →
      Function.Surjective (fun x : B.obj I × D.obj I => c.app I x.1 - d.app I x.2)) :
    ∃ δ : ∀ n : ℕ, E.rightDerived n ⟶ A.rightDerived (n + 1),
      ∀ M : C,
        ∀ n : ℕ,
          Function.Exact (fun x => ((a.rightDerived n).app M x,
            (b.rightDerived n).app M x))
            (fun x => (c.rightDerived n).app M x.1 - (d.rightDerived n).app M x.2) ∧
          Function.Exact
            (fun x : (B.rightDerived n).obj M × (D.rightDerived n).obj M =>
              (c.rightDerived n).app M x.1 - (d.rightDerived n).app M x.2)
            ((δ n).app M) ∧
          Function.Exact ((δ n).app M)
            (fun x => ((a.rightDerived (n + 1)).app M x,
              (b.rightDerived (n + 1)).app M x)) := by sorry

end CategoryTheory
