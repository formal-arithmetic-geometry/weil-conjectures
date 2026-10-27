module

public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Surjectivity transfer through free simplicial abelian evaluation

Source: Stacks Project, Tag 08P2, evaluation square and the surjectivity paragraph of
`lemma-homotopy-equivalence`, with the normalized differential `d₀`.
(blueprint: lem-trf-free-normalized-homology-surjectivity-transfer)

The free simplicial abelian group on `S : SSet` is `S ⋙ AddCommGrpCat.free`.
The underlying simplicial set of `Z` is `Z ⋙ forget AddCommGrpCat`, and evaluation is
`whiskerLeft Z AddCommGrpCat.adj.counit`. The standard normalized Moore complex uses
`N(Z)₀ = Z₀`, the kernels of the positive faces in positive degrees, and differential `d₀`.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped Simplicial

namespace AlgebraicTopology

/-- Evaluation is natural, every normalized cycle lifts as `[y] - [0]`, and surjectivity
on normalized homology of the free underlying simplicial map descends to the original map.

Source: Stacks Project, Tag 08P2, `lemma-homotopy-equivalence`, evaluation square and second
proof paragraph, using differential `d₀`.
(blueprint: lem-trf-free-normalized-homology-surjectivity-transfer)

Proof: The free functor sends each generator `[s]` to the generator of its image, so its
simplicial operators respect identities and composition. Evaluation sends a finite sum of
integer multiples of generators to the same sum of simplices. Additivity makes evaluation
commute with every simplicial operator. On `[x]`, both paths around the displayed square
are `f(x)`, and additivity gives the first clause on all elements.

The simplicial identities give `dᵢ d₀ z = d₀ dᵢ₊₁ z = 0` for the positive faces of a
normalized simplex and `d₀ d₀ z = d₀ d₁ z = 0`. In degree one the target is `Z₀`, with
zero outgoing differential. Thus normalization is a complex. Naturality and additivity
make each simplicial morphism preserve the normalized subgroups and commute with their
differentials, hence induce the indicated chain and homology maps.

For a normalized cycle `y` in positive degree, every face of `y` is zero, including `d₀`
by the cycle condition. Every face of `[y] - [0]` is therefore `[0] - [0] = 0`.
In degree zero both normalization and the cycle condition impose no restriction.
Evaluation sends this lifted normalized cycle to `y - 0 = y`, proving the second clause.

Finally represent any homology class of `Y` by `y` and lift it to `[y] - [0]`. The assumed
surjectivity supplies a normalized cycle `u` in the free group on `X` whose image differs
from this lift by the boundary of a normalized simplex `v`. Evaluating gives
`f(ε_X(u)) - y = ∂ ε_Y(v)` by the square and compatibility with differentials. Hence the
class of `ε_X(u)` maps to the chosen class of `y`. This also works in degree zero. -/
theorem free_normalized_homology_surjectivity_transfer
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) :
    (whiskerLeft X AddCommGrpCat.adj.counit ≫ f =
      whiskerRight (whiskerRight f (forget AddCommGrpCat)) AddCommGrpCat.free ≫
        whiskerLeft Y AddCommGrpCat.adj.counit) ∧
    (∀ (n : ℕ) (y : ((normalizedMooreComplex AddCommGrpCat).obj Y).cycles n),
      ∃ z : ((normalizedMooreComplex AddCommGrpCat).obj
          ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).cycles n,
        (Subobject.arrow (NormalizedMooreComplex.objX
          ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free) n))
            (((normalizedMooreComplex AddCommGrpCat).obj
              ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).iCycles n z) =
          FreeAbelianGroup.of ((Subobject.arrow (NormalizedMooreComplex.objX Y n))
            (((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles n y)) -
              FreeAbelianGroup.of (0 : Y _⦋n⦌) ∧
        (((normalizedMooreComplex AddCommGrpCat).map
          (whiskerLeft Y AddCommGrpCat.adj.counit)).f n)
            (((normalizedMooreComplex AddCommGrpCat).obj
              ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)).iCycles n z) =
          ((normalizedMooreComplex AddCommGrpCat).obj Y).iCycles n y) ∧
    (∀ n : ℕ,
      Function.Surjective (HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat).map
          (whiskerRight (whiskerRight f (forget AddCommGrpCat)) AddCommGrpCat.free)) n) →
      Function.Surjective (HomologicalComplex.homologyMap
        ((normalizedMooreComplex AddCommGrpCat).map f) n)) := by
  sorry

end AlgebraicTopology
