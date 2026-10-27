module

public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Injectivity transfer from free normalized homology

Source: Stacks Project, `simplicial.tex`, Tag 08P2, injectivity paragraph,
with the higher-face normalization and differential `d₀`
(blueprint: lem-trf-free-normalized-homology-injectivity-transfer).

The degreewise free construction is composition with `AddCommGrpCat.free`, and
its evaluation is the counit of `AddCommGrpCat.adj`. Normalized elements are
represented by Mathlib's normalized Moore subobjects and their canonical arrows.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology

open NormalizedMooreComplex

/-- Source: Stacks Project, Tag 08P2, third proof paragraph (lines 5935--5958),
written with higher-face kernels and differential `d₀`.
(blueprint: lem-trf-free-normalized-homology-injectivity-transfer)

For a normalized cycle `x` and a normalized `y` with boundary `f x`, the differences
`[x] - [0]` and `[y] - [0]` give normalized lifts. The first is a cycle, the boundary
of the second is the free image of the first, and evaluation of the first is `x`.
Consequently injectivity of the free map on degree `n` homology implies injectivity
of the original map on that degree's homology.

Proof plan:
1. Evaluation and the free map commute with every face, as can be checked on
   generators and extended additively. Thus they restrict to normalized complexes.
   The simplicial identities show that `d₀` preserves normalization and squares to zero.
2. Every face of a positive-degree normalized cycle `x` vanishes, so every face of
   `[x] - [0]` vanishes. The higher faces of `[y] - [0]` vanish, and its zeroth face
   is `[f x] - [0]`. Evaluation sends `[x] - [0]` to `x`. For `n = 0`, the outgoing
   differential is zero and no negative-degree term or face is used.
3. Represent a kernel homology class by `x` and choose a normalized boundary witness
   `y` in the target. Step 2 lifts it to a free cycle whose image is a boundary.
   Injectivity makes this free cycle a boundary, say of `v`.
4. Evaluation of `v` is normalized, since evaluation commutes with higher faces,
   and its zeroth face is `x`. Thus the original class is zero. Taking differences
   of classes proves injectivity. These calculations also apply in degree zero. -/
theorem freeNormalizedHomologyInjectivityTransfer
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    (∀ (x : (obj X).X n) (y : (obj Y).X (n + 1)),
      (obj X).d n (n - 1) x = 0 →
      objD Y n y = (NormalizedMooreComplex.map f).f n x →
      ∃ (xt : (obj (X ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free)).X n)
        (yt : (obj (Y ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free)).X (n + 1)),
        (objX (X ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free) n).arrow xt =
          FreeAbelianGroup.of ((objX X n).arrow x) - FreeAbelianGroup.of 0 ∧
        (obj (X ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free)).d n (n - 1) xt = 0 ∧
        (objX (Y ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free) (n + 1)).arrow yt =
          FreeAbelianGroup.of ((objX Y (n + 1)).arrow y) - FreeAbelianGroup.of 0 ∧
        objD (Y ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free) n yt =
          (NormalizedMooreComplex.map
            (Functor.whiskerRight f (forget AddCommGrpCat ⋙ AddCommGrpCat.free))).f n xt ∧
        (AddCommGrpCat.adj.counit.app (X _⦋n⦌))
            ((objX (X ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free) n).arrow xt) =
          (objX X n).arrow x) ∧
    (Function.Injective
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
          (NormalizedMooreComplex.map
            (Functor.whiskerRight f (forget AddCommGrpCat ⋙ AddCommGrpCat.free)))) →
      Function.Injective
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).map
          (NormalizedMooreComplex.map f))) := by
  sorry

end AlgebraicTopology
