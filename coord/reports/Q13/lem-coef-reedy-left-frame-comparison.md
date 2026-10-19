## Worker report

The module `Sheaf.CategoryTheory.ReedyLeftFrameComparison` states
`reedy_left_frame_comparison`, the left-Quillen transport and comparison theorem from
Hovey, *Model Categories*, Theorem 5.2.8, Proposition 5.4.7 and Lemma 5.5.1, pages
128 and 132--133 (blueprint `lem-coef-reedy-left-frame-comparison`). The proof is `sorry`.

The Lean statement renders the node clause by clause. `M` and `N` are complete and
cocomplete model categories with functorial factorizations, as in
lem-coef-reedy-model-structure. `T ⊣ U`
is the given adjunction; `hC` and `hTC` say that `T` preserves cofibrations and trivial
cofibrations. `X` is cofibrant via `cofibrations M (initial.to X)`. `S` is Reedy cofibrant
via `Reedy.leftClass ... (cofibrations M) (initial.to S)`, with `hS0` identifying `S^0`
with `X`; `p` is its augmentation, `hp` says every component is a weak equivalence, and
`hp0` says the degree-zero component is the identity under that identification. `S'` is
Reedy cofibrant in `N`, `hS'0` identifies its degree-zero object with `TX`, and `p'` is a
Reedy trivial fibration via `Reedy.rightClass ... (trivialFibrations N)`, with `hp'0` its
specified degree-zero identity. The conclusion states that `S ⋙ T` is Reedy cofibrant,
that `T` sends every weak equivalence between cofibrant objects of `M` to a weak
equivalence, that
all transported augmentation components and all structure maps of `S ⋙ T` are weak
equivalences, and that there is a natural transformation `a` to `S'`. Its equation is
`a ≫ p' = T(p)`, rendered by `Functor.whiskerRight p T` followed by
`Functor.constComp`; its degree-zero component is the identity after `hS0` and `hS'0`,
and all components of `a` are weak equivalences.

The statement dependencies used are `lem-coef-reedy-model-structure`, through the
existing module `Sheaf.CategoryTheory.ReedyModelStructure` (especially
`HomotopicalAlgebra.Reedy.leftClass`, `rightClass`, and the Reedy `SimplexCategory`
structure). The Brown split-factorization and left-adjoint-colimit facts are Mathlib
leaves recorded in the node's proof dependencies: `HomotopicalAlgebra.CofibrantBrownFactorization.instNonemptyOfIsCofibrant`
and `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`; no duplicate project
declarations were written.

Edge cases checked include degree zero (`SimplexCategory.mk 0`) and the empty latching
boundary, identity adjunctions, and non-fibrant `X`; the explicit object identifications
`hS0` and `hS'0` retain the identity clauses without imposing a definitional equality.
The empty indexing boundary is handled by the existing Reedy definitions.

Searches made: `msearch.py` leanfinder for “A left Quillen functor preserves Reedy
cofibrant cosimplicial frames and has a comparison to a special frame” (8 hits, no exact
match); `msearch.py` loogle for `"CofibrantObject"` (12 hits, no exact match);
`msearch.py` leansearch for “Left Quillen functors preserve weak equivalences between
cofibrant objects” (8 hits, no exact match); and `msearch.py` grep for
`Reedy|[Cc]osimplicial.*[Ff]rame|[Ll]eftQuillen` in `AlgebraicTopology` (hits only the
Reedy foundation, no comparison theorem). Repository searches with `rg` found no
existing declaration or node module for this item. All searches were recorded in
`searches.jsonl` by the search wrapper.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fixes

Applied by the maintainer's reviewer (H3, H8, H9):

- H3: the "moreover" clause said that `T` preserves every weak equivalence of `M`. That is
  false for left Quillen functors in general (the colimit functor on projectively cofibrant
  pushout diagrams is a counterexample), and the node restricts it to weak equivalences
  between cofibrant objects. The clause now has the hypotheses
  `cofibrations M (initial.to A)` and `cofibrations M (initial.to B)`.
- H3/H9: the binders `[HasLimitsOfSize.{w, w} _] [HasColimitsOfSize.{w, w} _]` with a free
  universe `w` were removed. `Reedy.leftClass`/`rightClass` on `SimplexCategory : Type`
  use size-0 limits, which come from `HasLimits`/`HasColimits`. The free `w` was unused,
  and a caller could not infer it.
- H3: the model categories of lem-coef-reedy-model-structure have functorial factorizations,
  and `Reedy.model_structure` needs them (step 3 objectwise cofibrancy in `M`, step 4
  lifting in `N`). The instances
  `(cofibrations _).HasFunctorialFactorization (trivialFibrations _)` and
  `(trivialCofibrations _).HasFunctorialFactorization (fibrations _)` are now assumed for
  `M` and `N`, as in the sibling `reedy_simplicial_frame_comparison`.
- H8: the theorem docstring now carries the node's four proof steps.

