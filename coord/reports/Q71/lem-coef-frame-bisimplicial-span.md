## Worker report

The module `Sheaf.CategoryTheory.FrameBisimplicialSpan` states the bisimplicial Hom span and its diagonal comparison. It defines `frameBisimplicialLeft`, `frameBisimplicialRight`, and `frameBisimplicialVertical` as the canonical maps induced by `T`, `b`, `a`, and the coaugmentations. It also defines `frameBisimplicialConstMap`, the componentwise constant natural transformation from `(const Y) ⋙ T` to `const Z` induced by `r`; this is the correctly typed constant-target instance required by the left map. The theorem `CategoryTheory.frame_bisimplicial_span` has proof `sorry`, as required for a stage-2 statement.

The Lean theorem hypotheses and conclusions correspond to the node clause by clause:

- `{M : Type u} [Category.{v} M] [ModelCategory M] [HasLimits M] [HasColimits M]` and the corresponding binders for `N` render the two model categories and the completeness/cocompleteness assumptions.
- `T`, `S`, `B`, `S'`, and `B'` are the functor and the four simplicial/opposite-simplicial diagrams.
- `a : S ⋙ T ⟶ S'` and `b : B ⋙ T ⟶ B'` render the two natural transformations.
- `_ha : ∀ m, WeakEquivalence (a.app m) ∧ IsCofibrant (T.obj (S.obj m)) ∧ IsCofibrant (S'.obj m)` says exactly that every component of `a` is a weak equivalence between cofibrant objects.
- `_hB' : Reedy.rightClass (monomorphisms SimplexCategory).op (fibrations N) (terminal.from B')` renders Reedy fibrancy of `B'`.
- `_hconst : ∀ n k f, WeakEquivalence (B'.map f)` renders homotopical constancy of `B'`.
- `frameBisimplicialLeft` acts by the lifted map `h ↦ b_n ≫ T(h)` (with the category-theoretic composition order represented by `T.map h ≫ b.app n`), and `frameBisimplicialRight` acts by precomposition with `a.app m`; their domains and codomains are the lifted Hom diagrams.
- The first conclusion conjunct is `SSet.Enhanced.IsWeakHomotopyEquivalence` for the diagonal of the right leg, rendering that `diag D' → diag E` is a weak homotopy equivalence.
- `Y`, `Z`, `i`, `i'`, and `r` are the two constant-target coaugmentations and the map `TY ⟶ Z`; the displayed premise `∀ n, T.map (i.app n) ≫ b.app n = r ≫ i'.app n` is exactly `bT(i)=i' const(r)` componentwise.
- The first displayed equality is the commuting square for the left leg, using `frameBisimplicialConstMap T r` for the constant target map. The second displayed equality is the commuting square for the right leg. `frameBisimplicialVertical` supplies the three maps from the mapping simplicial sets `H(S,Y)`, `H(TS,Z)`, and `H(S',Z)` to the corresponding diagonals.

Dependency declarations used:

- `Sheaf.CategoryTheory.ReedyModelStructure`, declarations under `HomotopicalAlgebra.Reedy` (in particular `Reedy.rightClass`, `Reedy.model_structure`, and matching maps).
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`, declaration `SSet.KanQuillen.right_proper_kan_quillen` and its recorded weak-equivalence/fibration interfaces.
- Mathlib's `SSet` declarations from `Mathlib/AlgebraicTopology/SimplicialSet/Basic.lean` (the recorded `def-weil-pbc-simplicial-set` match).
- `Sheaf.CategoryTheory.SpecialResolutionZigzagNerve`, declarations `CategoryTheory.specialResolutionHomDiagram`, `specialResolutionHomMap`, and `specialResolutionHomFunctorMap`, which are the existing canonical Hom-diagram constructions used by the three helper definitions.
- Proof-only stated dependencies imported by the module are `Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence` and `Mathlib.AlgebraicTopology.ModelCategory.BrownLemma`.

The edge cases checked were: degree zero in both simplex indices (the matching object is terminal in the intended lifting argument), identity and composite simplex operators, identity `a` and `b`, identity `r`, zero/initial and terminal objects when available, and constant diagrams (where `frameBisimplicialConstMap` has every component equal to `r`). The universe lifts use the explicit parameters `u v u' v'`; no universe equality is imposed.

Searches made before writing the module found no existing statement or definition of this span. `msearch.py ... leanfinder` queried “Natural transformations induce bisimplicial Hom span with diagonal weak equivalence for cofibrant objects and Reedy fibrant target” (eight generic homotopy hits, no match). `msearch.py ... loogle` queried `HomotopicalAlgebra.ModelCategory, CategoryTheory.specialResolutionHomDiagram` (no match for the combined notion). `msearch.py ... grep` queried `bisimplicial|cosimplicial.*fram` in `AlgebraicTopology` (zero hits). Repository `rg` searches for `frameBisimplicial`, `bisimplicial`, and the item id found no pre-existing project declaration. The Mathlib and upstream searches recorded in `searches.jsonl` were also inspected; all hits concern ordinary Reedy or Dold–Kan constructions rather than this theorem.

No statement correction, new definition node, dependency repair, or `STATEMENT-DISPUTED` marker is needed.

## Second reading by Q71

I reread the complete node statement and the complete module after the compile repair. The model-category, diagram, componentwise weak-equivalence/cofibrancy, Reedy-fibrancy, and homotopical-constancy hypotheses are all explicit. The helper maps use the recorded canonical Hom-diagram declarations, and the extra `frameBisimplicialConstMap` only supplies the natural transformation that the prose's `const(r)` requires when the source is definitionally `(const Y) ⋙ T`; it does not add a mathematical hypothesis. The diagonal weak-equivalence conjunct and both strict commuting equalities are present with the same directions as the node. The source compiles cleanly with only the expected theorem `sorry`; no mismatch was found.
