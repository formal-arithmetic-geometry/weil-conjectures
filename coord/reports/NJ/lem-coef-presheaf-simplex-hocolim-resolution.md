## Worker report

The module `Sheaf.AlgebraicTopology.PresheafSimplexHocolimResolution` defines the labelled
simplex category `SimplexElement F` (the node's `E_F`) and its arrows `(a, α)` with the
condition
`F(a)_n (F(e)(α)(τ)) = σ`.  The category instance composes `(a, α)` by componentwise
composition.  `simplexDiagram F` (the node's `B_F`) sends `(d,[n],σ)` to the tensor of the
discrete representable `h_d` and `SSet.stdSimplex.obj [n]`, and sends an arrow to the
corresponding tensor of the Yoneda map and standard-simplex map.  `SimplexEvaluationCocone`
records the evaluation cocone and its explicit Yoneda formula.  `SimplexProjectiveReplacement`
records a diagram `P`, its augmentation `P ⟶ B_F`, projective cofibrancy by lifting against
objectwise trivial fibrations, and objectwise weak equivalence.  The theorem states that a
canonical evaluation cocone exists and that for every such replacement the colimit is
projectively cofibrant and its induced augmentation to `F` is an objectwise weak homotopy
equivalence.

For the node's hypotheses and clauses, the Lean rendering is:

- `D` is an explicitly universe-bound `Type u` with `[SmallCategory D]`; `F` is
  `(F : Dᵒᵖ ⥤ SSet.{u})`.  No nonemptiness, fibrancy, or extra ring/site hypotheses are
  introduced.
- `E_F` is `simplexIndex F := SimplexElement F`; its objects have fields `d : D`,
  `n : ℕ`, and `σ : (F.obj (op d)).obj (op [n])`.
- Its arrows have `a : X.d ⟶ Y.d`, `α : [X.n] ⟶ [Y.n]`, and the exact compatibility
  equation in `SimplexElement.Hom.condition`.  `id`, composition, and their laws are
  explicit in the category instance.
- `simplexDiagram F` uses `representableFunctor`, `simplexDegreeProjection`, and the
  Cartesian monoidal tensor, giving `h_d × Δ^n` and `h_a × Δ^α`.
- `SimplexEvaluationCocone.formula` renders the component corresponding by Yoneda to
  `σ`: on `(b,t)` it is
  `(F.map b.op).app q ((F.obj (op X.d)).map t.op X.σ)`; `testInput` identifies `(b,t)`
  with the tensor element.
- `IsProjectivePresheafModel m` records the projective weak equivalences, fibrations,
  and cofibrations from `lem-coef-simplicial-presheaf-projective-model`.
- `SimplexProjectiveReplacement` quantifies a diagram `P`, an augmentation `map : P ⟶ B_F`,
  projective cofibrancy (`IsProjectivelyCofibrant`), and objectwise weak equivalence.
- The theorem's conclusion is `∃ ε : SimplexEvaluationCocone F, ∀ R`, with
  `m.categoryWithCofibrations.cofibrations (initial.to (colimit R.P))` and, for every
  `d : Dᵒᵖ`, weak homotopy equivalence of
  `(colimit.desc R.P {pt := F, ι := R.map ≫ ε.leg}).app d`.

The recorded dependency declarations used are:

- `def-coef-complete-algebroid`: `SSet.Enhanced.Algebroid.completeCategory` in
  `Sheaf.CategoryTheory.CompleteAlgebroid` (universes and the complete-algebroid context).
- `def-weil-pbc-simplicial-set`: Mathlib declarations `SSet`, `SSet.degenerate`,
  `SSet.nonDegenerate`, `SSet.Subcomplex`, and `SSet.Finite`.
- `lem-coef-simplicial-presheaf-projective-model`:
  `SSet.ProjectivePresheaf.simplicial_presheaf_projective_model` in
  `Sheaf.AlgebraicTopology.SimplicialPresheafProjectiveModel`.
- `lem-coef-hocolim-reindexing-zigzags`: the node records this proof-side
  homotopy-colimit dependency, but the displayed Lean statement uses only the
  ordinary `colimit` and has no term from that module.  Its import is therefore
  omitted from the statement module; importing it would transitively compile an
  unrelated side module whose existing `Diagrams` abbreviation fails the
  `noncomputable` check.

The module also imports `HomotopicalAlgebra.simplicialBarProjectiveResolution` from
`Sheaf.CategoryTheory.SimplicialBarProjectiveResolution` for the proof-side model
interface; no proof is attempted in this stage.  The hocolim dependency is retained in
the DAG but is proof-side only and is not imported by this statement module.  All item-specific helper declarations
are listed in the node's `lean.declarations`; no additional DAG node was needed.

Edge cases checked before writing:

- `D` may be empty: the definitions do not require an object of `D`, and the theorem has
  no `[Nonempty D]` binder.
- `F` may be empty-valued: then `SimplexElement F` is empty and all diagram quantifiers
  remain well-typed.
- `D` terminal and `D` with nontrivial automorphisms: the arrow equation retains the full
  `a : d ⟶ e` and the Yoneda evaluation uses the actual `b : e ⟶ d`.
- `n = 0` and degenerate simplices: `n : ℕ` is unrestricted and `SSet.stdSimplex` handles
  all operators; no nondegeneracy or fibrancy is assumed.
- The tensor is objectwise in `Dᵒᵖ`, and the simplex parameter uses the full simplex
  category, so no index-universe restriction is added.

Searches made:

- `msearch.py ... leanfinder "canonical representable simplex homotopy colimit resolution of a simplicial presheaf"` — 8 hits, all generic simplicial-object/realization declarations; no exact match.
- `msearch.py ... loogle "SSet, homotopy colimit, representable, cofibrant"` — unavailable query (`Unknown identifier homotopy`), so no match was claimed.
- `msearch.py ... grep "homotopy.?colimit|simplicial.?replacement|Bousfield.?Kan"` — 0 hits.
- `rg` over `WeilConjectures/` and project `lean/Sheaf/` for `simplex_hocolim_resolution`,
  `SimplexElement`, and `simplexDiagram` — no pre-existing declaration before this module.
- `grep -rn "lem-coef-presheaf-simplex-hocolim-resolution"` over the source checkout —
  no source declaration.

The module compiles cleanly with the required `scompile.py` wrapper; the theorem proof is
left as the single expected `sorry`.

The module has three postponed structure-law sorries in addition to the item theorem:
`simplexDiagramMap_id` and `simplexDiagramMap_comp` are the identity and composition
laws required to package the explicitly displayed `simplexDiagramMap` as the functor
`B_F`; `simplex_hocolim_resolution` is the node theorem itself.  Each has a source and
blueprint docstring, and no proof is attempted at stage 2.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
