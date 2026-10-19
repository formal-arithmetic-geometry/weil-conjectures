## Worker report

The module `Sheaf.CategoryTheory.SimplicialOperatorsReconstruction` states
`CategoryTheory.simplicialObject_reconstruction`, with one `sorry` proof. Its two
conjuncts are Stacks Tag 016B(2) (unique reconstruction) and 016B(3) (morphisms).
The source was read in `literature/stacks-project/simplicial.tex`,
`lemma-characterize-simplicial-object` and the following `remark-relations`.
No definition, hypothesis, correction, dependency repair or new node is needed.
Only the item's `lean` field changes. The docstring contains all six DAG proof
steps, including word evaluation, unique lifts, strict uniqueness and naturality.

Clause-by-clause correspondence:

- An ordinary category is `{D : Type u} [Category.{v} D]`, with independent,
  explicitly declared object and morphism universes. There are no limits,
  colimits, nonemptiness or other structural assumptions.
- The objects in nonnegative integer degrees are `U : ℕ → D`.
- Faces in every positive degree are
  `d : ∀ n : ℕ, Fin (n + 2) → (U (n + 1) ⟶ U n)`.
  The target degree is used as the parameter, so degree one has both faces.
- Degeneracies are
  `s : ∀ n : ℕ, Fin (n + 1) → (U n ⟶ U (n + 1))`.
- The first relation is the first implication premise:
  `d (n + 1) j.succ ≫ d n i = d (n + 1) i.castSucc ≫ d n j`
  for `i ≤ j`. Here the node's larger index is `j + 1`, so its `i < j`
  condition becomes `i ≤ j` after this reindexing. This ranges over all
  composable pairs of faces, starting with source degree two.
- The second relation is
  `s (n + 1) j.succ ≫ d (n + 1) i.castSucc = d n i ≫ s n j`
  for `i ≤ j.castSucc`. The original degeneracy index is `j + 1`;
  its decremented index is `j`. This covers exactly `i < j + 1`.
- Both identity clauses are separate premises, for every degree `n` and
  `j : Fin (n + 1)`:
  `s n j ≫ d n j.castSucc = 𝟙 (U n)` and
  `s n j ≫ d n j.succ = 𝟙 (U n)`.
- The fourth relation is
  `s (n + 1) j.castSucc ≫ d (n + 1) i.succ = d n i ≫ s n j`
  for `j.castSucc < i`. The original face index is `i + 1`, so this
  is exactly the node's face index strictly greater than `j + 1`.
- The fifth relation is
  `s n j ≫ s (n + 1) i.castSucc = s n i ≫ s (n + 1) j.succ`
  for `i ≤ j`. Recall that `a ≫ b` is ordinary composition `b ∘ a`.
  Thus the orientations of all five displayed relations agree with the node.
- Reconstruction concludes `∃! X : SimplicialObject D`. The predicate supplies
  `h : ∀ n : ℕ, X _⦋n⦌ = U n`, and says every `X.δ i` and `X.σ i`,
  transported by `eqToHom` along these object equalities, equals `d n i` and
  `s n i`, respectively. These are equalities of the prescribed objects and
  arrows, not arbitrary isomorphisms. The unique object is the functor `X`
  itself; proof witnesses `h` are not extra data subject to uniqueness.
- The second conjunct quantifies over arbitrary `X Y : SimplicialObject D`
  and `f : ∀ n : ℕ, X _⦋n⦌ ⟶ Y _⦋n⦌`, independently of the reconstruction
  data. Its left side says `∃ φ : X ⟶ Y` whose every component is `f n`.
  Its right side is exactly all face squares
  `X.δ i ≫ f n = f (n + 1) ≫ Y.δ i` and all degeneracy squares
  `X.σ i ≫ f (n + 1) = f n ≫ Y.σ i`. The connective is `↔`, not just
  sufficiency. A natural transformation is determined by its components.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-object`: the recorded module
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`, declarations
  `CategoryTheory.SimplicialObject`, `.δ` and `.σ`. Their full definitions
  identify the functor category and the images of the usual cofaces and
  codegeneracies. This is the public import used in the statement.
- Proof dependency `lem-sc-simplex-morphism-property-generators`:
  `Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty`,
  `SimplexCategory.morphismProperty_eq_top`. Its full signature requires a
  multiplicative morphism property containing all `δ` and `σ`.
- Proof dependency `lem-sc-module-cup-godement-simplex-presentation-faithful`:
  `Sheaf.CategoryTheory.SimplexPresentationFaithful`,
  `simplexPresentation_faithful : SimplexCategoryGenRel.toSimplexCategory.Faithful`.
  The declaration and proof docstring were read. These latter two imports are
  ordinary proof-only imports, as required; there is no import cycle.

Edge cases checked before writing:

- Degree zero has its object, one degeneracy, and both retraction equations
  `s₀ ≫ d₀ = 1` and `s₀ ≫ d₁ = 1`. No degree-minus-one face is introduced.
- The two mixed off-diagonal cases are indexed starting at source degree one;
  no typed instances in degree zero are omitted. The diagonal mixed cases
  already apply in degree zero. The double-face relation starts at degree two
  and the double-degeneracy relation starts at degree zero.
- Equal face indices in the reindexed double-face premise correspond to the
  consecutive original indices. Equal degeneracy indices are included in
  the double-degeneracy premise. First and last indices are included by `Fin`.
- Empty words give identities and maps to/from `[0]` are covered by the proof
  plan. Constant simplicial objects satisfy the statement with all operators
  identities. Empty categories cause no nonempty-data assumption: the relevant
  universal quantifiers are vacuous. Zero objects, when present, are allowed.
- The transport directions are `U source → X source → X target → U target`.
  Strict uniqueness is therefore not weakened to uniqueness up to isomorphism.

Searches for existing declarations (all performed through `msearch.py` or
read-only source searches; the raw tool results are in sandbox `searches.jsonl`):

- LeanFinder: "Objects and face and degeneracy maps satisfying the simplicial
  identities uniquely determine a simplicial object". Eight hits: chiefly
  `SimplicialObject`, split-object extensionality and `hom_ext`; none reconstructs
  an arbitrary simplicial object from operators.
- Loogle: `SimplexCategoryGenRel`. Twelve hits, including the presented category,
  its generators and `toSimplexCategory`. These supply the presentation, not
  the requested reconstruction statement.
- LeanSearch: "A simplicial object is uniquely reconstructed from objects with
  face and degeneracy maps satisfying the simplicial identities". Eight hits:
  `SimplicialObject`, `SSet` and identities for already given simplicial objects;
  none states reconstruction.
- Mathlib grep via `msearch.py`:
  `of.*[δσ]|mk.*SimplicialObject|toSimplexCategory.*(equiv|Equiv|Faithful|Full)|def.*(lift|desc)`
  under `AlgebraicTopology`: no reconstruction declaration. Read the full
  `SimplicialObject` definitions and relevant identities in `Basic.lean`, and
  the six presentation relations in `GeneratorsRelations/Basic.lean`.
- Read-only `rg` in upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, reconstruction, and operator
  construction names found no exact match. The project has the recorded
  faithfulness theorem and concrete Godement constructions, which do not state
  reconstruction for an arbitrary category. Exact-name search for
  `simplicialObject_reconstruction` in Mathlib, upstream, project and the name
  index found no collision.

Validation: the prescribed `scompile.py Q29
lem-trf-simplicial-operators-reconstruction <module>` compiled the sandbox and
library module cleanly (1.7 seconds each, no warnings or errors). Every variable
and universe is explicitly bound; `autoImplicit` is also disabled in the file.
No statement dispute or node fault was found.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
