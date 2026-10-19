## Worker report

The module `lean/Sheaf/CategoryTheory/FiniteEmbeddedSimplexResolution.lean` states
`SSet.exists_finite_embedded_simplex_resolution`.  It introduces a finite simplicial set
`X : SSet.{u}` with the Mathlib hypothesis `[X.Finite]`, then asserts existence of a
finite `Q : SSet.{u}`, a `Q.Nonsingular` instance, and a simplicial map `q : Q ⟶ X`.
`SSet.Nonsingular` is Mathlib's exact formulation that every nondegenerate simplex
`Δ[n] ⟶ Q` is a monomorphism.  The final universal clause quantifies over a simplicial
set `E`, a quasicategory instance `_ : E.Quasicategory`, a map `p : X ⟶ E`, and a
vertex `T : E _⦋0⦌`.  The displayed map is the restriction map induced by
`MonoidalClosed.pre q`; its source is the right-pinched mapping space from the vertex
of `p` to the constant diagram on `T`, and `mappingSpaceMap` gives the corresponding
map after restriction to `Q`.  `SSet.Enhanced.IsFunctorEquivalence` states that this
map is an equivalence of the simplicial mapping spaces (hence the Kan-complex
formulation in the source).  The empty finite simplicial set is allowed, and no
quasicategory condition is imposed on `X` or `Q`; no colimit hypothesis on `E` is
introduced.

The dependency declaration used is the complete interface in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded by
`def-cbc-enhanced-diagrams-cones` as `SSet.Enhanced.coneCategory`.  In this statement
I use its recorded declarations `SSet.Enhanced.diagramVertex`,
`SSet.Enhanced.constantDiagrams`, `SSet.Enhanced.mappingSpaceMap`, and
`SSet.Enhanced.IsFunctorEquivalence`; the restriction map is Mathlib's
`CategoryTheory.MonoidalClosed.pre`.  The finite and nonsingular notions are
Mathlib's `SSet.Finite` and `SSet.Nonsingular` from
`Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular`.

Searches for an existing theorem/definition were made as follows.  LeanFinder
(`msearch.py ... leanfinder "finite simplicial set finite resolution every nondegenerate
simplex monomorphism"`) returned only `SSet.Finite`, finiteness lemmas, and no
resolution theorem.  Loogle (`... loogle "SSet.Finite, SSet.nonDegenerate, Mono
yonedaEquiv"`) returned no result (and reported `Mono` as an unknown query token).
Grep over Mathlib simplicial-set files for `Finite|nonDegenerate|mono_of_nonDegenerate`
found the exact primitive classes and lemmas, including `SSet.Nonsingular`, but no
finite cofinal-resolution theorem.  `rg` over both `WeilConjectures/` and the
project's `lean/Sheaf` found no declaration with this theorem or name.  The existing
Mathlib `SSet.Nonsingular` class was therefore used directly rather than redefined;
there is no exact theorem match for this node.

The file was compiled with `scompile.py` and contains only the postponed `sorry` proof.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module line by line.  The `[X.Finite]` hypothesis,
finite `Q`, nonsingularity/embedded-simplex clause, map `q`, universal quantifiers over
`E`, its quasicategory hypothesis, `p`, and vertex `T` all appear in the Lean binders.
The restriction map is canonical (`MonoidalClosed.pre q`), and its source and target
are exactly the dependency's right-pinched `mappingSpaceMap`; no arbitrary map,
colimit assumption, or extra condition on `X` or `Q` was added.  `SSet.Nonsingular`
was checked in Mathlib's full declaration and matches the node's monomorphism clause.
The `X = ∅` case remains permitted.  No mismatch was found.


## Second reading by Q34

I independently opened the node, its source place, the dependency declaration
`SSet.Enhanced.coneCategory` and the Lean module. The item statement is the
finite intermediate resolution in HTT Variant the project server, claim (*) and claim
(*′), printed p. 256. The source's displayed finite case says that a finite
simplicial set admits a cofinal map from a finite simplicial set whose
nondegenerate simplices are monomorphisms; the node expands the same restriction
property in the right-pinched mapping-space convention of
`def-cbc-enhanced-diagrams-cones`. The source and node allow the empty case and
make no quasicategory or colimit assumption on the indexing simplicial sets or
target.

The step-1 object and clause audit is:

- The input is a small simplicial set `X`; Lean renders this as
  `{X : SSet.{u}}`.
- Finiteness of `X` is the node's finite-simplicial-set hypothesis; Lean renders
  it as the typeclass `[X.Finite]`.
- The output finite simplicial set is `Q : SSet.{u}` and its finiteness is the
  existential instance `_ : Q.Finite`.
- The embedded-simplex condition is exactly Mathlib's
  `SSet.Nonsingular`, rendered by `_ : Q.Nonsingular`; its declaration says
  every nondegenerate simplex map from a standard simplex is monic.
- The comparison map is the simplicial map `q : Q ⟶ X`.
- The universal quantifier over targets is rendered as
  `∀ (E : SSet.{u}) (_ : E.Quasicategory)`, with no condition on `X` or `Q`.
- The diagram is `p : X ⟶ E`, and the specified vertex is
  `T : E _⦋0⦌`, exactly the node's `T ∈ E`.
- The conclusion is the restriction map induced by `q`, rendered as
  `SSet.Enhanced.mappingSpaceMap ((MonoidalClosed.pre q).app E)
  (SSet.Enhanced.diagramVertex p)
  ((SSet.Enhanced.constantDiagrams X E).app _ T)` and asserted to satisfy
  `SSet.Enhanced.IsFunctorEquivalence`. This is the dependency's coherent
  equivalence notion for the Kan right-pinched mapping spaces. The source and
  target therefore are respectively the mapping spaces for `p` and `p q`, and
  constants restrict to constants. Quantifier order is unchanged.

No hypothesis was added or dropped, and no conclusion was weakened or
strengthened. The Lean universe is shared by `X`, `Q`, `E`, and the vertex
simplicial sets, which is the node's single small-simplicial-set convention; no
universe equality beyond that convention is introduced.

Edge cases checked: `X = ∅` is admitted by `[X.Finite]`, and the node's empty
construction `Q = ∅` is not excluded; `Q` may be empty, and no nonempty index or
vertex assumption is present for `X` or `Q`; the zero-dimensional case and
constant vertex case use the same `T : E _⦋0⦌`; arbitrary characteristics are
irrelevant; and no quasicategory or colimit condition is imposed on `X` or `Q`.

For the one-definition audit, I searched Mathlib's simplicial-set files and
`WeilConjectures/` for finite embedded/simplex-resolution and cofinal-resolution
notions, and searched the project's `lean/Sheaf` tree. My independent LeanFinder query was “Finite nonsingular replacement of a
simplicial set preserving cocones in every infinity category”; it returned
`SSet.Finite.finite`, coskeleta, `KanComplex`, finiteness and skeleton primitives,
and the finite initial object, with no resolution theorem. My independent
Loogle query was `"Nonsingular", "Finite"` and returned no hits. My LeanSearch
query “Every finite simplicial set admits a finite nonsingular cofinal
replacement” returned finiteness, presentability and epi/mono finiteness
lemmas; none concludes nonsingularity or universal restriction equivalence.
The later project grep found the parent poset replacement only in its proof
docstring; it is not an existing declaration of this intermediate theorem. I also used
grep with `Finite|nonDegenerate|mono_of_nonDegenerate` and
`Nonsingular|nonDegenerate.*mono|mono.*nonDegenerate`. These searches found only
Mathlib's primitive `SSet.Finite` and `SSet.Nonsingular`; no theorem with this
statement exists. I opened `Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular`
and used that exact class rather than defining a private copy. The dependency
`Sheaf.CategoryTheory.EnhancedDiagramsCones` was opened and its declarations
`diagramVertex`, `constantDiagrams`, `mappingSpaceMap`, and
`IsFunctorEquivalence` are the ones used here. The proof-dependency modules with
recorded declarations are imported (`EnhancedFunctorConeCalculus` and
`GlueSimplex`); the two new localization nodes remain postponed and are named
only in the proof plan.

The only mismatch found was H8: the worker theorem docstring gave the source and
statement but omitted the node's proof steps. I repaired the docstring by adding
the seven-step plan: strengthened universally localizing induction and empty
base case; maximal-simplex removal and boundary pushout; pullback/cone graph
construction; nonsingularity; finiteness; weak-contractibility and localization
pushout; and the final functor-category/mapping-space comparison. I also added the two missing ordinary imports of recorded proof-dependency
modules, `EnhancedFunctorConeCalculus` and `GlueSimplex`, as stage 2 requires.
No statement, node field, declaration, or dependency list was changed. The module now
compiles cleanly with `scompile.py`; the only postponed proof remains `sorry`.
