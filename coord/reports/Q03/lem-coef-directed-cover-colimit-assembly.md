## Worker report

The module `Sheaf.CategoryTheory.DirectedCoverColimitAssembly` states
`SSet.Enhanced.directed_cover_colimit_assembly`, with its sole theorem proof `sorry`.
The node's mathematical statement is unchanged. Four real-data helpers construct the
canonical incidence subset, its two projections, and the inclusion of a local fiber.
They belong to this assembly construction and are listed in `lean.declarations`.
No independent notion, new node, dependency repair, or statement correction is needed.
There was no repair note for this item.

Source read: HTT Proposition the project server, Remark the project server, and Corollary the project server,
printed pp. 249--253, online at
https://people.math.harvard.edu/~lurie/papers/HTT.pdf. In particular, Remark the project server
identifies directed unions of subsets as satisfying the contractible-support condition;
Corollary the project server identifies colimits of the original and assembled diagrams.
The statement uses the existing fat coherent comma-cocone model. Incidence prisms
express the mixed-block data of HTT's join model without choosing a join comparison
from an unproved existence theorem. The theorem's docstring carries all six proof steps
and the dependency used in each step.

Hypotheses, one by one:

- The small simplicial set is `K : SSet.{u}`. Its subsets are the existing
  `U : I → K.Subcomplex`; Mathlib's `Subcomplex` is `Subfunctor`.
- The small partially ordered index is `I : Type u` with `[PartialOrder I]`.
  `[Nonempty I]` and `hdir : Directed (· ≤ ·) (fun i : I ↦ i)` say precisely that
  every finite subset has an upper bound, including the empty finite subset.
  Pairwise upper bounds plus nonemptiness imply finite upper bounds by induction.
- `hmono : Monotone U` is the specified inclusion for `i ≤ j`.
  `hcover : iSup U = ⊤` says that every simplex in every degree belongs to some stage.
- `E : SSet.{max u v}` with `[Quasicategory E]` is the infinity category. The two
  universes are independent: indexing shapes are in `u`, while the target can be larger.
  `SSet.uliftFunctor.{v}` merely embeds the small shapes and maps degreewise into the
  ambient universe. It imposes no equality of size universes.
- `hcolimits` quantifies over every `L : SSet.{u}` and every coherent diagram from its
  canonical lift, and supplies a vertex of its existing `coconeCategory` satisfying
  `IsColimiting`. This is exactly existence of all small coherent colimits, including
  the empty shape, without selecting data from that existence hypothesis in a definition.
- `p` is a simplicial map from the lifted `K` into `E`.
- `q i` is the entire prescribed coherent cocone on
  `SSet.uliftFunctor.map (U i).ι ≫ p`; its apex is `(q i).1.1`.
  `hq i` says that this specified cocone is colimiting.

Conclusion clauses, one by one:

- `c : SSet.uliftFunctor.obj (nerve I) ⟶ E` is the coherent apex diagram, retaining
  all simplices of the index nerve. Its vertex equation sets its value at `i` equal
  to the given apex `(q i).1.1`, not an unrelated equivalent object.
- `directedCoverIncidence U` has degree-n elements `(x, chain)` with `x ∈ U (chain j)`
  for every vertex `j`. For a monotone family, this is exactly membership at the first
  vertex. Thus a chain `i₀ ≤ ... ≤ iₙ` supplies the whole `K_i₀ × Δ[n]` family.
  Closure under operators is proved directly from subfunctor closure, with no theorem
  placeholder and no chosen filler. The two projections retain respectively `x` and
  `chain`. `directedCoverFiber U i` sends a simplex to itself paired with the constant
  chain at `i`.
- `a` is one transformation on this entire incidence set. Its endpoint equations say
  that it goes from the original diagram, pulled back along the shape projection, to
  `c`, pulled back along the index projection. Its local-fiber equation identifies the
  entire transformation at each stage with `coconeHomotopy ... (q i)`.
  On a chain `i ≤ j`, this is a coherent family of local cocones between those at its
  endpoints. Hence the edge `c_i → c_j` is induced by the given cocone on `K_i` and the
  restriction of the given cocone on `K_j`. The family over longer chains retains every
  higher compatibility; it is stronger data than bare pairwise apex arrows, but exactly
  a representation of the coherent assembly requested by the node.
- `l : (coconeCategory p) _⦋0⦌` with `IsColimiting p l` realizes `colim_K p`.
  This is existentially supplied as a cocone, not a hollow chosen colimit definition.
- `ν : (coconeCategory c) _⦋0⦌` is the compatible cocone on the assembled diagram;
  `ν.1.1 = l.1.1` makes its apex the same global colimit object.
- Compatibility with the global cocone is the triangle `t` on the whole incidence set.
  Its `δ₂` edge is `a`; its `δ₀` edge is the pullback of the transformation of `ν`;
  its `δ₁` edge is the pullback of the transformation of `l`. This represents the
  composition triangle and all higher compatibilities simultaneously, rather than
  an equality only on homotopy classes or an arbitrary comparison map.
- `IsColimiting c ν` says this very compatible cocone is colimiting. Since its apex is
  exactly the apex of `l`, this also states `colim_i c_i ≃ colim_K p` without choosing
  a second colimit or adding a redundant arbitrary equivalence.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.coconeCategory` and
  `SSet.Enhanced.IsColimiting`, with their complete explicit degreewise pullback and
  initial-object definitions read. The former stores an apex and the full internal-hom
  edge, and the latter tests outgoing right-pinched mapping spaces for contractibility.
- Mathlib `SSet`, `SSet.Subcomplex`, `SSet.uliftFunctor`, `CategoryTheory.nerve`,
  `SSet.ι₀`, `SSet.ι₁`, `SSet.stdSimplex.δ`, and the cartesian monoidal products.
  Read the signatures/docstrings of `SSet`, `degenerate`, `nonDegenerate`, `Subcomplex`,
  and `SSet.Finite` recorded by the simplicial-set dependency.
- The added already-landed statement dependency `lem-coef-infinity-final-index-colimit`
  supplies `SSet.Enhanced.coconeHomotopy` in
  `Sheaf.CategoryTheory.FinalIndexColimit`. Its signature and complete definition were
  read: it is exactly the uncurrying of the stored coherent transformation. The
  final-index theorem is not used, and its dependency closure does not contain this item.
  Adding this node uses the standing authorization for citing a landed helper's owner;
  no mathematical change to the statement or proof is made.
- All currently stated proof-dependency modules are imported non-publicly:
  `EnhancedFunctorConeCalculus`, `TerminalBoundaryExtension`,
  `FilteredNerveWeakContractibility`, `RightAnodyne`, `AnodyneCocones`,
  `TrivialKanHomotopyEquivalence`, and Mathlib's `Skeleton` and
  `CategoryWithFibrations`. The three proof nodes for the join-slice comparison,
  opposite relative-cone equivalence, and contractible-join right-anodyne lemma currently
  have no declaration, so there is no module to import for them.

Edge cases checked:

- `K = ∅`: all local shapes and the incidence set are empty. `q i` specifies an
  initial apex. The vertex equation still fixes all these apices, while the coherence
  equations on the incidence set impose no spurious inhabitance condition. The theorem
  still requires the coherent diagram and its colimiting cocone at the initial global
  colimit. Nonemptiness and directedness of `I` ensure its nerve is contractible.
- Empty individual `K_i` are allowed: the local-fiber equation is vacuous on the
  transformation, but the separate vertex equation retains that prescribed initial apex.
- A one-element index forces `U i = ⊤`; the statement compares the given colimit with
  itself by a coherent cocone at the same apex. No nontrivial transition is demanded.
- Repeated stages and identity chains are allowed. The nerve and incidence construction
  include all degeneracies, so the coherence data enforce their usual identities.
- An empty index is explicitly excluded as in the node. No finiteness of the shape or
  its subsets, ordinary-category restriction on the target, or extra preservation
  hypothesis is present. The ambient simplicial set may live in any larger universe.

Searches performed for this task:

- `msearch.py ... leanfinder "A colimit over a directed union of simplicial subsets is
  the colimit of their local coherent colimits"`: eight hits, principally
  `SSet.Subcomplex.MulticoequalizerDiagram.isColimit[']`, `SSet.hasColimits`,
  `SSet.horn.isColimit`, and filtered-colimit stability of simplicial monomorphisms.
  Their signatures concern colimits in the ambient ordinary category of simplicial
  sets, not coherent diagrams in an arbitrary quasicategory; no exact match.
- `msearch.py ... loogle '"colimit", "directed"'`: twelve hits, on scheme gluing and
  ordinary cardinal-directed-poset colimits. Their signatures do not state this result.
- `msearch.py ... grep 'colimit|directed|cofinal' AlgebraicTopology/Quasicategory`:
  zero hits.
- `msearch.py ... leansearch "Coherent colimits assemble over a directed union of
  simplicial indexing subsets"`: eight hits on ordinary simplicial-object colimits,
  `SSet.hasColimits`, scheme gluing and truncated simplicial sets; no exact match.
- `rg` in upstream `WeilConjectures` and side-project `lean/Sheaf` for
  `directedCover|directed.cover|colimitAssembly|lem-coef-directed-cover-colimit-assembly`:
  only unrelated scheme covers, field/ring directed covers and tensor-colimit results.
  Additional searches for coherent cocone restriction and homotopies found the reusable
  `coconeHomotopy` helper above, which is imported rather than defined again.
- `rg` for all new declaration names in Mathlib, upstream `WeilConjectures`,
  side-project `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collisions.

Validation: the prescribed `scompile.py Q03 lem-coef-directed-cover-colimit-assembly`
compiled the sandbox file and its library-module form cleanly (2.9 s and 3.7 s);
all variables and universes are bound explicitly. The only postponed declaration is
`SSet.Enhanced.directed_cover_colimit_assembly`, with the DAG-matching proof docstring.
No disputed statement or source fault was found.

## Second reading by Q03

I read the item record, its source place (HTT Proposition the project server, Remark the project server,
and Corollary the project server), the dependency declarations, and the complete Lean module.
The item statement and the signature agree clause by clause:

- `K : SSet.{u}` is the small simplicial shape; `I : Type u` with
  `[PartialOrder I] [Nonempty I]` and `hdir : Directed (· ≤ ·) ...` expresses a
  nonempty directed poset, hence upper bounds for every finite subset.
- `U : I → K.Subcomplex`, `hmono : Monotone U`, and `hcover : iSup U = ⊤` are
  exactly the monotone simplicial-subset family and its union-cover hypothesis.
- `E : SSet.{max u v}` with `[Quasicategory E]` is the target infinity category;
  the independent ambient universe is retained by `SSet.uliftFunctor.{v}`.
- `hcolimits` supplies a colimiting coherent cocone for every required small shape
  `L : SSet.{u}`.  `p` is the coherent diagram on `K`; `q i` and `hq i` are the
  prescribed colimiting cocone and its universal-property proof on `U i`.
- The witnesses `c`, `a`, `l`, and `ν` render respectively the coherent diagram on
  `nerve I`, the full incidence transformation from the `K` projection to the index
  projection, the global colimiting cocone, and the assembled cocone.
- The vertex equation identifies `c_i` with `(q i).1.1`; the two endpoint equations
  identify `a` with the two incidence projections; and the fiber equation identifies
  every local restriction with `coconeHomotopy ... (q i)`.
- `IsColimiting p l` and `IsColimiting c ν`, together with `ν.1.1 = l.1.1`, give
  the global colimit and the colimit of the assembled diagram on the same apex.
  The final `t : incidence ⊗ Δ[2] ⟶ E` and its three face equations record the
  complete compatibility triangle, including higher coherence.

The four helper definitions are real canonical data: `directedCoverIncidence` is
the all-vertices incidence subcomplex, `directedCoverToShape` and
`directedCoverToIndex` are its projections, and `directedCoverFiber` is the constant
chain inclusion of each local subset.  They do not add hypotheses or alter the node's
objects.  The source's directed-support condition is exactly the `hdir` plus `hcover`
case (the support of each simplex is nonempty and upward closed).  No dependency
module is missing or unusable; the recorded declarations
`SSet.Enhanced.coconeCategory`, `SSet.Enhanced.IsColimiting`, and
`SSet.Enhanced.coconeHomotopy` have the required coherent comma-category meanings.

Edge cases were checked explicitly.  `K = ∅` makes every local shape and the
incidence subcomplex empty while leaving the prescribed local apexes and the nerve
diagram; `a` and `t` then have empty domain.  Empty individual `U i`, identity and
repeated chains, a one-element directed index, and dimension-zero simplices are all
handled by the definitions.  The nonempty index hypothesis covers the empty finite
subset, and no finiteness, Noetherian, characteristic, or extra target assumption is
present.  The index and target universes remain independent as required.

I repeated the existing-notion searches with LeanFinder, Loogle, LeanSearch, and
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`; all hits were ordinary
simplicial-set or ordinary-category colimits, with no exact coherent infinity-
categorical assembly declaration.  There is therefore no existing declaration to
record and no new definition node or dependency repair to add.

No mismatch was found, so no statement, helper, dependency, or proof-docstring
change was necessary.  The prescribed `scompile.py` run compiled the sandbox and
library forms cleanly; all binders and universes are explicit and the only warning is
the permitted theorem `sorry`.
