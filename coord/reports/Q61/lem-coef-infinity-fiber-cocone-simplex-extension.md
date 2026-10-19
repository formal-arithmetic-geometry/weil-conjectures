## Worker report

The module `Sheaf.CategoryTheory.FiberCoconeSimplexExtension` states
`CategoryTheory.fiber_cocone_simplex_extension`. Its proof is `sorry`; it is the
only postponed theorem. Four auxiliary constructions implement the objects
introduced in this very node. No new DAG notion or dependency repair is needed,
and the node is unchanged except for its `lean` record. Every helper has a
source/blueprint docstring and real construction data. There is no
`STATEMENT-DISPUTED` issue.

The previous sandbox draft was not ready: it assumed existence of some
colimiting cocone without identifying it with the cocone prescribed by `F`.
That is insufficient for the exact boundary-extension claim. This revision
adds the prescribed apex and entire transformation equations, removes redundant
preorder instances, reuses Mathlib's boundary through its existing nerve
isomorphism, supplies every declaration's docstring and the six-step proof
plan, and regenerates the node record from the repository's current node.
This repairs the Lean rendering; it does not correct or change the DAG statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `n : ℕ` and `hn : 1 ≤ n` are exactly the positive dimension assumption.
  `simplexIndex.{u} n` abbreviates `ULift.{u} (Fin (n+1))`, with Mathlib's
  existing order and preorder-category instances. This is the ordered category
  with vertices zero through `n`, placed in the common containing universe.
- `V : simplexIndex.{u} n ⥤ Cat.{u,u}` is the strict functor to small ordinary
  categories. No preservation property is imposed on its transition functors.
- `Grothendieck V`, used by the published `Collage`, is the displayed `K_V`.
  Its objects have fields `base`, `fiber`; its homs have fields `base`, `fiber`.
  The fiber hom is from the transported source to the target. Its composition
  is the one specified by the node, using the strict functor laws.
- `Collage (simplexIndex n) V` is the displayed `P_V`: its old and new objects
  are the two disjoint summands; its hom constructors are `left`, `mixed`,
  `right`, and there is no constructor from right to left. `mixed` is a base
  hom, which is a singleton precisely when the base inequality holds, and is
  empty otherwise. The published category instance uses base projection in
  mixed composition. `collageProjection` is precisely `π_V`.
- `simplexBoundary n` is the preimage of `SSet.boundary n` under
  `(SSet.stdSimplex.isoNerve n).inv`. Thus it is Mathlib's union of proper
  faces transported to `N([n])`. The isomorphism takes an ordinal-nerve chain
  to its monotone vertex map, so membership is exactly omission of a vertex.
- `simplexBoundaryCollage V` is the supremum of the range of
  `nerveMap collageLeft` and the preimage of that boundary under
  `nerveMap collageProjection`. Because `collageLeft` is the inclusion of
  the full old summand, its range is exactly `N(K_V)`. The supremum is the
  degreewise union, so this is exactly `B_V`, including the overlap.
- `{E : SSet.{u}} [E.Quasicategory]` is the arbitrary quasicategory target.
  The single universe is a containing universe for every small category and
  simplicial set under discussion, as stipulated in the node.
- `F : (simplexBoundaryCollage V : SSet) ⟶ E` is the entire prescribed map.
  `simplexFiberMap V r` is the canonical nerve fiber inclusion, factored
  through the old summand's range in `B_V`. Thus its composite with `F` is
  exactly the specified restricted diagram on `N(V(r))`.
- `hcolim` quantifies over every vertex `r` and supplies a vertex `c` of the
  recorded coherent `coconeCategory` on that restricted diagram.
  `IsColimiting ... c` asserts that this cocone is initial in the coherent
  cocone category, exactly the node's colimit convention.
- The first conjunct of `hcolim` identifies `c.1.1`, its apex, with the value
  of `F` at the new vertex `r`, represented by
  `(nerveMap collageRight).app (op ⦋0⦌) (ComposableArrows.mk₀ r)`.
  The last conjunct identifies `coconeHomotopy ... c` in every degree `m`
  and on every `(s,a)` with `F` applied to the canonical
  `collageFiberPrism V r`. That prism sends time zero to the old fiber and
  time one to the new final vertex, including mixed arrows and every higher
  simplex. It is precisely precomposition through `N(V(r)^▹)` in the node.
- Each existential `b` in these two conjuncts is a simplex of the subtype
  `B_V` whose underlying simplex is the specified canonical vertex or prism
  simplex. These are uniquely determined as subtype elements. For `n ≥ 1`
  they exist automatically: their projection is constant at `r`, omitting
  at least one of the `n+1` base vertices. Hence these equations express
  restriction of the actual prescribed map, without an extra mathematical
  hypothesis or an arbitrary comparison map. This formulation avoids any
  choice of an unspecified cone or replacement up to equivalence.
- The conclusion supplies `Fbar : nerve (Collage ...) ⟶ E` and the literal
  simplicial equality `(simplexBoundaryCollage V).ι ≫ Fbar = F`. It fixes all
  of `B_V`, hence its entire boundary preimage and every prescribed fiber
  cone, in every degree. There is no conclusion merely up to equivalence.

Dependency declarations inspected and used:

- `def-cbc-enhanced-diagrams-cones` is recorded in
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its full comma-cone
  definitions and docstrings were read, especially
  `SSet.Enhanced.coconeCategory`, `IsColimiting`, and `IsInitial`.
  The definition module is publicly available through the collage import.
- The canonical constructions already published in
  `Sheaf.CategoryTheory.FiberColimitCollage` were read in full:
  `CategoryTheory.Collage`, `CollageHom`, `instCategoryCollage`,
  `collageProjection`, `collageLeft`, `collageRight`, `collageFiber`, and
  `collageFiberPrism` with its ordinary prism functor. They are reused, not
  redefined. Only these constructions are used; the parent theorem
  `fiber_colimit_collage` is not an assumption of our theorem or its proof.
- The published projection `SSet.Enhanced.coconeHomotopy` from
  `Sheaf.CategoryTheory.FinalIndexColimit` was read and is reused through
  the collage module. It extracts the whole coherent transformation.
- Mathlib supplies `CategoryTheory.Grothendieck`, `nerve`, `nerveMap`,
  `SSet.boundary`, `SSet.stdSimplex.isoNerve`, `SSet.Subcomplex.range`,
  `preimage`, `lift`, `range_comp`, and `image_le_range`. The helper's
  range-inclusion verification just applies these existing operations.
- Stated proof dependencies `def-coef-infinity-fibrations` and
  `lem-coef-infinity-cocone-restriction-initial` are imported nonpublicly
  from `Sheaf.CategoryTheory.InfinityFibrations` and
  `Sheaf.CategoryTheory.CoconeRestrictionInitial`. Their complete
  signatures/docstrings were inspected. The latter's apex and prism
  characterization is consistent with this statement.
- The other proof dependencies `lem-coef-infinity-relative-exponential-restriction`,
  `lem-cbc-enhanced-relative-exponential`, and
  `lem-coef-infinity-cartesian-initial-boundary-lift` have no Lean records
  in the current DAG; no import can yet be supplied for them. Their role is
  retained in the theorem's six-step natural-language proof.
- Import-cycle note for later proof-import maintenance: the parent
  `FiberColimitCollage` module owns the canonical helpers this file imports.
  Adding this file as a proof import back into that module would create a
  module cycle. Under stages/2-statements.md §3(7), that parent proof import
  must be omitted. No new DAG edge to the parent is introduced.

Edge cases checked before finishing:

- At `n=1`, the boundary consists of the two constant base fibers, including
  their old-to-new cone simplices, but omits a chain visiting both vertices.
  The prescribed colimits constrain exactly those cones, not a nonexistent
  transition-colimit preservation property.
- For higher dimensions, a chain belongs to the boundary iff it omits a
  base vertex; repeated vertices and degenerate simplices are retained.
- For an empty fiber, the prism equation has no input simplex, but the
  separate apex equation still fixes the new vertex. The colimit condition
  then says that the specified apex is initial. The old draft's omission
  of this apex identity has been repaired.
- No nonemptiness of a fiber or of `E` is imposed. If `E` is empty, no map
  `F` from this nonempty prescribed domain exists; the universal theorem
  handles that case correctly. The statement excludes `n=0` exactly as
  the node/source do: its boundary would not contain the new vertex.
- No local instances, file-local notations, private definitions, unbound
  implicit variables, or universe equalities were introduced.

Source read: https://kerodon.net/tag/02ZR, Lemma the project server and its full proof,
including the prescribed lifting square (7.21), vertex colimit condition,
relative functor categories (7.22), and exact filler. The blueprint's current
`prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2, and the unit
`sk-prop-sf-biduality-general/_section.md` were also read. No source-based
correction is required.

Searches performed in this repair (in addition to the preserved node searches):

- `msearch.py leanfinder`, query "Prescribed fiber colimit cocones extend over
  a Grothendieck collage over a simplex with its entire boundary fixed": eight
  hits, including subcomplex/horn colimit constructions and ordinary
  `coconeOfCoconeFiberwiseColimit` / `isColimitCoconeOfFiberwiseCocone`.
  Their signatures do not state quasicategory-valued exact relative extension.
  Mathlib's ordinary Grothendieck fiberwise-colimit source was inspected;
  it assumes an ordinary target category and ordinary colimits.
- `msearch.py loogle`, query `SSet.Quasicategory, SSet.Subcomplex`: zero hits.
- `msearch.py grep`, query `collage|relativeJoin|fiber.*[Cc]olimit` in
  `AlgebraicTopology`: zero hits.
- `msearch.py leansearch`, query "A diagram on the boundary of a Grothendieck
  collage extends relative to specified colimiting fiber cocones": rate
  limited; no verdict was based on that unavailable response.
- A subsequent `msearch.py leansearch`, query "Extend a coherent diagram
  across a simplex relative to its boundary using prescribed colimiting
  fiber cocones": eight hits, all ordinary cocone extensions or ordinary
  fiberwise colimits, not the statement here.
- `rg` in the named upstream `WeilConjectures` source and the project's
  `lean/Sheaf`, for the item id, `fiber_cocone_simplex_extension`,
  `simplexIndex`, `simplexBoundary`, `simplexFiberMap`, and
  `collageFiberPrism`: no existing item/helper-name collision; the canonical
  prism helpers are in `FiberColimitCollage` and were reused.
  The upstream name inventory was also checked for the new names, with no
  matches. Searches of Mathlib's Nerve/StdSimplex/Boundary sources located
  `stdSimplex.isoNerve` and `boundary`, which are used directly.

Validation: compile each delivered file with the prescribed `scompile.py` wrapper;
run `deliver2.py Q61 lem-coef-infinity-fiber-cocone-simplex-extension --no-push`.
The second reading is intentionally left to the independently started reader.

## Second reading by Q61

I read the node, the Kerodon source at tag 02ZR (Lemma the project server), the recorded
dependency declarations, and the complete module independently. The source's
lifting problem specializes to the nerve of the displayed split Grothendieck
collage over Δ^n, with the boundary subset and target over a point. The node
records the stronger all-vertex prescribed-cocone interface used by its parent;
the Lean statement matches that node verbatim.

Object and hypothesis checklist:

- `n : ℕ`, `hn : 1 ≤ n`: the positive simplex dimension; `simplexIndex.{u} n`
  is `ULift (Fin (n+1))`, giving the ordered category `[n]` in the common
  universe.
- `V : simplexIndex.{u} n ⤒ Cat.{u,u}`: the strict diagram of small ordinary
  categories. `Grothendieck V` is `K_V`, with the stated `(base,fiber)` objects
  and transported fiber morphisms.
- `Collage (simplexIndex n) V` and `collageProjection`: the disjoint old and
  right copies, mixed arrows exactly when the base order admits them, no
  right-to-old arrows, and the projection π_V. `collageLeft` and
  `collageRight` render the two inclusions.
- `simplexBoundary n` is Mathlib's union of proper faces transported through
  `stdSimplex.isoNerve`; `simplexBoundaryCollage` is precisely
  `N(K_V) ∪ (Nπ_V)^{-1}(∂Δ^n)`. `simplexFiberMap` is the canonical inclusion
  of `N(V(r))` into this subcomplex.
- `{E : SSet.{u}} [E.Quasicategory]` and `F` render the quasicategory target and
  the complete prescribed map `F : B_V → E`.
- `hcolim` quantifies over every vertex `r`, supplies a cocone `c` for the exact
  restricted diagram, identifies its apex with `F` at the right-copy vertex,
  asserts `IsColimiting`, and gives the prism equation in every simplicial
  degree and for every fiber simplex and interval simplex. The subtype
  witnesses `b` are the canonical members of `B_V`; they add no arbitrary map
  or comparison datum.
- The conclusion is an `Fbar : nerve (Collage ...) → E` with the literal
  equality `(simplexBoundaryCollage V).ι ≫ Fbar = F`, so all boundary and fiber
  data are fixed exactly.

No mismatch was found. In particular, the apex equation and the degreewise
prism equation retain the empty-fiber case; no transition-functor colimit
preservation, nonemptiness, Noetherianity, characteristic, or universe equality
is assumed. The conclusion is neither weakened nor strengthened relative to the
node. The node's `lean.statement` is byte-for-byte equal to the theorem
signature in the module. All helper definitions have real construction data,
and the only proof hole is the named theorem's `sorry`.

Edge checks: `n = 0` is excluded by `hn`, as in the node; `n = 1` gives the two
proper-face fibers and the mixed cone simplices; repeated and degenerate chains
remain in the transported boundary; empty fibers are handled by the explicit
apex and prism clauses; an empty target admits no `F`, so the quantified theorem
has the correct vacuous behavior; zero or empty fiber categories introduce no
additional hypothesis. The `ULift` index and common `u` cover all vertices and
small categories without an unbound universe.

Existing-definition searches were repeated with `msearch.py` and `rg`: LeanFinder
for a prescribed fiber-colimit extension returned only ordinary subcomplex
colimits and ordinary Grothendieck fiberwise-colimit declarations; Loogle for
`SSet.Quasicategory, SSet.Subcomplex` returned no hits; grep for
`collage|relativeJoin|fiber.*[Cc]olimit` in Mathlib's AlgebraicTopology returned
none. Searches of the named upstream `WeilConjectures` tree and the project's
`lean/Sheaf` found no item or helper-name collision; the canonical collage and
prism declarations are the published dependency and are reused. No dependency
record was unusable and no new node or statement correction was required.

The module compiled cleanly with
`scompile.py Q61 lem-coef-infinity-fiber-cocone-simplex-extension` (sandbox and
library checks, no errors). The only change made by this second reading is this
independent verification report; the worker's Lean module and node statement
remain unchanged.
