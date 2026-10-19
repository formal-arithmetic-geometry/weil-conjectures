## Worker report

Item: `def-coef-infinity-relative-join`. Module:
`lean/Sheaf/CategoryTheory/RelativeJoin.lean`.
Main declaration: `SSet.Enhanced.relativeJoin`.

The module defines the relative join as a literal degreewise pullback, together
with every map and identification requested in the node. The mathematical
statement is unchanged. The only additional statement dependency is the already
landed `lem-coef-infinity-blunt-sharp-join-equivalence`, because its helper
`bluntSharpCylinderSimplex` already constructs precisely the interval-splitting
simplex needed here. No notion is copied or replaced. There are no new nodes or
dependency record repairs.

Source read: Kerodon Construction the project server, tag 0242, and Remark the project server,
tag 0234. The latter identifies maps into a join with their block parameter
and the two restrictions. The online source confirms that the relative join
is the specified pullback along the splitting map. Direct opening of tag 0242
timed out, but web search returned the construction text and its displayed
diagram; the subsection 0241 also supplies the construction.

Clause-by-clause correspondence:

- Fixed sufficiently large universe: one explicit `universe u`, with every
  simplicial set in `SSet.{u}`. No finiteness, nonemptiness, Kan or quasicategory
  hypothesis is imposed.
- Given `f:A→C` and `g:B→C`: explicit binders `{A B C : SSet.{u}}`,
  `(f : A ⟶ C)`, `(g : B ⟶ C)` in `relativeJoin` and its maps.
- Ordinary join and `f⋆g`: the existing `orderedJoinFunctor.obj (A,B)` and
  `orderedJoinFunctor.map (f,g)`. Terminal augmentation and its unique
  degree-minus-one simplex are inherited from that functor.
- Splitting map `ρ_C`: `relativeJoinRho C`, with actual component
  `bluntSharpCylinderSimplex C C n.unop s t s`. The imported helper first takes
  the convolution generator of `(s,s)` in the two full copies of `[n]`, then
  restricts it along `bluntSharpOrdinal`. That ordinal selects vertex `i` from
  the first copy when `t(i)=0`, otherwise from the second. The convolution
  normal form is exactly the restrictions of `s` to the initial zero block and
  final one block. Constant parameters give an empty block, with its unique
  terminal augmentation element.
- Pullback equation and simplices: `relativeJoinSubcomplex f g` is the
  subcomplex of `(A⋆B) ⊗ (Δ[1] ⊗ C)` defined by the equality
  `(orderedJoinFunctor.map (f,g)).app n x.1 = (relativeJoinRho C).app n x.2`.
  `relativeJoin` is its `toSSet`, so elements are literally the required pairs
  with an equality proof, not diagrams with additional coherence data.
- Operators: `Subfunctor.toFunctor` restricts each ambient product coordinate.
  Thus `((z,(t,s)),eq)` maps to `((α*z,(tα,α*s)),eq')`; the proof of closure
  uses naturality of the two displayed pullback maps. All faces and degeneracies
  are included.
- `p_C`: `relativeJoinProjection f g` is the second pullback projection
  `relativeJoinSnd f g` followed by the second cartesian projection. Its value
  is exactly `s`. `relativeJoinFst` also exposes the ordinary-join projection.
- Inclusions: `relativeJoinEndpoint C i` sends `s` to `(constant i,s)`;
  `relativeJoinInl` is the pullback lift of `orderedJoinInl A B` and
  `f ≫ relativeJoinEndpoint C 0`. `relativeJoinInr` uses `orderedJoinInr A B`
  and `g ≫ relativeJoinEndpoint C 1`. Consequently their literal values are
  `(ι_A(a),(0,f(a)))` and `(ι_B(b),(1,g(b)))`.
- Change of data: `relativeJoinMap` binds all six simplicial sets, all seven
  maps `f,g,f',g',a,b,h`, and exactly the commutativities
  `ha : a ≫ f' = f ≫ h`, `hb : b ≫ g' = g ≫ h`. The pullback lift uses
  `relativeJoinFst f g ≫ orderedJoinFunctor.map (a,b)` and
  `relativeJoinSnd f g ≫ (𝟙 Δ[1] ⊗ₘ h)`. It therefore sends a simplex to
  `((a⋆b)(z),(t,h(s)))` as required.
- Identity case: `relativeJoinIdentityIso C` has the second projection as its
  `hom`, and the pullback lift of `relativeJoinRho C` and the identity as its
  inverse. Its inverse has value `(ρ(t,s),(t,s))`; the stored inverse laws
  follow from the defining subtype equality and `orderedJoinFunctor.map_id`.
- Vertex copy and strict fiber: `relativeJoinFiber f c` is
  `pullback f (SSet.yonedaEquiv.symm c)` for an arbitrary vertex `c : C _⦋0⦌`.
  Its map to `A` is exactly `pullback.fst`; the other factor is `Δ[0]`.
- Join-block parameter: `joinBlockCollapse` collapses an augmented ordinal to
  `[0]`, including the unique arrow from the empty ordinal. `joinBlockWord`
  concatenates two such collapses to `[0]⋆[0]=[1]`, then precomposes with the
  representative's ordinal map. `existsUnique_joinBlockParameter` specifies
  this value on every convolution generator and every restriction. Thus
  `joinBlockParameter` is determined up to equality by a complete universal
  property, and its choice is not from mere existence or `Nonempty` data.
- Fiber cone: `relativeJoinFiberCone f c` has source
  `rightJoinCone (relativeJoinFiber f c)` and target `relativeJoin f (𝟙 C)`.
  Its first coordinate is `orderedJoinFunctor.map (pullback.fst ..., vertexMap)`;
  its second is the pair of `joinBlockParameter` and the constant map at `c`.
  The latter is the map to `Δ[0]` followed by `SSet.yonedaEquiv.symm c`, so its
  degree-n value is precisely the degenerate simplex `c_n`.
- Data only: no existence of a relative colimit, quasicategory structure,
  cofinality, or universal-cone assertion appears in any declaration.

Dependency declarations used (full signatures/docstrings read):

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the recorded `coneCategory`
  and its surrounding simplicial conventions; this item uses Mathlib's
  `SSet`, `stdSimplex`, degreewise cartesian tensor and pullbacks exposed by
  that module, as the dependency node prescribes.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `rightJoinCone`; its imported
  `orderedJoinFunctor`, `joinAugmentation`, `orderedJoinInl`, `orderedJoinInr`,
  `joinGenerator` are the existing ordinary join, augmentation and inclusions
  in `Sheaf.AlgebraicTopology.PushoutJoinSaturation` and
  `Sheaf.CategoryTheory.JoinSliceRightFibration`.
- `Sheaf.AlgebraicTopology.BluntSharpJoinEquivalence`:
  `bluntSharpOrdinal` and `bluntSharpCylinderSimplex`. Its owning recorded node
  has been added to `stmt_deps`, without changing its record. The theorem
  `blunt_sharp_join_equivalence` is not used to choose any construction data.
- Mathlib: `Subcomplex.lift`, cartesian `lift`, `fst`, `snd`,
  `SSet.yonedaEquiv`, `stdSimplex.isTerminalObj₀.from`, and `pullback.fst`.

The five postponed theorems are construction proof obligations for this
same definition node (all listed in `lean.declarations`), not additional
universal-cone or quasicategorical assertions:
`relativeJoinRho_naturality`, `relativeJoin_endpoints`,
`relativeJoinRho_natural`, `existsUnique_joinBlockParameter`, and
`relativeJoinFiberCone_compatible`. Each has a source/blueprint docstring
and a complete natural-language proof. Every theorem has exactly `by sorry`;
there is no `sorry` in a definition or a structure field. The first theorem
postpones only the naturality proof for explicit component data; the uniqueness
theorem determines the canonical block map up to equality, as required by
AGENTS.md section 5.

Edge cases checked before writing:

- Degree zero has exactly the two constant parameters; the two inclusions use
  the appropriate pure summands. There is no spurious mixed degree-zero term.
- Constant zero/one parameters and restrictions that erase either block use the
  terminal empty augmentation, not an assumed simplex of an empty factor.
- Empty `A` or `B` leaves the other pure factor; empty `A` and `B` leaves an
  empty pullback. No `Nonempty` assumption enters the parameter construction.
- Empty `C` forces both domains empty when the maps exist; the degreewise
  subtype and identity-base isomorphism still apply.
- The strict fiber can be empty; its right join cone retains the pure apex.
  The block-parameter universal property includes the empty first factor,
  and the fiber-cone formula still sends the apex to the right copy of `c`.
- Arbitrary base changes and the identity case retain all degenerate simplices.
- All objects can be raised to the fixed sufficiently large universe; no extra
  equality between independently specified universe levels is imposed.

Searches made through `msearch.py Q111 def-coef-infinity-relative-join`:

- `leanfinder`: "Relative join of simplicial sets as pullback along interval
  times base". Eight hits: Quillen generating maps, interval inclusions,
  circle, multicoequalizers, relative morphisms and pointed simplices. None
  defines this relative join.
- `loogle`: `"SSet", "join"`. Twelve hits, all unrelated neighborhood/disjointness
  declarations; no simplicial relative join.
- `grep`: `relativeJoin|relative.?[Jj]oin|joinMap` under AlgebraicTopology.
  Zero hits in Mathlib.
- `leansearch`: "Define the relative join of two simplicial sets over a base as
  the pullback along the interval splitting map". Eight hits: relative
  morphisms, finite pullbacks, and a convex join. Their returned full signatures
  do not define the requested simplicial construction.
- `rg` in the upstream `WeilConjectures` tree for relative-join names and the
  node id: no hits. `rg` in `lean/Sheaf`: only `FiberColimitCollage`'s source
  comment mentions a relative join, and its construction is an ordinary
  categorical collage, not this simplicial construction.
- Reading join-related modules found the reusable `bluntSharpCylinderSimplex`;
  it is used rather than duplicated. An exact-name search for every new helper
  in Mathlib, upstream and side `lean/Sheaf` returned no collisions.
- A read-only traversal of the existing DAG verified that the added landed
  dependency has no path back to this item (68 reachable nodes inspected).

Validation: the prescribed `scompile.py` compiled both sandbox and library
module forms cleanly (3.5 s and 3.4 s). `autoImplicit` is disabled, all universes
are explicit, and every source line is at most 100 characters.
No statement dispute or source-based correction was needed.

## Second reading by Q111

I independently opened the base node, the sandbox node and the entire delivered
module, then the statements and Lean records of all three statement dependencies.
I read `EnhancedDiagramsCones.lean`, `RelativeInfinityCone.lean`, the two explicit
helpers in `BluntSharpJoinEquivalence.lean`, and the augmentation, convolution
join, generator and pure inclusions in `PushoutJoinSaturation.lean` and
`JoinSliceRightFibration.lean`. There is one module and one node in the delivery;
there are no new nodes or dependency repairs. No repair-note file exists for this
item, and the sandbox has no `statement_change`.

Source reading: Kerodon Construction the project server
([0242](https://kerodon.net/tag/0242)) and Remark the project server
([0234](https://kerodon.net/tag/0234)), also read in the containing subsection
[0241](https://kerodon.net/tag/0241). The construction explicitly takes arbitrary
simplicial sets and maps, although the surrounding section later applies it to
quasicategories. The latter application's hypotheses do not belong to this
definition. Remark 0234 describes a map into a join by its interval parameter
and the maps on its zero and one fibers. This yields precisely the restrictions
in the node's splitting formula. These are Kerodon sources, not Stacks tags;
the node records its archival copy as wanted. A direct request for 0242 timed
out, but the search result returned its complete construction and pullback
diagram, and 0241 confirmed the construction and arbitrary-simplicial-set scope.

My object/hypothesis/clause checklist, in node order:

1. Arbitrary small simplicial sets in one containing universe: `universe u` and
   `{A B C : SSet.{u}}`. Verdict: exact. There is no quasicategory, Kan,
   nonempty, finite or extra universe-equality assumption.
2. Maps `f : A ⟶ C` and `g : B ⟶ C`: the explicit binders of `relativeJoin`.
   Verdict: exact; the dependency modules expose the existing Mathlib simplicial
   sets, standard simplices and degreewise cartesian products.
3. Ordinary join and the summand map `f ⋆ g`:
   `orderedJoinFunctor.obj (A, B)` and `orderedJoinFunctor.map (f, g)`.
   Verdict: exact. I checked that `joinAugmentation` is the right Kan extension
   assigning a singleton to the empty ordinal, and `orderedJoinFunctor` is its
   convolution along ordinal concatenation. Thus its map applies `f,g` to the
   respective blocks and the unique map to empty blocks. `rightJoinCone` is
   exactly that join with `Δ[0]`, with the apex last.
4. Splitting map `ρ_C`: `relativeJoinRho C` applies
   `bluntSharpCylinderSimplex C C n.unop s t s`. Verdict: exact. I read the
   helper's body: the ordinal selects `i` in the first copy if `t(i)=0` and
   `n.len+1+i` in the second otherwise. Restricting the generator of `(s,s)`
   therefore takes the initial zero restriction and final one restriction of
   the same simplex. For constant parameters one block is empty. This uses
   the existing helper, not the comparison-equivalence theorem to choose data.
5. Degreewise pullback equation and simplex coordinates:
   `relativeJoinSubcomplex` consists of ambient pairs `x=(z,(t,s))` satisfying
   `(orderedJoinFunctor.map (f,g)).app n x.1 = (relativeJoinRho C).app n x.2`;
   `relativeJoin` is its `toSSet`. Verdict: exact. The equality proof is the
   subtype membership proof, with no additional coherence datum or hypothesis.
6. Every monotone operator: the ambient cartesian product acts coordinatewise,
   and `Subcomplex.toSSet` restricts it to the displayed equality. Verdict:
   exact; naturality of both pullback arrows ensures closure, for faces and
   degeneracies alike. The result is `(α*z,(tα,α*s))` as in the node.
7. Structure map `p_C`: `relativeJoinProjection` is `relativeJoinSnd ≫ snd _ _`,
   so sends the subtype element to `s`. Verdict: exact. `relativeJoinFst`
   separately exposes `z` and `relativeJoinSnd` exposes `(t,s)`.
8. Pure inclusions: `relativeJoinInl` lifts `orderedJoinInl` and
   `f ≫ relativeJoinEndpoint C 0`; `relativeJoinInr` lifts `orderedJoinInr`
   and `g ≫ relativeJoinEndpoint C 1`. Verdict: exact. The endpoint component
   is `(constant i,s)`, and the existing pure inclusions use the unique
   augmented empty simplex. The resulting values are precisely the node's.
9. Primed maps and commuting triple: `relativeJoinMap` binds `f',g',a,b,h`
   after `f,g`, with `ha : a ≫ f' = f ≫ h` and
   `hb : b ≫ g' = g ≫ h`. Verdict: exact, including quantifier order and both
   equations. Its lift pairs the ordinary join map of `(a,b)` with
   `𝟙 Δ[1] ⊗ₘ h`, giving `((a ⋆ b)(z),(t,h(s)))`.
10. Identity case: `relativeJoinIdentityIso C` has the second projection as
    `hom`, and the lift of `relativeJoinRho C` and the identity as `inv`.
    Verdict: exact. Its two stored inverse laws use the subtype equation and
    the join functor's identity law; the inverse is `(ρ(t,s),(t,s))`.
11. Vertex copy and strict fiber: `relativeJoinFiber f c` is
    `pullback f (SSet.yonedaEquiv.symm c)`, for `c : C _⦋0⦌`.
    Verdict: exact. Yoneda supplies the copy of `Δ[0]` at the vertex, and
    `pullback.fst` supplies `r`; this is a strict fiber, not a path fiber.
12. Fiber-cone interval coordinate: `joinBlockCollapse`, `joinBlockWord` and
    `existsUnique_joinBlockParameter` specify the zero/one word on every
    augmented convolution generator and every restriction by `q`. Verdict:
    exact. Collapsing each block to `[0]` concatenates to `[1]`. The empty
    ordinal has its unique collapse too. The complete uniqueness property
    determines `joinBlockParameter` up to equality, so its `Classical.choose`
    is permitted construction data, rather than a choice from mere existence.
13. Fiber-cone source, target and formula: `relativeJoinFiberCone f c` has
    source `rightJoinCone (relativeJoinFiber f c)` and target
    `relativeJoin f (𝟙 C)`. Its lift uses the join map of
    `(pullback.fst ..., SSet.yonedaEquiv.symm c)` and the pair of
    `joinBlockParameter` with the terminal map followed by the vertex map.
    Verdict: exact. These are `((r ⋆ c)(w),(t,c_n))`, with the compatibility
    proved later by the named theorem `relativeJoinFiberCone_compatible`.
14. Data only: no colimit, quasicategory, cofinality or universal-cone assertion
    is added. Verdict: exact. The five sorry theorems are precisely simplicial
    naturality/endpoint/functoriality, block-parameter uniqueness and the
    fiber-cone compatibility needed by these construction formulas.

Edge-case inspection: in degree zero a monotone parameter is constant, giving
exactly the two pure vertex copies and no mixed vertex. In degree one the mixed
edge has `f(a)` as its initial base vertex and `g(b)` as its final base vertex;
the orientation is correct. Restrictions can erase either block and use the
terminal augmentation's unique empty element. An empty first or second factor
retains the other pure factor; both empty factors give an empty relative join.
An empty base forces its mapped domains empty, with the identity isomorphism
still valid. An empty strict fiber retains the apex of its right cone and maps
it to the right vertex `c`. For `C=Δ[0]`, the equation yields the ordinary join.
No empty index, zero object, scheme or characteristic hypothesis occurs in this
simplicial definition. The parameterization allows every `u`, including `u=0`,
and all objects inhabit the same fixed containing universe as the node requires.

Independent searches, using vocabulary different from the author's searches:

- `msearch.py ... leansearch "Simplicial ordered join relative to a base by
  pulling back a cylinder splitting morphism"`: eight hits, all
  `SimplicialObject.Split`/`Splitting` declarations. I opened
  `Mathlib/AlgebraicTopology/SimplicialObject/Split.lean`; these split a
  simplicial object into nondegenerate pieces, not this relative join.
- `msearch.py ... leanfinder "Fiberwise join of simplicial sets using an
  interval and a common base"`: eight hits, namely Quillen horn generators,
  the simplicial circle, cylinder endpoints, strict Segal concatenation,
  truncated path concatenation, colimits, and finite coproducts. Their returned
  signatures are not maps or constructions of the specified relative join.
- `msearch.py ... grep
  "fiberwiseJoin|fibrewiseJoin|joinOver|join_over|relativeJoin|relative_join"`:
  zero Mathlib hits. Independent `rg` on Mathlib, upstream `WeilConjectures`
  and project `lean/Sheaf` with those names and `relative join` found only
  `FiberColimitCollage.lean`'s source comment. That module's collage is an
  ordinary categorical construction, not a duplicate. A further block,
  parameter, interval and projection search found the already reused
  blunt-to-sharp helper and blunt-join projections, not a block-parameter
  map on arbitrary sharp joins. I also opened Mathlib's `RelativeMorphism`:
  it fixes a map on subcomplexes and is not a relative join.

I verified that the only node changes are `lean` and the addition of the
already landed owner of `bluntSharpCylinderSimplex` to `stmt_deps`; no source
statement is changed. I traversed the resulting 135-node dependency closure:
there is no path back to this item. All delivered declarations are recorded in
`lean.declarations`. Every theorem has a whole `sorry` proof and a source,
blueprint and detailed proof docstring. Definitions have explicit data or,
only for the interval map, data determined by a complete uniqueness property.
All universes and variables are bound (`autoImplicit false`); no file-local
notation, private notion, prefix collision or overlong Lean line was found.
The node's `lean.statement` is the exact signature read from `relativeJoin`.

Mismatch and repair: the module docstring lacked the multi-declaration
`Main definitions` index required by brief §3. I added that index only.
There was no mathematical mismatch, so all definitions, theorem signatures,
construction bodies and the node record were left intact. The independent
clause-by-clause review above is appended without replacing `Worker report`.

Validation: the prescribed `scompile.py` compiled the single delivered module
in sandbox and library forms cleanly (1.9 s and 2.1 s before the docstring-only
edit). The final file is compiled again by the prescribed wrapper and checked
by `deliver2.py --no-push` before delivery.
