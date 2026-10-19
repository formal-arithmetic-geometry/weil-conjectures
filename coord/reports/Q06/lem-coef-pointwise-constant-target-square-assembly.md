## Worker report

The module `Sheaf.CategoryTheory.PointwiseConstantTargetSquareAssembly` states
`SSet.Enhanced.pointwise_constant_target_square_assembly`, with one `sorry` and no
other postponed theorem. All five helpers have explicit data. No node statement or
dependency is changed, and no new node or dependency module is needed.

The main interface uses the canonical cylinder roof for composition. This matters:
there is no strictly functorial composition operation on the dependency's right-pinched
simplicial mapping spaces. Replacing it with arbitrary horizontal maps, or requiring
strict equality of chosen compositions after applying r, would change the statement.
Here every map in the roof is restriction or postcomposition, so the canonical
commutation homotopy is retained by an actual transformation cylinder.

For `p : L ⟶ H`, write M for the pushout `(L × Δ[1]) ⨿[L × {1}] H`.
`constantTargetCylinder p` is this actual categorical pushout.
`constantTargetCylinderDiagram p a f α` is its unique map d to X, equal to α.h on
the whole cylinder and to a on H. Its zero-end restriction is f, by α.h₀ and the
pushout equation. `constantTargetCylinderBase p` is that zero-end inclusion.
`constantTargetCylinderVertex b` is the unique pushout map induced on the cylinder by
`k ↦ (b,k)` and on the endpoint by `b : Δ[0] ⟶ B`. The definition specifies both
coordinates and proves the gluing equations with real proofs.

The square `ConstantTargetRestrictionSquare r i d w` has upper-left corner
`Map_Fun(M,X)(d, Δ_M w)`, upper-right the restriction to L, and the corresponding
Y-corners. Every mapping space is the recorded right-pinched `mappingSpace`, not its
set of components. The horizontal maps are `mappingSpaceMap ((MonoidalClosed.pre i).app _)`;
the vertical maps are `mappingSpaceMap ((ihom _).map r)`. The homotopy-pullback test is
the recorded `IsHomotopyPullbackSquare`, hence uses the full path pullback and the
actual constant-path comparison of this strictly commuting restriction square.

To read this roof as the displayed composition square, restriction along `H → M`
gives natural equivalences
`Map_Fun(M,X)(d, Δ_M w) ≃ Map_Fun(H,X)(a, Δ_H w)`, and likewise for Y.
For completeness, this equivalence has the following explicit mapping-space argument.
Fix a coherent transformation u from a to the constant w. Over u, a map from d to
constant w is the family of coherent composition triangles with edges α and p*u.
Restriction of `Fun(Δ[2],D)` to its inner composition horn, with these two edges fixed,
is a trivial Kan fibration on these fixed-endpoint arrow spaces. Its fibers are
contractible, including all higher parameter simplices. Thus forgetting the triangles
is an equivalence. Equivalently, in the contravariant space-valued mapping diagram
on M, a section over H extends over each attached cylinder as a path with one endpoint
fixed. This extension space is contractible. These descriptions are natural in r.
Under this equivalence zero-end restriction is precisely composition with α, and the
strict commutation upstairs transports to the canonical commutation homotopy downstairs.
The natural pinch comparison identifies the arrow-space calculation with the exact
right-pinched spaces used in the file. The cylinder roof therefore represents the
same specified square; it is not a new hypothesis or a weakening of its pullback test.

Hypotheses and clauses, individually:

- The two quasicategories are `{X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]`.
  The arbitrary enhanced functor is `(r : X ⟶ Y)`; no fibration instance is requested.
- The two small simplicial shapes are `{B K : SSet.{u}}`. The universe u is arbitrary;
  one common sufficiently large universe contains the shapes and both categories.
  Neither shape has a nonemptiness, Kan, or quasicategory assumption.
- The two coherent diagrams are `(a : B ⟶ X)` and `(f : B ⊗ K ⟶ X)`. Mathlib's
  cartesian tensor is the degreewise product, so `fst B K` is exactly pr_B.
- The supplied coherent transformation is `(α : SSet.Homotopy f (fst B K ≫ a))`.
  Despite its library name, `SSet.Homotopy` is simply a map
  `(B ⊗ K) ⊗ Δ[1] ⟶ X` with these two endpoint equations. It imposes no inverse,
  equivalence, or homotopy-group condition. Currying this map is exactly the edge
  α in `Fun(B × K,X)`. No additional extension or cone is an input.
- The fixed test vertex is `(w : X _⦋0⦌)`.
- For every vertex b, the first conjunct's antecedent is
  `ConstantTargetRestrictionSquare r (constantTargetCylinderBase (! : K ⟶ Δ[0]))
  (constantTargetCylinderVertex b ≫ constantTargetCylinderDiagram (fst B K) a f α) w`.
  The endpoint restriction is a(b); the zero-end restriction is f_b; and the full
  cylinder restriction is α_b. Its four corners and arrows are therefore exactly
  the four pointwise corners and their composition/r-induced arrows in the node,
  through the natural roof equivalence just described.
- The first conjunct's consequent is the same square on the entire global cylinder
  of pr_B, with `constantTargetCylinderBase (fst B K)`. The terminal endpoint gives
  `Map_Fun(B,X)(a, Δ_B w)` and its Y-version. The zero endpoint gives
  `Map_Fun(B×K,X)(f, Δ_(B×K) w)` and its Y-version. Its horizontal roof includes
  pr_B restriction before composition with α, exactly as in the node.
- The second conjunct, under `IsEmpty (B _⦋0⦌)`, explicitly asserts
  `IsContractible` for EACH of the four original global corners, written using a,
  f, a ≫ r, f ≫ r and the corresponding constant diagrams.
- The third conjunct, under `IsEmpty (K _⦋0⦌)`, explicitly asserts contractibility
  for BOTH original right corners. Its first iff identifies the whole pointwise
  hypothesis with `∀ b, IsWeakHomotopyEquivalence (mappingSpaceMap r (a.app _ b) w)`.
  Its second iff identifies the global condition with weak equivalence of the actual
  left-column `mappingSpaceMap ((ihom B).map r)` at a and Δ_B w.
- An empty vertex set is equivalent to an empty simplicial set: restriction of any
  simplex to any vertex would otherwise produce a vertex. Thus the two `IsEmpty`
  conditions are precisely the empty cases of the node, not stronger conditions.
- There are no colimit-existence assumptions in X or Y, nor additional conditions
  on r, B, K, the arrows of the diagrams, or α.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `diagramVertex`, `constantDiagrams`, `IsContractible` and
  `IsWeakHomotopyEquivalence`. Read the full source, including their formulas.
- `Sheaf.CategoryTheory.RelativeInfinityCone`: `SSet.Enhanced.IsHomotopyPullbackSquare`
  and `homotopyPullbackComparison`. Read its actual path-pullback signature and body.
- Mathlib `AlgebraicTopology.SimplicialSet.Homotopy`: `SSet.Homotopy`, its directed
  interval data `h`, and endpoint equations `h₀`, `h₁`; Mathlib categorical pushouts,
  cartesian products, internal homs and Yoneda supply the remaining constructions.
- The already stated proof dependencies are imported privately:
  `EnhancedFunctorConeCalculus`, `KanFibrationFiberCriterion`, `RightPinchComparison`,
  `SimplicialPresheafProjectiveModel` and `SpaceTransportClassification`, in their
  recorded `Sheaf.CategoryTheory` or `Sheaf.AlgebraicTopology` modules.
  `lem-coef-infinity-yoneda-presheaf-limits` and
  `lem-coef-simplicial-model-coherent-diagrams` have no recorded Lean module and are
  mentioned in the proof docstring without inventing imports or restating them.

Edge cases checked before writing:

- B empty, K arbitrary: both B and B×K are empty. All original corners are the
  mapping space of the unique pair of diagrams in the terminal functor simplicial
  set; hence they are terminal. The pointwise premise has no vertices to check.
- K empty, B arbitrary: the pr_B cylinder pushout is B, its zero-end source is empty,
  and the two right corners are terminal. The two iff clauses give the exact
  pointwise/global left-column criteria, with no existence requirement for maps a→w.
- B and K both empty: these descriptions agree; each original corner is terminal.
- Empty mapping spaces when K is nonempty are permitted; a vertex w does not force
  maps a(b)→w or f_b→Δ_Kw to exist. All predicates use weak equivalences of spaces,
  not a nonempty witness or a bijection of vertices.
- No arrow of B or K, nor α, is assumed invertible. In particular the transformation
  encoding uses the directed standard interval, not the invertible interval.

Searches for an existing statement or notion:

- `msearch.py`, leanfinder: “Pointwise homotopy pullback squares of mapping spaces
  into constant diagrams assemble into a homotopy pullback in a quasicategory”.
  Eight results concerned ordinary model-category path objects, truncated edge
  composition, an ordinary homotopy-category square, and hypercovers. None gives
  this coherent constant-target mapping-space assembly assertion.
- `msearch.py`, loogle: `SSet.Enhanced.mappingSpace,
  SSet.Enhanced.IsHomotopyPullbackSquare`. Zero results; unknown identifier
  `SSet.Enhanced.mappingSpace` in the Mathlib index.
- `msearch.py`, leansearch: “A homotopy pullback square of mapping spaces into a
  constant diagram is detected at each vertex of its indexing simplicial set”.
  Eight results were ordinary categorical pullback criteria and finiteness of
  simplicial pullbacks, not quasicategorical mapping spaces or this assertion.
- `msearch.py`, grep `homotopyPullback|IsHomotopyPullback|pointwise.*constant` in
  Mathlib `AlgebraicTopology`: zero hits.
- Direct `rg` for the item id and
  `pointwiseConstant|constantTargetSquare|ConstantTarget` in the project source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no exact declaration.
- Direct `rg` for `homotopyPullback|IsHomotopyPullback` in Mathlib
  `AlgebraicTopology`: zero hits. Broader source searches found the recorded
  relative-cone and source-attachment interfaces, which do not assert this node.
- Searches for mapping cylinders in Mathlib, the project source and `lean/Sheaf`
  found model-category cylinders, a relative categorical cylinder with equivalence
  conditions, and the endpoint-pushout blunt join. None is this relative pushout
  along pr_B. The new helpers are concrete construction data for the canonical
  square of this node, not independent notions or replacements of dependency data.
- Final collision search for all six chosen declaration names in Mathlib, source,
  side-project Lean and the upstream name index: no hits.

Sources opened: [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Proposition the project server and Corollary the project server (printed pp. 318–319),
[Kerodon 02XK](https://kerodon.net/tag/02XK), and the actual natural mapping-model
comparison [Kerodon 01L5](https://kerodon.net/tag/01L5).
The natural-language proof in the theorem docstring follows every node proof step,
including the pending pointwise-presheaf-limit and path-object inputs.

No statement correction, disputed statement, or unusable dependency was found.
Every variable and universe is explicitly bound; no local notation, local instance,
private definition, hidden `let`, or arbitrary chosen comparison is used.


## Second reading by Q06

I independently opened the item node, its sandbox node copy and full Lean module,
both statement-dependency nodes and their actual modules. The sandbox changes only
`lean` in the item record. There is no repair note for this id, no statement_change,
no new node, and no dependency module in this delivery. I found no mismatch requiring
a Lean or node edit; this second-reading section is the only change I made.

Source check: I read [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Proposition the project server and Corollary the project server (printed pp. 318–319), and Proposition
the project server (printed p. 320), as well as [Kerodon 02XK](https://kerodon.net/tag/02XK)
and [the pinch comparison 01L5](https://kerodon.net/tag/01L5).
The source place explicitly has no Stacks tag. HTT's pointwise colimit-existence
assumption is used, dually, in the category of spaces and its presheaf category,
where the required limits exist. It does not impose colimits on X or Y. Kerodon's
relative assertion also starts with an arbitrary functor; its proof replaces that
functor by an inner fibration rather than assuming a fibration. The given node is
its fixed-test-object mapping-space assembly form. Neither source restricts B or K
to nerves, nonempty shapes, or shapes whose arrows are invertible.

My object/hypothesis/conclusion checklist, with the file open:

| Node item | Lean rendering and verdict |
| --- | --- |
| Quasicategories X and Y | `{X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]`. Exact; no Kan assumption on either category. |
| Arbitrary enhanced functor r | `(r : X ⟶ Y)`. Exact simplicial functor, with no fibration or equivalence instance. |
| Small simplicial shapes B and K | `{B K : SSet.{u}}`. Exact; no nonempty, category-nerve or finiteness premise. All four simplicial sets can be placed in the arbitrary common universe of the dependency convention. |
| Diagram a on B | `(a : B ⟶ X)`. Exact. |
| Diagram f on B times K | `(f : B ⊗ K ⟶ X)`. Exact: the cartesian tensor is the degreewise simplicial product. |
| Projection to B | `fst B K`. Exact cartesian projection, used in both the transformation endpoint and cylinder. |
| Coherent transformation from f to a after projection | `(α : SSet.Homotopy f (fst B K ≫ a))`. Exact: I opened Mathlib's Homotopy and checked its interval map and the equations h₀ and h₁; no invertibility is part of this type. |
| Fixed vertex w | `(w : X _⦋0⦌)`. Exact; rw is `r.app _ w`. |
| Every vertex b, its f_b and α_b | `∀ b : B _⦋0⦌` and `constantTargetCylinderVertex b ≫ constantTargetCylinderDiagram (fst B K) a f α`. The pushout map is `(k,t) ↦ ((b,k),t)` on the cylinder and b on its endpoint. Its zero end is f_b and its endpoint is a(b); the full interval is α_b. Exact. |
| Four pointwise corners | The antecedent's `ConstantTargetRestrictionSquare`, with `constantTargetCylinderBase (! : K ⟶ Δ[0])`. Its right corners are the actual right-pinched mapping spaces from f_b and rf_b to the K-constant targets. Its left corners restrict canonically to Map_X(a(b),w) and Map_Y(ra(b),rw). This is the canonical roof presentation, justified below, not a test on components. |
| Pointwise composition and r maps, with the canonical homotopy | Horizontal maps are `mappingSpaceMap ((MonoidalClosed.pre i).app _)` and vertical maps are `mappingSpaceMap ((ihom _).map r)`. Under endpoint restriction the horizontal roof is composition by α_b; postcomposition preserves its entire interval. Thus its constant-path comparison represents the specified canonical homotopy, rather than a freely selected homotopy. Exact. |
| Pointwise pullback premise implies global pullback conclusion | The first conjunct is precisely the universally quantified pointwise `ConstantTargetRestrictionSquare` implying the same predicate on `constantTargetCylinderBase (fst B K)` and the global cylinder diagram. Exact implication and quantifier order. |
| Four global corners | Endpoint restriction of the two left corners gives the mapping spaces of a and ra in Fun(B,X) and Fun(B,Y). Zero-end restriction gives the spaces of f and rf in Fun(B times K,X) and Fun(B times K,Y). Targets come from the dependency's `constantDiagrams`. Exact up to the canonical endpoint equivalence of the roof. |
| Global horizontal arrows include projection restriction before α | `constantTargetCylinderDiagram (fst B K) a f α` glues α.h to a by α.h₁. Its zero-end map is f by α.h₀. Hence the restriction roof first pulls a-to-w back along pr_B and then composes with α; the Y-row is its postcomposition by r. Exact. |
| If B is empty, each of the four original global corners is contractible | Second conjunct, `IsEmpty (B _⦋0⦌) → ...`, lists four `IsContractible` clauses using a, f, a followed by r, and f followed by r. Exact; these are the original corners, not merely the cylinder corners. |
| If K is empty, both original right corners are contractible | Third conjunct lists both `IsContractible` clauses for the product-indexed X- and Y-mapping spaces. Exact. |
| Empty K: pointwise premise is equivalence on left columns | First iff in the third conjunct compares the whole pointwise premise with `∀ b, IsWeakHomotopyEquivalence (mappingSpaceMap r (a.app _ b) w)`. Exact maps and endpoints. |
| Empty K: global conclusion is equivalence on its left column | Final iff compares the global square predicate with `IsWeakHomotopyEquivalence (mappingSpaceMap ((ihom B).map r) (diagramVertex a) ((constantDiagrams B X).app _ w))`. Exact global left-column map. |
| No colimit or fibration existence hypothesis | There is no such binder in the theorem or any helper. Pushouts defining the indexing shape are simplicial-set pushouts, not colimits in X or Y. Exact. |

I checked the potentially delicate cylinder representation separately. For general
p:L→H let M=(L times Δ[1]) amalgamated over its final end with H, let j:H→M
be the endpoint inclusion and i:L→M the zero end. The diagram d really is α.h
on the cylinder and a on H. For an arrow u:a→constant(w), coherent extensions
from d to constant(w) are the composition coherences between α and p*u,
including their higher parameter simplices. Their space is contractible; forgetting
the extension is the usual inner-horn composition comparison. One can also see the
endpoint's finality from the cylinder contraction `(l,t,s) ↦ (l,max(t,s))`,
which fixes H and contracts the interval to its glued final end. This works for
arbitrary p and arbitrary simplicial L,H. Target-fixed mapping sections therefore
give a weak equivalence

`Map_Fun(M,X)(d,constant(w)) → Map_Fun(H,X)(a,constant(w))`.

Together with restriction along i, this is the canonical roof representing
precomposition with α. The construction commutes with every simplicial functor r.
Apply the natural right-pinch comparison to these arrow mapping spaces to obtain
exactly the right-pinched models in the Lean. Thus the square's canonical homotopy
is retained when the endpoint equivalences replace its left corners. It is valid
to test the specified square using the roof's strict restriction square and the
recorded constant-path comparison; a different, arbitrary path is never inserted.
For the assembly itself, the cylinder of pr_B is canonically B times the cylinder
of K→Δ[0], since product with B preserves simplicial pushouts. Its restriction at
b is precisely the pushout map `constantTargetCylinderVertex b`. This also checks
that pointwise and global predicates concern one coherent family.

Dependency checks: `EnhancedDiagramsCones.mappingSpace` imposes the entire initial
face equal to the source vertex and the last vertex equal to the target, with its
appendLast operators. `mappingSpaceMap` is actual postcomposition on these
simplices. `diagramVertex` and `constantDiagrams` are the recorded internal-hom
vertex and the curry of the second projection. `IsWeakHomotopyEquivalence` uses
components and every positive based homotopy group of realization;
`IsContractible` tests the actual terminal map. In RelativeInfinityCone I read both
`homotopyPullbackComparison` and `IsHomotopyPullbackSquare`: the latter requires
strict commutativity and weak equivalence of the actual constant-path comparison
into the full path pullback. This matches the strictly commuting roof; it is not
an ordinary categorical pullback predicate. The dependency records are usable as
written and are imported publicly, with no substitute definition.

Edge cases checked independently: an empty vertex set forces every simplicial
degree empty by restriction to a vertex. Thus the two IsEmpty hypotheses express
exactly empty simplicial shapes. If B is empty the pointwise premise is vacuous
and all four original corners are terminal; if K is empty the cylinder of pr_B
is B, its zero end is empty, and the two right corners are terminal, giving the
two stated left-column criteria. Both empty cases agree. Mapping spaces may be
empty for nonempty shapes, and the theorem never asserts their nonemptiness.
X and Y can be empty in the ambient quantification; the supplied w makes the
empty-X instance vacuous exactly as in the node. Degree zero and degenerate
simplices are included by the actual internal-hom and mapping-space formulas.
There is no arithmetic, characteristic or nonzero-ring restriction here. The
universe u is explicitly bound; no hidden auto-implicit variable is enabled.

Independent searches used different descriptions from the worker:

- LeanFinder through msearch.py: “Restriction to the final endpoint of a relative
  simplicial mapping cylinder gives equivalent spaces of maps into a constant
  diagram”. Eight hits were ordinary HomotopicalAlgebra cylinder endpoint and
  projection facts; none states this coherent assembly or its relative cylinder.
- LeanSearch through msearch.py: “Limits in infinity categories of space valued
  functors are pointwise and preserve cartesian squares of spaces”. Eight results
  were ordinary functor-category limits and preservation declarations, with no
  quasicategorical mapping-space square or specified homotopy.
- Loogle through msearch.py: `CategoryTheory.Square.IsPullback` returned twelve
  ordinary categorical square facts. They do not assert the node's path-model
  pullback statement. An earlier query mistakenly using
  `CategoryTheory.Limits.IsPullback` reported an unknown identifier; I corrected
  the namespace and searched again rather than counting that as a successful
  absence search.
- Direct rg on Mathlib/AlgebraicTopology and then the entire Mathlib tree, the
  upstream WeilConjectures source, and lean/Sheaf searched mapping cylinders,
  pointwise homotopy pullbacks, and constant-target squares. I opened RelativeCategoricalCylinderCriterion: it requires an
  invertible/categorical-equivalence cylinder with two endpoint sections and is
  a different notion. BluntJoinComparison defines the two-ended blunt join,
  not this relative composition roof. CocartesianRelativeCylinderExtension
  asserts extension of a lift using fiber colimits, not this fixed-target test.
  None supplies this statement. Name searches for the theorem and all five
  helpers in upstream, lean/Sheaf, and dag/lean_names_upstream.json returned no
  collisions.

Construction and documentation verdict: all five helper definitions have explicit
pushout/restriction data. The two equality proofs inside pushout.map are
well-definedness data proved by extensionality, not postponed lemmas or a new
mathematical result. The only theorem is the node's theorem with proof `sorry`.
Each declaration has the source and blueprint docstring, and the main docstring
follows all five DAG proof steps with their cited inputs. No new definition node
or dependency repair is needed for these item-specific canonical-map helpers.
No existing Lean or node text was rewritten.

Validation: scompile.py Q06 lem-coef-pointwise-constant-target-square-assembly
compiled the delivered module both in its sandbox form and under its intended
library path, cleanly (reported 1.9 s and 1.8 s). I checked the recorded
lean.statement is verbatim the theorem signature up to :=, that the six recorded
declarations are those in the file, that the file has one sorry, and that no line
exceeds 100 characters. All binders and u are explicit. The required deliver2.py --no-push dry run subsequently printed OK: commit
28440abf3e passes the server preflight and compiles; nothing was pushed by that
dry run. The prescribed delivery push follows.
