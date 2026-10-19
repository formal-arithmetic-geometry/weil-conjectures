## Worker report

The delivery states `SSet.SingularSpanBar.singular_span_bar_cylinder_gluing` in
`Sheaf.AlgebraicTopology.SingularSpanBarCylinderGluing`. It includes the genuine missing
prerequisite `lem-coef-double-cylinder-weak-equivalence-gluing`, whose module supplies the
endpoint quotient and its canonical induced maps. All four theorems have whole proofs
`sorry`; all definitions have explicit data. The assigned node's natural statement,
proof, and proof dependencies are unchanged. Its statement dependencies gain the cylinder
node because its actual quotient construction is needed to type the comparison.

The source was read at
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
paragraph 2. That paragraph supplies the derived-adjunction context; the assigned node
and its reviewed auxiliary nodes specify the expanded topological construction. No
stronger source hypothesis has been inferred from the surrounding algebraic setting.

Hypotheses and clauses of the assigned node correspond as follows:

- Small simplicial sets `A,B,C` are the unrestricted `SSet.{u}` binders. The universe
  is explicit and arbitrary. Given continuous maps of realizations are exactly
  `f : |C| ⟶ |A|` and `g : |C| ⟶ |B|`, morphisms of `TopCat`.
- The ordinary walking span is Mathlib's `WalkingSpan`, with `left=a`, `zero=c`, and
  `right=b`. Mathlib's `span f g` has precisely the two nonidentity arrows out of `zero`.
- The strict singular diagram is `diagram (realizedSpan A B C f g)`, defined by
  `span f g ⋙ TopCat.toSSet`. Its values and arrows are the existing singular-set
  functor, not a substitute model. `TopCat.toSSetObjEquiv` identifies each degree
  with continuous maps from the real topological simplex; its operators precompose
  with the affine simplex operators.
- `bar S` is the dependency's `SSet.BousfieldKan.BK WalkingSpan (diagram S)`.
  Its degree objects really are dependent sums of `ComposableArrows` and simplices
  at the first object. Its face and degeneracy operations are the recorded BK ones.
- `Space (realizedSpan A B C f g)` is the stated `D(f,g)`: the type is `Quot (Rel S)`
  on `S.A ⊕ ((S.C × Set.Icc (0:ℝ) 1) ⊕ S.B)`. `Rel.left` and `Rel.right` are exactly
  `(y,0)~f(y)` and `(y,1)~g(y)`. The topology is the ordinary disjoint union/product
  topology followed by the quotient topology; there is no compact-generation step.
- A representative `[(chain,σ),s]` is `realizationPoint (bar S) n z s`. This is the
  existing realized Yoneda simplex evaluated at `n.toTopHomeo.symm s`, hence the
  ordinary geometric-realization class, not an unrelated presentation.
- The sum `w=Σ_{j:i_j=c}s_j` is `centralWeight z.1 s`, with an explicit finite sum
  over the chain's vertices.
- `simplexFormula` matches the initial vertex. Its `left` case is the left quotient
  class of the continuous evaluation `σ(s)`, using `S.A.toSSetObjEquiv`. Its `right`
  case is the corresponding right class, using `S.B.toSSetObjEquiv`. Its `zero`
  case evaluates in `S.C` and inserts `cylinderTime z.1 s` into the middle summand.
- `cylinderTime` is `w/2` if the final vertex is `left`, `1-w/2` if it is `right`,
  and `1/2` if it is `zero`. The `Set.projIcc` only bundles the real value into the
  interval. Since the simplex coordinates are nonnegative and sum to one,
  `0≤w≤1`; all three real values already lie in the interval and clamping fixes
  them. This adds no restriction and does not change any coordinate formula.
- The existential `Φ` is a family of continuous maps, with its value specified on
  EVERY representative by the first conjunct. This expresses precisely that the
  displayed formula is well defined and continuous. Realized simplices cover the
  realization, so the characterization determines the map; this is not an
  arbitrary comparison map or a definition chosen from mere existence.
- `IsWeakEquivalence (Φ A B C f g)` unfolds to bijectivity on the dependency's
  `componentsMap`, and bijectivity of its `homotopyGroupMap` for every `r≥1` and
  every source basepoint. Those are the prescribed path components and cubical
  homotopy groups relative to the entire boundary. Postcomposition preserves
  concatenation, so bijectivity is exactly isomorphism of the indicated groups.
- A strict map of spans is `e : Hom S T`: it contains continuous component maps
  `a,b,c` and the two equations `S.f ≫ e.a = e.c ≫ T.f` and
  `S.g ≫ e.b = e.c ≫ T.g`. These are precisely the displayed two commuting squares.
  `diagramMap e` applies `TopCat.toSSet` to the strict span transformation;
  `barMap e` is the dependency's `bkMap` of that transformation.
- The last equation is `D(e) ∘ Φ = Φ' ∘ |BK(Sing(e))|`, with the actual
  quotient-induced `TopCat.DoubleMappingCylinder.map e` on the left. Its middle
  action is `(e.c, identity of [0,1])`, as required.
- There is no nonemptiness, separation, connectivity, compact generation, or
  special characteristic binder. In particular any of the three simplicial sets
  may be empty whenever the given arrows exist.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the full signatures and docstrings of
  `SSet.Enhanced.componentsMap`, `homotopyGroupMap`, and `IsWeakHomotopyEquivalence`.
  The first two are reused directly; the last was inspected to retain its exact
  path-component and based positive-degree convention for arbitrary spaces.
- `Sheaf.AlgebraicTopology.BousfieldKanComparisonCalculus`:
  `SSet.BousfieldKan.BKObj`, `BKMap`, `BK`, `bkMapApp`, and `bkMap`, including their
  chain orientation, actual operators, and endpoint action. The main
  `comparison_calculus` statement and proof docstring were read as well.
- The delivered `Sheaf.Topology.DoubleMappingCylinder` supplies the actual `Space`,
  `mk`, `Hom`, and `map`; its owning node is now cited in `stmt_deps`.
- Mathlib `Mathlib.AlgebraicTopology.SingularSet`: `TopCat.toSSet`,
  `TopCat.toSSetObjEquiv`, `SSet.toTop`, `sSetTopAdj`, `SSet.toTopSimplex`.
  Mathlib `Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`: `SimplexCategory.toTopHomeo`.
  Mathlib `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan`: `WalkingSpan`,
  `span`, and `spanHomMk` (central, left, right argument order).
  Mathlib `Mathlib.Topology.Constructions`: the quotient topology on `Quot`.
  Mathlib `Mathlib.Order.Interval.Set.ProjIcc`: the explicit interval projection.

Edge cases checked before writing: if `C` is empty the central bar summands and
middle cylinder disappear and the map is the two counits on the disjoint ends.
An empty `A` or `B` forces the existence of the indicated arrow to require `C`
empty. If all three are empty, the map is empty-to-empty and the component
condition is bijective while the based conditions are vacuous. If all three are
points the central vertex lands at `1/2`, the two bar edges run over the two
halves of the interval, and the end vertices land at `0,1`. For a central chain
with final left/right vertex, `w=0` is the corresponding glued end and `w=1`
is the midpoint. Repeated central vertices and identity arrows use the full sum
of their barycentric coordinates; the formula is therefore compatible with
inserting identities. Degree zero is retained in the formula; positive degrees
only are used for homotopy groups, with the separate component condition.

Searches made for an existing statement or construction:

- `msearch.py ... leanfinder "The singular simplicial bar of a walking span realizes
  weakly equivalently to the double mapping cylinder"`: eight hits, all abstract
  model-category cylinder facts or the algebraic homotopy cofiber; no topological
  walking-span comparison.
- `msearch.py ... loogle "SSet.toTop, TopCat.toSSet, sSetTopAdj"`: four hits,
  `sSetTopAdj`, its unit formula, the standard-simplex unit formula and the degree-zero
  adjunction formula; none states the assigned comparison or defines its double cylinder.
- `msearch.py ... grep "mapping.?cylinder|doubleCylinder|double.*cylinder"
  AlgebraicTopology`: zero hits.
- `msearch.py ... leansearch "double mapping cylinder topological spaces homotopy
  equivalence under weak equivalences of spans"`: eight hits, homotopy equivalence
  structures and abstract model-category cylinder facts; no match.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`,
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`, and Mathlib for
  `DoubleMappingCylinder|doubleMappingCylinder|singular_span_bar_cylinder_gluing|singularSpanBar`:
  no declarations. The exact node ID search in the source repository also found none.
  A broader span/bar/cylinder search found unrelated enriched bar and categorical
  mapping-cylinder constructions, not this topological quotient or this theorem.
- DAG node inspection found the already existing genuine cylinder-gluing node;
  it is supplied under the missing-prerequisite authorization rather than adding
  a duplicate definition node. Both it and the other two proof auxiliaries had no
  usable Lean record. The other two supply only proof steps, not missing objects
  used in the statement, and are left for their own statement work.
- A search for existing topological weak-equivalence definitions in Mathlib and
  `lean/Sheaf/Topology` found none with this type; the imported enhanced-diagrams
  module exposes the exact component and cubical group maps that are reused.

No statement correction or disputed mathematical statement is proposed. The source
still lacks the archived external homotopy-theory reference requested in the DAG;
this delivery does not replace that request with an assertion of archival coverage.

## Dependency modules

`lem-coef-double-cylinder-weak-equivalence-gluing` had neither a `lean` record nor a
`mathlib_match`; the prescribed `scompile.py --source Sheaf.Topology.DoubleMappingCylinder`
also confirmed that this newly supplied module was not already available. Under the
human's 2026-10-16 instruction to state genuine missing prerequisites, this delivery
provides `Sheaf.Topology.DoubleMappingCylinder` and changes only that node's `lean`.
Its statement is rendered for arbitrary spaces `Span.{u}` with no extra assumptions:
`f,g` are its two continuous arrows, `Raw/Rel/Space` give the exact quotient and
topology, and `Hom` records the three maps and their two commuting equations.
`rawMap` acts by `e.a`, `(e.c,id)`, and `e.b` on the three summands. `rawMap_rel`
states its descent through the endpoint identifications; `map` is literally
`Quot.map`, and `continuous_map` states its continuity. The main
`weak_equivalence_gluing` has three clauses: `map (Hom.id S)=id`, preservation of
composition for all composable strict triples, and weak equivalence of `map e`
assuming exactly weak equivalence of `e.a,e.c,e.b`. `IsWeakEquivalence` is explicitly
the dependency's component and based cubical group criterion. Empty spaces remain
allowed. Every auxiliary theorem has a natural-language proof in its docstring and
is an explicit well-definedness or continuity clause of this same DAG node.

Validation: both delivered files passed the prescribed `scompile.py N1
lem-coef-singular-span-bar-cylinder-gluing <DoubleMappingCylinder.lean>
<SingularSpanBarCylinderGluing.lean>` call, in dependency order, in both their sandbox
and library-module forms, with no errors or warnings. Every universe and variable
is explicitly bound (`autoImplicit false` in both files). The initial elaboration
failure was repaired by scoped classical decidability for vertex comparisons and
an explicit dependent `Eq.ndrec` for identifying the singular simplex's target.

The first dry run passed preflight and compilation (`837654295b`). Its refresh
revealed that the cylinder node's stage-1 proof had been expanded during this
session; its natural statement was unchanged. I reread that complete six-step
proof and its prerequisite records. The module now imports the stated proof
prerequisites `Mathlib.Topology.CompactOpen` (`ContinuousMap.curry/uncurry`) and
`Sheaf.CategoryTheory.HomotopyEquivalenceWeak`
(`SSet.Enhanced.homotopy_equivalence_weak`) privately, and its main proof docstring
follows all six current DAG steps, including joint continuity of quotient
homotopies via currying and the final binary-open-cover gluing input. The latter
node remains unstated and is consequently not imported. The dependency node copy
was refreshed while retaining only this delivery's `lean` change.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
