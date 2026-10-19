## Worker report

The module `Sheaf.AlgebraicTopology.InfinityPullbackMappingSpace` states
`SSet.Marked.infinity_pullback_mapping_space`. Its only postponed proof is that
named theorem. The auxiliary declarations are explicit maps, the strict marked
pullback, its actual coordinates, and the structure bundling the assertion; no
new mathematical notion or dependency repair is needed. No definition has sorry
data. The two additional stmt_deps are already landed nodes whose helper
constructions are reused, rather than duplicated.

Clause-by-clause translation:

- Small quasicategories C, X, Y: `IntervalCospan.X`, `.Y`, `.C` are `Marked.{u}`
  with `fibrantX`, `fibrantY`, `fibrantC : IsNaturallyFibrant ...`.
  The recorded dependency defines this predicate as the quasicategory condition
  and exactly the equivalence marking. This is the same data as C^natural, etc.,
  not a separate model of quasicategories. The natural marking's explicit
  degenerate-edge disjunct agrees with equivalences by the dependency theorem.
- Arbitrary functors f and g: `IntervalCospan.f` and `.g` are marked maps between
  these naturally marked objects. This adds no preservation hypothesis: applying
  a simplicial map to an inverse and its two triangular witnesses preserves all
  the inverse equations, so every functor is such a marked map. Degenerate edges
  are preserved by simplicial naturality. There is no fibration assumption on f
  or g, nor an equivalence or nonemptiness assumption on any object.
- W=(C^natural)^((Delta[1])^sharp): the actual dependency construction
  `internalHom (sharp (Delta[1])) S.C` is used in every interval declaration.
  `intervalEvaluation` inserts a fixed endpoint and uses the dependency's
  `exponential` applied to the identity. `exponential_formula` uniquely pins
  this adjunction to ordinary evaluation, so this does not choose arbitrary
  endpoint maps. `intervalEndpoints` pairs evaluations at 0 and 1.
- Endpoint model-fibration hypothesis: `.endpoint_fibration` is
  `(cof ⊓ weak).rlp (intervalEndpoints O C)`, exactly the fibration class
  `O.fibrations` of the recorded model theorem. It is the only relative lifting
  hypothesis.
- Strict marked pullback H: `intervalPullback S` is
  `pullback (productMap S.f S.g) (intervalEndpoints O S.C)`, using `O.complete`.
  This is an ordinary categorical pullback in marked simplicial sets, not a
  homotopy pullback substitution. Its object is determined up to the unique
  projection-preserving isomorphism by the pullback universal property. The
  completeness data are supplied by the model dependency; no choice from a
  bare existence assertion is used to define an unspecified object.
  `intervalPullbackBase` and `intervalPullbackPath` are its actual two maps.
- H fibrant, hence H=R^natural: `.fibrant` states `IsNaturallyFibrant H`.
  Unfolding that existing predicate says its underlying R is a quasicategory
  and its marking is exactly the equivalence predicate. Extensional equality
  of marked objects then gives H=natural R, using the dependency's
  `natural_marking`. No additional R or unspecified equivalence is introduced.
- Test quasicategory Q: `A : FibrantObjects.{u}` is the dependency's full
  subcategory on `IsNaturallyFibrant`. Its `.obj` is exactly Q^natural. This
  retains the empty quasicategory and arbitrary small quasicategories.
- The four mapping complexes are the dependency's `mapSharp`, not Hom sets.
  `.mapping_kan` explicitly asserts Kan fibrancy for the left side, each of the
  three other mapping complexes, and the path-space target. The right-hand
  object `intervalMappingTarget` uses the existing
  `Enhanced.simplicialHomotopyPullback (mapSharpPost A f) (mapSharpPost A g)`.
  Its definition is exactly the two iterated endpoint pullbacks displayed in
  the node, with `Fun(Delta[1],M)` the existing `(ihom Delta[1]).obj M`.
- The claimed isomorphism: `.comparison S A` is an actual simplicial-set
  isomorphism, with both inverse identities. Together with `.mapping_kan`,
  it is precisely an isomorphism of Kan complexes.
- Preservation of the X and Y projections: `.first_projection` and
  `.second_projection` are equalities of simplicial maps, using the existing
  homotopy-pullback projection declarations and the actual marked projections.
- Preservation of the specified entire interval path: `.specified_path`
  fixes the path coordinate in every simplicial degree, via
  `intervalCurriedSimplex`. That definition reassociates
  A x (Delta[n] x Delta[1])^sharp to (A x Delta[n]^sharp) x Delta[1]^sharp,
  postcomposes with the supplied interval coordinate and ordinary evaluation,
  uses the dependency's normalized tensor adjunction, swaps the two parameter
  factors, curries Delta[1], and uses Mathlib's Yoneda equivalence. Thus the
  path is fixed on every simplex, not only at the endpoints or up to homotopy.
- Naturality in Q: `.natural_source` is the actual commuting square with
  `mapSharpPre q H` and `intervalMappingPre S q`. The latter reuses the existing
  canonical homotopy-pullback map on all three precomposition maps.
- Naturality in strictly commuting maps of cospans: `.natural_cospan` takes
  arbitrary a,b,c with exactly `S.f ≫ c = a ≫ T.f` and
  `S.g ≫ c = b ≫ T.g`. It supplies the induced actual marked map h of strict
  pullbacks. The first equality specifies its base coordinates; the next
  equality specifies its uncurried path by postcomposition with c. These two
  conditions determine h uniquely. For every Q, the final equality is the
  commuting comparison square with `intervalMappingPost`; this uses the
  existing canonical path-model map with coordinates a_*, b_*, c_*.
- Enlargement of the input universe: the theorem asserts the full bundled
  statement both at u and at `max u v`, for any v, with the same polymorphic
  definitions and normalization formulas. There is no equality imposed on
  universes or restriction to successor universes. In particular the products,
  evaluations, currying and projection formulas on lifted original inputs are
  the same formulas; the theorem does not choose unrelated comparison maps
  without coordinate normalizations. This is validity in every enlarged input
  universe, as in the node, rather than a separate invariance hypothesis.
- The final homotopy-pullback clause is rendered literally by the reused
  path-space definition. The Kan assertion and the isomorphism identify that
  model with the left mapping complex.

The `O : CartesianModelStatement` parameter merely makes the dependency's
complete model and its normalized adjunctions explicit. The dependency theorem
supplies such data in both input universes. The assertion works for every such
model, so no chosen replacement model or stronger property is assumed.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `Hom`, `product`, `productMap`, `sharp`, `internalHom`,
  `mapSharp`, `mapSharpPre`, `mapSharpPost`, `cof`, `weak`,
  `IsNaturallyFibrant`, `FibrantObjects`, `CartesianModelStatement`, and
  `marked_point_cartesian_model`. In particular I read the complete structure
  signatures, the exponential and tensor normalization formulas, fibration
  identification, completeness and Kan-enrichment clauses.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge`, `core`, `evaluation`, and the recorded
  `coneCategory` construction/docstring. This is the shared simplicial,
  quasicategorical, functor-object and homotopy-fiber convention.
- `Sheaf.CategoryTheory.SourceAttachmentGluing`:
  `SSet.Enhanced.simplicialHomotopyPullback`,
  `sourceAttachmentPullbackFst`, `sourceAttachmentPullbackSnd`.
  Their full definitions and docstrings were read. Its much broader gluing
  theorem is not assumed by the statement: only these existing definitions
  are used. The owning landed node is added to stmt_deps.
- `Sheaf.CategoryTheory.KanHomotopyPullbackInvariance`:
  `SSet.Enhanced.simplicialHomotopyPullbackMap`, including its two actual
  pullback lifts and endpoint-naturality proofs. Only this canonical map is
  used, not its weak-equivalence theorem. The owning landed node is added to
  stmt_deps. No weak-equivalence hypothesis on a,b,c is added.
- Mathlib: `pullback`, its projections, `lift`, `fst`, `snd`, the associator and
  braiding, `MonoidalClosed.curry`, `SSet.yonedaEquiv`, `KanComplex` and the
  ordinary internal hom. I read the closed-functor implementation and the
  Yoneda-equivalence signature used for the curried simplex.

Edge cases: Q empty makes each mapping complex and the target terminal; the
statement includes this without requiring an inhabitant. If C is empty, any
nonempty X or Y has no cospan leg; the valid empty cases remain included. If
C is a point, the target reduces to the product of the two mapping complexes.
Disjoint discrete images give the empty pullback and empty target when Q is
nonempty; for empty Q both remain points. Simplicial degree zero still retains
an entire interval in M, not an equality of vertices. The cospan maps can be
identities or arbitrary nonfibrations. No characteristic or finiteness condition
appears. Naturalities include identity and composite source/cospan maps through
actual equality of simplicial maps.

Searches made using the authorized msearch wrapper (raw outputs in the sandbox
search log):

- LeanFinder: "Sharp mapping complexes of a marked interval path pullback are
  the path homotopy pullback of Kan mapping complexes". Eight results, led by
  `HomotopicalAlgebra.PathObject.trans_P`, `PathObject.trans_ι`, and SSet paths.
  These concern abstract path objects/edge paths, not this marked comparison.
- LeanSearch: "Sharp mapping spaces preserve pullbacks of marked simplicial
  sets". Eight generic pullback-preservation results, led by `IsPullback.map`;
  none gives this sharp interval mapping formula.
- Loogle: `"MonoidalClosed", "curry"`. Twelve results, including `curry`,
  `uncurry`, their inverse identities and `curryHomEquiv'`. These are reused
  primitives, not an existing statement of the item.
- msearch grep: `MapSharp|mapSharp|marked.*[Cc]otensor`: no Mathlib hits.
- Direct rg in Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf` for
  the candidate names and marked sharp/pullback formulas found no exact
  statement. The upstream search for the node id gave no hit. Side-project
  concept searches found the marked model and the existing homotopy-pullback
  definition/map, which are reused. The proposed declaration/helper names have
  no existing matches in any of these libraries.

Source check: fetched the cited HTT PDF to this item's scratchpad, converted it
to text, and read the internal-Hom and sharp mapping properties preceding
Remark the project server (printed pp. 154-155), Corollary the project server and its proof (p. 162),
and Remark A.2.4.5 (p. 816). These agree with the tensor/cotensor and path-model
conventions. Also read the current blueprint's integral-exceptional-adjoint
proof paragraph 2; this item supplies its inherited technical mapping-space
infrastructure and is not the unit's own statement.

No STATEMENT-DISPUTED flag, statement correction, new node, or dependency repair.
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NH
lem-coef-infinity-pullback-mapping-space
lean/Sheaf/AlgebraicTopology/InfinityPullbackMappingSpace.lean` passed both the
sandbox and library checks without errors or warnings, with the sole intended
sorry theorem. No global build or direct git operation was run.

## Second reading by NH

I reopened the node and complete final module for a separate clause-by-clause
self-check. The dispatcher forbids starting another agent; the maintainer's
independent review remains the external second reading. This section records
what was actually checked, without claiming another worker performed it.

I checked that `.endpoint_fibration` concerns only W -> C x C; `.f` and `.g`
remain arbitrary functors. `IsNaturallyFibrant` and `FibrantObjects` encode
exactly the four naturally marked quasicategories, including the empty ones.
The marked H uses the actual productMap and endpoint map. The source object of
`comparison` is `mapSharp A.obj H`, and its target expands to exactly the
iterated endpoint pullback. Both projection equations have the correct factor
order. In the path formula the reassociator gives ((q,t),i), the braiding sends
(i,t) to (t,i), and currying therefore gives Delta[n] -> Fun(Delta[1],M),
with the correct interval direction and no endpoint reversal. The naturality
square in Q has precomposition B -> A, and the cospan square has
postcomposition S -> T. The induced marked h is pinned on the whole uncurried
interval, not merely its endpoints. The large-universe clause keeps the same
formulas at max u v. There are no auto-bound variables or hidden assumptions.

The first compilation exposed that the canonical homotopy-pullback map's
module does not export the separate SourceAttachmentGluing definitions. I
added their owning module explicitly, rather than recreating them. The final
compile is clean. No mismatch with the node was found in the separate reading;
the report explicitly documents the equivalent naturally-fibrant encoding,
universal-property limit construction, and universe-polymorphic interpretation
so the independent maintainer can assess them directly.
