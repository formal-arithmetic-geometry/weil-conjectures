## Worker report

The module `Sheaf.AlgebraicTopology.SphereMappingWeakEquivalence` states
`SSet.Enhanced.sphere_mapping_weak_equivalence`, with one `sorry` and no other
declarations. The node statement and dependencies are unchanged. No new nodes,
dependency modules, statement correction, or disputed statement are needed.

Source checked: Hovey, *Model Categories*, Lemma 2.4.17, printed pp. 56--57,
and Proposition 2.4.22(1), printed p. 58, in the PDF linked in the node. The
former includes every sphere dimension at least -1 and the empty-sphere
convention; the latter supplies kification. The proof docstring records all
eight steps of the DAG proof, including the reduction to arbitrary spaces,
the explicit disk-cylinder retraction, the disk contraction, the sphere
pullback, both group exact-sequence chases, and the component orbit argument.

Hypotheses and clauses, matched individually:

- Arbitrary topological spaces are `{X : Type u} {Y : Type v}` with their
  `TopologicalSpace` instances. The two universes are independent. There are
  no separation, connectedness, compact-generation, or nonemptiness assumptions.
- The continuous map is `(f : C(X, Y))`.
- The component bijection is `hπ₀ : Function.Bijective (componentsMap f)`.
  This is the dependency's map on path components, not connected components.
- All positive based-group isomorphisms are
  `hπ : ∀ (n : ℕ), 1 ≤ n → ∀ (x : X),
  Function.Bijective (homotopyGroupMap f n x)`.
  The dependency defines this map by postcomposition on boundary-relative
  cubical homotopy classes. It preserves concatenation, so bijectivity is
  exactly the group-isomorphism condition, including the nonabelian first group.
- The sphere is `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)`.
  Indexing by ambient dimension `m : ℕ` is a reindexing of the entire range
  `r ≥ -1`: `m = 0` is `S^(-1)` and `m = r + 1` gives each `S^r` for `r ≥ 0`.
  Mathlib's Euclidean norm is the norm in the node; a sphere of radius one
  about zero is exactly the subset defined by norm equal to one.
- The mapping set is `C(sphere, X)`, with Mathlib's compact-open topology;
  `ContinuousMap.compactOpen_eq` generates it by precisely the compact/open
  subbasic conditions in the node. The codomain is handled identically.
- Kification is the dependency's `TopologicalSpace.compactlyGenerated`,
  installed on the same underlying continuous-map set through Mathlib's
  `WithTopology`. Its compact-test universe is explicitly `max u v` on both
  sides, large enough for compact real spheres, cubes and their products;
  no equality of the source and target universes is imposed.
- The conclusion quantifies over every `m` and asserts a bundled continuous
  map `g` between those exact kified spaces. The equation
  `∀ a, WithTopology.ofTopology (g a) = f.comp (WithTopology.ofTopology a)`
  fixes its underlying function to postcomposition on every input. This is
  a uniquely determined canonical map, not an unspecified weak equivalence.
  Existentially bundling its continuity in the theorem introduces no choice
  of data, no auxiliary postponed continuity theorem, and no new definition.
- Its weak equivalence is the conjunction of
  `Function.Bijective (componentsMap g)` and
  `∀ (n : ℕ), 1 ≤ n → ∀ x, Function.Bijective (homotopyGroupMap g n x)`.
  The component and based-group conventions are exactly those in the hypotheses.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.componentsMap` and `SSet.Enhanced.homotopyGroupMap`.
  Their full definitions and docstrings were read. The module is publicly
  available through the realization dependency. Its simplicial
  `IsWeakHomotopyEquivalence` is deliberately not applied to topological maps.
- `Sheaf.AlgebraicTopology.RealizationFiniteLimits`:
  `SSet.realization_finite_limits`, including its complete signature and
  k-space/limit conventions. The public import supplies the recorded
  kification topology and Euclidean-space primitives; the theorem is a proof input.
- `Mathlib.Topology.CompactOpen`: `ContinuousMap.curry` and
  `ContinuousMap.uncurry`, the recorded Mathlib match for
  `lem-coef-compact-open-currying`. Their signatures and docstrings were read;
  both are imported as proof inputs, together with `continuous_postcomp`.
- `Sheaf.CategoryTheory.HomotopyEquivalenceWeak`:
  `SSet.Enhanced.homotopy_equivalence_weak`, imported as a proof input after
  reading its signature and homotopy/basepoint docstring.
- `lem-coef-serre-homotopy-exact-sequence` has neither a Lean declaration nor
  a Mathlib match at this snapshot. It is only a proof dependency, not a
  statement prerequisite, so it is described in the proof docstring and
  has no module import yet. No other DAG node is stated in this delivery.

Edge cases checked before writing:

- `m = 0`: Euclidean space on `Fin 0` has only its zero vector, of norm zero;
  its unit sphere is empty. Both mapping spaces are singletons, even for
  empty targets, so the component and group conclusions are correct.
- `m = 1`: the sphere in the real line has the two unit points and represents
  `S^0`, without accidentally replacing the unbased mapping space by a based one.
- Empty `X`: the component bijection forces `Y` empty. For `m > 0` both
  mapping spaces are empty; the component bijection holds and the group
  condition quantifies over no basepoints. The `m = 0` case remains a singleton.
- Disconnected spaces and nonconstant sphere maps are included. Every
  continuous sphere map is a possible basepoint `x` in the conclusion.
- Degree zero is covered by the separate path-component condition; positive
  degrees start at one, and no assumption of abelian fundamental groups is made.

Searches for an existing statement:

- `msearch.py`, `leanfinder`, query “Postcomposition by a weak homotopy
  equivalence induces a weak homotopy equivalence of compact open sphere
  mapping spaces”: eight hits. They concern model-category homotopy classes,
  postcomposition of homotopies, or a sphere homotopy-equivalence predicate;
  none states this topological mapping-space result. In particular
  `LeftHomotopyClass.postcomp_bijective_of_weakEquivalence` is about homotopy
  classes in an already supplied model structure, not this theorem.
- `msearch.py`, `loogle`, query
  `ContinuousMap.comp, HomotopyGroup, TopologicalSpace.compactlyGenerated`:
  zero hits.
- `msearch.py`, `grep`, query
  `WeakHomotopyEquiv|weakHomotopyEquiv|sphere.*[Mm]ap`, subdirectory `Topology`:
  eight hits, all classical CW-complex attaching-map conditions, not a match.
- `rg` of upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id, `sphere_mapping_weak`,
  `SphereMapping`, and `sphereMapping` found no existing declaration.
  Broader weak-equivalence searches in the topology modules found only
  simplicial/abstract model statements; no duplicate topological statement.
- Mathlib source searches for `compactlyGenerated`, `WithTopology`,
  `continuous_postcomp`, `curry`, and `uncurry` identified the exact existing
  topology and continuous-map constructions used in the signature and proof plan.
  Search-tool outputs are also retained in the sandbox's `searches.jsonl`.

Validation: `scompile.py Q71 lem-coef-sphere-mapping-weak-equivalence` compiled
the delivered module successfully both as a sandbox file and at its library
module path. The required proof-dependency overlay also compiled. No errors
or non-sorry warnings were reported. All variables and universes are bound;
there is no local notation, local instance, private definition, or hollow data.


## Second reading by Q71

I independently read the node, its eight proof steps, the complete delivered Lean
module, the statement-dependency nodes and their actual declarations, and the
available proof-dependency declarations. There is no item-specific repair note.
The sandbox contains just the item node and its module: no new definition node or
dependency module requires a separate H12/H13 audit. There is no statement_change;
the mathematical statement and statement dependencies agree with the repository.

Source checked independently: [Hovey, Model Categories](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf),
section 2.4, printed pp. 49--50 (ambient category, compact-open topology, spheres,
and based cubical homotopy groups), Lemma 2.4.17, printed pp. 56--57, and
Definition 2.4.21 / Proposition 2.4.22(1), printed pp. 57--58.
The source is Hovey, not a Stacks tag. Top in this section comprises arbitrary
topological spaces and continuous maps. The sphere theorem has no separation,
connectedness, nonemptiness, or compact-generation hypothesis on X or Y.
Kification retains continuous maps from compact Hausdorff tests, so it retains
the component and based-group maps used here. Thus the node's kified version
has exactly the same weak-equivalence content as the source theorem.

The following is my object/hypothesis/conclusion checklist, taken from the node
before comparing it with the candidate:

1. **Two arbitrary topological spaces X and Y.** Lean:
   `{X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]`.
   Verdict: exact, including distinct universes; no extra geometric or size
   hypothesis. Neither space is assumed already k-generated.
2. **A continuous map f from X to Y.** Lean: `(f : C(X, Y))`.
   Verdict: exact; continuity is the bundled `ContinuousMap` field.
3. **Bijection on path components.** Lean:
   `hπ₀ : Function.Bijective (componentsMap f)`.
   Verdict: exact. I opened `SSet.Enhanced.componentsMap` in
   `Sheaf.CategoryTheory.EnhancedDiagramsCones`: its target and source are
   `ZerothHomotopy`, and its quotient map uses path-connectedness witnesses.
   It does not use connected components.
4. **Isomorphisms of every positive homotopy group at every source point.**
   Lean: `hπ : ∀ (n : ℕ), 1 ≤ n → ∀ (x : X),
   Function.Bijective (homotopyGroupMap f n x)`.
   Verdict: exact quantifier order and range. I opened `homotopyGroupMap`:
   it sends a boundary-relative `GenLoop (Fin n)` class to its composite
   with f and sends its basepoint to `f x`. This operation preserves the
   first-coordinate concatenation defining the group law, so bijectivity
   states precisely group isomorphism, including the nonabelian n = 1 case.
5. **The specified real Euclidean spheres, including S^(-1).** Lean:
   `m : ℕ` and `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)`.
   Verdict: exact reindexing by ambient dimension m = r + 1; `dist v 0 = 1`
   is `‖v‖ = 1`. The EuclideanSpace primitive uses the Euclidean norm,
   not the supremum norm on an ordinary function space.
6. **Unbased continuous mapping spaces with the compact-open topology.**
   Lean: `C(sphere, X)` and `C(sphere, Y)`.
   Verdict: exact. I read `ContinuousMap.compactOpen` and `compactOpen_eq`
   in Mathlib: their generators are exactly `{h | MapsTo h L U}` with
   `IsCompact L` and `IsOpen U`. The elements are all continuous maps,
   with no restriction to constant maps or a distinguished based component.
7. **Apply kification to those mapping spaces.** Lean:
   `WithTopology C(sphere, X) (TopologicalSpace.compactlyGenerated.{max u v}
   C(sphere, X))`, and the analogous Y expression.
   Verdict: exact. I read the definition in Mathlib's
   `Topology.Compactness.CompactlyGeneratedSpace`: it coinduces the topology
   from the disjoint union of all continuous compact Hausdorff tests. This
   is precisely the notion used by the recorded
   `Sheaf.AlgebraicTopology.RealizationFiniteLimits` dependency; no weak
   Hausdorff modification is involved. `WithTopology` changes only the
   topology. The common compact-test universe `max u v` accommodates both
   mapping spaces and all real spheres, cubes, and their finite products,
   without requiring u = v or restricting either space to a smaller universe.
8. **Postcomposition induces the continuous map for each sphere.** Lean:
   `∀ (m : ℕ), ∃ g : C(kifiedSource, kifiedTarget),
   (∀ a, WithTopology.ofTopology (g a) = f.comp (WithTopology.ofTopology a)) ∧ ...`.
   Verdict: exact. The equation specifies the entire underlying function
   pointwise. Injectivity of `WithTopology.ofTopology` makes the bundled
   map unique, since continuous-map equality is function equality. Hence
   this existential states continuity of the canonical postcomposition
   function and its property; it cannot choose a different weak equivalence.
9. **That canonical map is a weak homotopy equivalence.** Lean:
   `Function.Bijective (componentsMap g) ∧ ∀ (n : ℕ), 1 ≤ n → ∀ x,
   Function.Bijective (homotopyGroupMap g n x)`.
   Verdict: exact; it uses the same component/group maps as the hypotheses,
   with every continuous sphere map as a possible source basepoint. The
   theorem does not apply the dependency's simplicial-map predicate to a
   topological map or assume any model-category structure.

Edge cases independently checked:

- m = 0 (r = -1): the zero-dimensional Euclidean space has only zero,
  whose norm is zero. Its unit sphere is empty. Both continuous-map spaces
  are singletons, even when X or Y is empty, as are their kifications.
- m = 1 (r = 0): the two-point sphere gives the full unbased mapping space;
  in particular it does not accidentally encode only the fibre of evaluation.
- X empty: component surjectivity forces Y empty. For m > 0 both mapping
  spaces are empty, their component map is bijective, and the positive
  group conclusion has no basepoints. The m = 0 singleton case is included.
- Point targets (the terminal/zero-dimensional test), disconnected targets,
  nonconstant sphere maps, and every possible mapping-space component are
  included. Positive group degree n = 1 is included; n = 0 is handled by
  the separate path-component clause rather than an unnecessary group law.
- No ring, scheme, characteristic, or algebraic index set occurs here.
  The empty sphere is the relevant empty-domain case. Universes u and v
  are both bound and independent, and the compact-test universe is explicit.

Independent H4 searches used different phrasing from the first worker:

- `msearch.py ... leanfinder`: "A weak equivalence of topological spaces is
  preserved by the free mapping space functor with a finite sphere as
  domain" returned eight hits: singular-simplex descriptions, abstract
  model-category path objects, generalized-loop definitions and sphere
  homotopy equivalences. None states this result.
- `msearch.py ... loogle 'HomotopyGroup, ContinuousMap'` returned five hits,
  all the existing group-law specifications or the loop/fundamental-group
  equivalence; no mapping-space preservation statement.
- `msearch.py ... grep 'postcomp.*(Bijective|[Ww]eak)|[Ww]eak.*postcomp'`
  returned 25 hits, principally abstract model-category postcomposition.
  I opened `LeftHomotopyClass.postcomp_bijective_of_weakEquivalence`:
  it assumes a model category, cofibrancy and fibrancy and concerns maps on
  abstract homotopy classes. It is not this topological sphere-space theorem.
- Direct `rg` in Mathlib Topology/AlgebraicTopology, the upstream
  `WeilConjectures`, and project `lean/Sheaf` for sphere/function-space/
  mapping-space homotopy or weak-equivalence terminology found no exact
  declaration. The project's TopologicalSerreModel module only cites this
  node as a proof input. I also read Mathlib `ContinuousMap.curry`,
  `uncurry`, `continuous_postcomp`, and the exact kification/WithTopology
  primitives rather than accepting the worker's naming claims.

Dependency and convention audit: `componentsMap` and `homotopyGroupMap` are
exactly the recorded definitions, reexported by the public realization import.
I read `SSet.realization_finite_limits` and its topology conventions and the
full signature of `SSet.Enhanced.homotopy_equivalence_weak`. The latter and
Mathlib CompactOpen are imported as proof inputs. The long-exact-sequence
node still has no recorded Lean declaration or Mathlib match; it is solely
a proof dependency, so there is no missing statement object or module to
supply here. The eight numbered docstring steps track all eight node steps,
including both exact-sequence chases and the component action/orbit argument.
Module and theorem docstrings name the source and blueprint id. There is
one named theorem with exactly one `sorry`, no new data definition or proved
helper, no hidden instance, no local notation, and no line over 100 columns.

Mismatches and changes: none in the node or Lean. I left both unchanged and
appended this independent reading to the report. The node's `lean.statement`
is verbatim equal to the theorem signature in the module (checked directly).

Validation: the required `scompile.py Q71
lem-coef-sphere-mapping-weak-equivalence <module>` invocation succeeded on the
server, compiling the module both as a sandbox file and at its library path,
1.4 seconds each. Output contains no errors and no non-sorry warnings.
