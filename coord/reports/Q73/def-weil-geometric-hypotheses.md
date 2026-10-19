## Worker report

The module `Sheaf.Paper.GeometricHypotheses` introduces exactly one missing predicate,
`WeilConjectures.FiniteFieldDatum.IsSmoothOfPureDimension`. It has real data, no theorem
or `sorry`, and no new node is needed. The other two predicates in this bundle of
conventions already exist: use `AlgebraicGeometry.IsProper Y₀.hom` and
`AlgebraicGeometry.GeometricallyConnected Y₀.hom`. They are publicly available through
this module, and its module docstring identifies these exact expressions. Defining aliases
for them would duplicate the dependency notions.

The statement was checked against its recorded master blueprint source (order 412) and
against the current `main-20261015` copy (order 422); their mathematical text agrees.
No statement correction or disputed statement is needed. Only the item's `lean` field changes.

Clause-by-clause correspondence:

- The global tuple `(p,a,q,k₀,k)` is the binder
  `(D : WeilConjectures.FiniteFieldDatum.{u})`. Its recorded structure includes prime `p`,
  positive `a`, `q = p ^ a`, a field of cardinality `q`, and the fixed algebraic closure.
- A `k₀`-scheme is `(Y₀ : Over (Spec (CommRingCat.of D.k₀)))`; `Y₀.hom` is its
  specified structure morphism. This bundled form follows the geometric-fibre dependency.
- Finite type is `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`, exactly the
  conjunction prescribed by `def-weil-finite-type-morphism`.
- The nonnegative integer is `(d : ℕ)`, including zero.
- Smoothness of the structure morphism is the first conjunct, `Smooth Y₀.hom`.
  No relative-dimension predicate substitutes for the specified geometric-fibre condition.
- The geometric fibre is the recorded `D.geometricFiber Y₀`, with underlying scheme `.left`.
  Its dependency definition is `Over.pullback` along
  `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`, so this is precisely
  `Y₀ ×_{k₀} k` with the fixed inclusion.
- The second conjunct, `(D.geometricFiber Y₀).left.IsPureDimension d`, is the recorded
  `Scheme.IsPureDimension` predicate. Its body quantifies over every
  `Z : Set (D.geometricFiber Y₀).left` in `irreducibleComponents` and asserts
  `topologicalKrullDim Z = (d : WithBot ℕ∞)`. The subtype topology is the subspace topology.
- Properness reuses `IsProper Y₀.hom`: separatedness, universal closedness, and locally
  finite type are its fields. Universal closedness implies quasi-compactness, recovering
  the source's finite type; no new definition or stronger condition is imposed.
- Geometric connectedness reuses `GeometricallyConnected Y₀.hom`. Its defining
  `geometrically (ConnectedSpace ·)` tests all field-valued base changes.
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` identifies these, over
  `Spec k₀`, with base changes along every `[Field K] [Algebra D.k₀ K]`.
  `ConnectedSpace` includes `Nonempty`; the trivial extension gives nonemptiness of `Y₀`.
- The equivalent algebraic-closure clause is already stated by the imported dependency
  `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`, with
  `k = D.k₀`, `Ω = D.k`, and `X = Y₀.left` equipped with its given over-structure.
  `D.isAlgClosure` supplies algebraic closedness. The pullback is the underlying scheme of
  `D.geometricFiber Y₀`. Its `ConnectedSpace` includes the explicitly mentioned nonemptiness.
  `AlgebraicGeometry.GeometricallyConnected.nonempty_over_field` records the other
  nonemptiness implication. These dependency theorems are reused, not restated or proved.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.geometricFiber` (full definitions read, including the
  current source obtained with `scompile.py --source`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, together with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`; exported by the finite-field module.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, through pure dimension.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: the recorded dimension module;
  its `topologicalKrullDimAt` is read but is not the dimension needed here. The component
  dimension is the dependency's existing `topologicalKrullDim` from
  `Mathlib.Topology.KrullDimension`, not local dimension or dimension of the entire fibre.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`, with
  `IsSeparated` and `UniversallyClosed`.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.GeometricallyConnected`; the general `geometrically` signature and
  its field-algebra specialization in `Geometrically.Basic` were also read.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (nonemptiness included).
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure`:
  `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed` and
  `AlgebraicGeometry.GeometricallyConnected.nonempty_over_field`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the current source was
  read via `scompile.py --source`, including the full `moduleBaseChange` signature and
  docstring. That declaration is module base change, not the scheme base change used here.
  Scheme base change is the dependency's specified `Over.pullback`, already used by
  `FiniteFieldDatum.geometricFiber`. The existing finite-field and connectedness modules
  import the older side base-change module; this delivery does not additionally import the
  upstream module and so does not introduce duplicate base-change declarations.

Edge cases checked before writing: `d = 0` is included; the empty scheme has no irreducible
components and so satisfies pure dimension for every `d` (smoothness remains the first
conjunct). It is excluded by geometric connectedness because connectedness includes
nonemptiness. Neither properness nor smoothness is silently assumed when defining the
other independent hypotheses. Disconnected fibres may have multiple components, but every
component must have the same prescribed dimension. Infinite component dimension does not
equal any `(d : WithBot ℕ∞)`. Universe `u` is explicit and shared with the recorded datum,
schemes, and dependency base change; no independent smaller test-field universe is added.
No file-local notation, instance, or private definition is used.

Searches for existing statements (all via the prescribed Q73/item wrapper where applicable):

- `msearch.py ... leansearch "smooth scheme pure dimension geometric fiber irreducible components"`:
  eight results, concerning smoothness and finite irreducible components, with no predicate
  giving the specified conjunction.
- `msearch.py ... leanfinder "scheme over finite field smooth of pure dimension geometric fiber equidimensional proper geometrically connected"`:
  eight results, including `IsSmoothOfRelativeDimension` and properness results; none matches
  smoothness together with the recorded pure-dimension-of-fixed-fibre condition.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.GeometricallyConnected"`:
  zero results. Remote search indexes use some older `IsSmooth` names; local source signatures
  were read to verify the actual pinned `Smooth` declaration.
- `msearch.py ... grep "IsSmoothOfPureDimension|[Gg]eometric[Hh]ypotheses|[Pp]ure[Dd]imension|[Ee]quidimensional" AlgebraicGeometry`:
  one unrelated comment in `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`.
- `rg -n` with `def-weil-geometric-hypotheses|IsSmoothOfPureDimension|Smooth.*PureDimension|[Gg]eometric[Hh]ypotheses`
  in the upstream `WeilConjectures`, the side `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no matches. `grep -rn "def-weil-geometric-hypotheses"` in upstream `WeilConjectures`:
  no matches. These searches establish that the proposed declaration name and conjunction
  are new; properness, geometric connectedness, and pure dimension reuse existing declarations.

Validation: the prescribed `scompile.py Q73 def-weil-geometric-hypotheses
lean/Sheaf/Paper/GeometricHypotheses.lean` compiled both the sandbox probe and library-path
module cleanly (each about 1.6 seconds), with no errors or warnings. Delivery dry-run result
is recorded below when complete. No delivery was pushed; independent second reading remains
for the second reader.

## Second reading by Q73

I independently read the sandbox node and module against the master blueprint source,
order 412, at
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-comp-category/def-weil-geometric-hypotheses.md`.
The source has no surrounding hypotheses beyond the global finite-field datum and the
finite-type scheme it explicitly introduces. I also read Stacks `topology.tex`,
Definition `definition-equidimensional` (0058), and `varieties.tex`, Definition
`definition-geometrically-connected`, its nonempty convention, and Lemmas 0387 and 054N.
These introduce no extra smoothness, properness, connectedness, or Noetherian assumption.

My object/hypothesis/clause list and independent correspondence check is:

- Global datum `(p,a,q,k₀,k)`: `D : WeilConjectures.FiniteFieldDatum.{u}`. I opened the
  full structure and its current source using `scompile.py --source
  Sheaf.Paper.FiniteFieldFiber`: it has prime `p`, `1 ≤ a`, `q = p ^ a`, a finite field
  `k₀` with `Nat.card k₀ = q`, and the fixed algebraic closure `k` with its algebra
  structure. Verdict: exact dependency object, no extra field hypothesis.
- Scheme with its specified map to `Spec k₀`: `Y₀ : Over (Spec (CommRingCat.of D.k₀))`.
  Its scheme is `Y₀.left` and its structure morphism is `Y₀.hom`. Verdict: exact,
  using the permitted bundled scheme-over-base convention.
- Finite type of that structure map: `[LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom]`. I read these Mathlib signatures and the recorded finite-type
  node: they give its two required conditions. Verdict: exact, with no separatedness
  or smoothness assumed.
- Nonnegative dimension: `(d : ℕ)`. Verdict: exact, including zero.
- Smoothness of the structure map: the first conjunct `Smooth Y₀.hom`. I read the
  recorded `Mathlib.AlgebraicGeometry.Morphisms.Smooth` declaration; it is the scheme
  smoothness predicate, not a local-ring formal-smoothness condition. Verdict: exact.
- Fixed geometric fibre: `(D.geometricFiber Y₀).left`. I opened the dependency's body:
  it is `Over.pullback` along `Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))`.
  Verdict: precisely the specified `Y₀ ×_{k₀} k`, not an arbitrary fibre or closure.
- Every irreducible component of that fibre has dimension `d`: the second conjunct
  `(D.geometricFiber Y₀).left.IsPureDimension d`. I opened the pure-dimension module;
  its body is `∀ Z : Set X, Z ∈ irreducibleComponents X →
  topologicalKrullDim Z = (d : WithBot ℕ∞)`. I also read Mathlib's
  `irreducibleComponents` (maximal `IsIrreducible` subsets) and `topologicalKrullDim`
  (Krull dimension of irreducible closed subsets). `Z` has the subtype topology.
  Verdict: exact quantifiers and dimension of each component, not of the whole fibre.
- Properness: the existing expression `AlgebraicGeometry.IsProper Y₀.hom`, identified
  in the module docstring. I opened its class: it extends `IsSeparated`,
  `UniversallyClosed`, and `LocallyOfFiniteType`. I checked the instance
  `[UniversallyClosed f] : QuasiCompact f` in `Morphisms/UniversallyClosed.lean`.
  Verdict: exactly separated, finite type, universally closed; no duplicate definition.
- Geometric connectedness, including nonemptiness of `Y₀`: the existing expression
  `AlgebraicGeometry.GeometricallyConnected Y₀.hom`, identified in the module docstring.
  I opened `Geometrically/Connected.lean`, `Geometrically/Basic.lean`, and
  `ConnectedSpace`. The former class is `geometrically (ConnectedSpace ·)`;
  `geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` gives all field-algebra
  extensions of the base, and `ConnectedSpace` has `toNonempty`. The trivial extension
  includes connectedness and nonemptiness of `Y₀` itself. Verdict: exact, without
  adding smoothness or properness to this independent predicate.
- Equivalent fixed-algebraic-closure test: the imported recorded dependency
  `AlgebraicGeometry.geometricallyConnected_iff_connectedSpace_of_isAlgClosed`, whose
  full signature and proof docstring I opened, says precisely that geometric
  connectedness is equivalent to `ConnectedSpace` of the pullback along `k₀ → k`.
  `D.isAlgClosure` supplies the required algebraically closed field instance, and the
  over-structure is the one specified by `Y₀.hom`. The pullback is the underlying scheme
  of `D.geometricFiber Y₀`. `ConnectedSpace` includes the stated nonemptiness clause;
  the same module's `GeometricallyConnected.nonempty_over_field` covers the original
  scheme. Verdict: exact reused statement; no theorem was restated or proved here.

I read all eleven dependency nodes, including the base-change record's note: its main
declaration `moduleBaseChange` is for modules, whereas this item needs scheme base change,
which the record explicitly assigns to `Over.pullback` and the fibre dependency uses.
Thus the similarly named main declaration is not mistaken for the required construction.
The component and connected-space leaves use the Mathlib notions described above.
There are no new nodes or dependency modules in this delivery and no statement correction
or `statement_change`; no citer audit is therefore required.

Edge cases: the empty fibre has no irreducible components, so pure dimension is vacuous
for every `d`, as required; the geometric-connectedness predicate excludes the empty
scheme. `d = 0` is present. Multiple components are each tested with the same `d`;
infinite dimension cannot equal its finite cast. There is no indexing type or separate
zero-object construction here. The characteristic is unrestricted beyond the recorded
prime and finite-field datum, including characteristic two. The sole universe `u` is
explicit and matches the datum, schemes, and dependency base change. The field tests use
the ambient scheme universe from the existing geometric-connectedness API, not an
independent smaller universe. No unbound variable, universe equation, hidden instance,
or additional nonemptiness requirement was introduced.

Independent searches, using different queries from the worker:

- `msearch.py Q73 def-weil-geometric-hypotheses leanfinder "predicate smooth over finite
  field all components base change algebraic closure same dimension"`: eight results,
  about smooth algebras and standard smooth relative dimension, no matching predicate.
- `msearch.py ... leansearch "A scheme is smooth and every maximal irreducible subset
  after extension to an algebraic closure has dimension d"`: eight results, smoothness
  and relative-dimension classes, no conjunction on the recorded fixed geometric fibre.
- `msearch.py ... grep "IsSmoothOfPureDimension|geometric hypotheses|Smooth.*PureDimension"`:
  zero matches.
- `rg -n -i 'equidimen|pure.?dim|smoothof.*dim|smooth.*pure'` in upstream
  `WeilConjectures/AlgebraicGeometry`, Mathlib `AlgebraicGeometry`, and project
  `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/Paper`, plus the broader project
  `rg -n -i 'equidimen|pure.?dim|smooth.*pure|pure.*smooth'`: only component-dimension
  predicates, their users, and relative smoothness declarations. I opened
  `SmoothOfRelativeDimension`: it uses affine standard-smooth charts, not the literal
  fixed-fibre conjunction of this node. The existing `Scheme.IsPureDimension` is already
  reused. The new declaration's exact full name is absent from upstream and project Lean.

Verdict: no mathematical or convention mismatch found. The definition contains real
propositional data and no `sorry`, choice, auxiliary proof, private definition, or local
notation. Its source/blueprint docstrings are present; this definition node has an empty
proof list, so no proof steps are omitted. The node's `lean.statement` matches the file's
signature verbatim. I preserved the correct Lean module and node record; this second
reading adds only this independent audit and the validation results below.

Second-reader validation: `scompile.py Q73 def-weil-geometric-hypotheses
lean/Sheaf/Paper/GeometricHypotheses.lean` passed for both sandbox and library module,
each in 1.6 seconds, with no errors or warnings. A text comparison confirmed exact
signature equality with `lean.statement` and the 100-character Lean line limit.

Delivery dry run: `deliver2.py Q73 def-weil-geometric-hypotheses --no-push` printed
`OK (dry run): commit 3905818aba passes the preflight and compiles; nothing pushed`.
