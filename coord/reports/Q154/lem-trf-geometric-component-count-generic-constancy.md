## Worker report

The module `Sheaf.TraceFormula.GeometricComponentCountGenericConstancy` states
`AlgebraicGeometry.geometricFibreComponentCount_genericConstancy`, with its sole proof
`sorry`. It is the unchanged statement of
`lem-trf-geometric-component-count-generic-constancy`, Stacks Tag 055A, using the geometric
irreducible-component convention of Tag 0556. Both statements and the complete 055A proof
were read in `literature/stacks-project/more-morphisms.tex`. No new nodes, dependency repairs,
or statement corrections are needed.

Hypothesis and clause correspondence:

- Schemes and their morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Finite type is precisely `[LocallyOfFiniteType f] [QuasiCompact f]`, the conjunction
  recorded by `def-weil-finite-type-morphism`. There are no flatness, separatedness,
  Noetherianity, irreducibility, or nonemptiness assumptions on the original schemes.
- The arbitrary point is `(y : Y)`.
- The closure is `closure ({y} : Set Y)`. Its subtype has the induced topology, and
  `V : TopologicalSpace.Opens ↥(closure ({y} : Set Y))` is a relatively open subset,
  not an ambient open or a neighbourhood imposed on the original base.
- `(V : Set ↥(closure ({y} : Set Y))).Nonempty` is the required nonemptiness.
- `∃ n : ℕ` is the finite nonnegative integer, including zero.
- `∀ (t : ↥(closure ({y} : Set Y))), t ∈ V → ...` ranges over exactly its points.
- `Y.residueField t.val` is the recorded residue field κ(t).
- `(K : Type u) [Field K] [Algebra (Y.residueField t.val) K]
  [IsSepClosure (Y.residueField t.val) K]` is an arbitrary separable closure and its
  specified scalar embedding. `IsSepClosure` asserts separable closedness and algebraic
  separability (the latter implies algebraicity). The field map is necessarily injective.
- `f.fiberToSpecResidueField t.val` is the structure map of the actual scheme-theoretic
  fibre `f.fiber t.val`. Its pullback along
  `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField t.val) K))` is literally
  `X_t ×_{Spec κ(t)} Spec K`, with no replacement by a set of rational points.
- `irreducibleComponents ↥(pullback ...)` is the set of maximal nonempty irreducible
  subsets of that scheme's underlying space. `ENat.card ... = (n : ℕ∞)` says that it has
  exactly n members, and excludes infinity. In particular it does not identify the
  infinite case with zero, as `Nat.card` alone would.
- The same existentially chosen `V` and `n` precede the universal choices of `t` and `K`.
  Thus constancy and independence from all separable-closure choices are both retained.
  `Type u` is the residue field's universe; it admits its separable closure, and does not
  quantify over a smaller independent universe that could make the assertion vacuous.
  All universes and variables are explicitly bound (`autoImplicit false`).

Statement dependencies used, with their signatures and docstrings read in source:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (imported by FiniteType).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`,
  `Scheme.Hom.fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`; existence for schemes is provided through Fiber.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, whose docstring explicitly identifies the
  node's separable closure with Mathlib `IsSepClosure`; that class is used directly.

The already stated proof-dependency modules are imported without `public`: reduced induced
closed subscheme, generic component splitting, geometric generic cover spreading, etale generic
residue-field model, geometric-fibre count base change, ordinary generic component lower bound,
and Mathlib Noetherian, PullbackCarrier, UnderlyingMap and UniversallyOpen. The theorem
contains the node's seven-step proof plan in its docstring, including the zero-component case,
the ordinary-to-geometric lower-bound comparison, and descent through the open etale image.
No new supporting theorem or arbitrary canonical-map assumption is introduced.

Edge cases checked: empty source gives `n = 0`; empty base admits no `y`; the closure of a
chosen point is nonempty even over a non-Noetherian or nonreduced base. Empty fibres are
allowed. Irreducibility here is the nonempty notion, so an empty geometric fibre has no
components. A constant disjoint union of r affine spaces has count r. The real family
`Spec ℂ → Spec ℝ` distinguishes the ordinary count one from geometric count two. Two
crossing lines distinguish connected components from irreducible components. The punctured
identity over the affine line shows why shrinking is allowed and no equality is asserted at
all specializations. No finite-presentation or flatness restriction has been introduced.

Searches performed using the prescribed wrapper:

- LeanFinder: "For a finite type morphism of schemes the number of geometric irreducible
  components of fibres is constant on a nonempty relatively open subset of the closure of
  every point". Eight hits concern finite/discrete fibres, Jacobson fibres, specializing
  maps and closed-point images; none states generic constancy.
- Loogle: `irreducibleComponents, IsSepClosure`. Zero hits.
- LeanSearch: "The number of geometric irreducible components of a finite type scheme
  morphism is generically constant". Eight hits concern finite component sets and generic
  points; no generic constancy theorem.
- Mathlib grep: `geometric.*component|component.*generic|055A` in AlgebraicGeometry.
  Three hits, in Geometrically/Reduced and Properties, concern geometric reducedness or
  generic-point stalks, not the requested statement.
- Direct `rg` in the upstream `WeilConjectures/` and side `lean/Sheaf/` for geometric
  component, component count, generic component and the exact node id found no exact
  declaration. `GeometricFibreComponentCountBaseChange` is Tag 0556, and
  `GenericFibreComponentLowerBound` is Tag 0554; neither asserts this generic constancy.
  `GeometricallyIrreducibleFibreLocus` is the downstream constructibility theorem, not
  this lemma. Nearby geometric connected-component count modules count different objects.
- The proposed full declaration name was searched in Mathlib, upstream, side Lean and
  `dag/lean_names_upstream.json`; no collision was found.

Validation: prescribed `scompile.py Q154 lem-trf-geometric-component-count-generic-constancy`
compiled the module cleanly as both sandbox and library (1.9 s and 2.1 s), with no errors or
warnings. The wrapper compiled the already published lower-bound overlay as required.
The item's JSON differs only in `lean`, with the exact multiline signature from the file.

## Second reading by Q154

Author self-check, as permitted for dispatcher workers; independent mathematical review belongs
to the maintainer. I reread the node and the final Lean signature side by side. The pair of finite
 type classes matches finite type; no stronger geometric assumption is present. The open lives
in the closure subtype and is separately nonempty. The natural number is existential, and the
universal closure choice occurs after it, so changing choices cannot change the value or open.
The pullback uses the fibre's second projection to its residue-field spectrum, exactly matching
the iterated base change in the node. Components are irreducible rather than connected, and
extended-natural cardinality equal to a natural number enforces finiteness as well as equality.
There is one postponed theorem and no data definition. All dependency notions are reused.
No mismatch was found and no mathematical statement was changed.
