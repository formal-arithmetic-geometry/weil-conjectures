## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricPureFibrePointDimension` states
`AlgebraicGeometry.geometric_pure_fibre_point_dimension`, with a single `sorry`.
It introduces no definitions, new nodes or dependency repairs, and changes only
`lean` on the item. The mathematical statement is unchanged.

Clause correspondence:

- The schemes and morphism are `{T B : Scheme.{u}} (g : T ⟶ B)`.
- Local finite presentation is `[LocallyOfFinitePresentation g]`; the dimension
  parameter is `(d : ℕ)`. There is no flatness or other finiteness hypothesis.
- Every nonempty geometric fibre is pure of dimension `d`: `hpure` quantifies
  over each `s : B` and every chosen field `Ω : Type u` with
  `[Algebra (B.residueField s) Ω] [IsAlgClosure (B.residueField s) Ω]`.
  It assumes `Nonempty` of the geometric fibre and concludes its
  `Scheme.IsPureDimension d`. In particular, this includes the canonical
  `AlgebraicClosure (B.residueField s)` and does not pick a special closure.
- The ordinary fibre is the recorded `g.fiber s`; its structure map is
  `g.fiberToSpecResidueField s`. The chosen algebraic closure map is
  `Spec.map (CommRingCat.ofHom (algebraMap (B.residueField s) Ω))`.
  The geometric fibre is expressed as the pullback of these two maps. This is
  exactly the equivalent base-change description explicitly allowed by
  `def-weil-geometric-fibre`, not the set of lifts used by the unrelated
  pro-etale geometric-fibre definition. Pullback pasting identifies it with
  `T ×_B Spec Ω`, and `pullback.fst` is its projection to the ordinary fibre.
  No arbitrary map or chosen existential comparison is introduced.
- `(x : T)` is arbitrary and `s` is written explicitly as `g x`, without a `let`.
  `g.asFiber x : g.fiber (g x)` is the point of the ordinary fibre corresponding
  to `x` under Mathlib's canonical `fiberHomeo`; its image under `fiberι` is `x`.
- Existence of a geometric lift is the first conjunct `∃ xbar, ... = g.asFiber x`,
  with the left side the application of `pullback.fst` to `xbar`.
- The second conjunct quantifies over every geometric-fibre point `xbar` and
  assumes exactly that same projection equation. It asserts
  `topologicalKrullDimAt (g.asFiber x) = topologicalKrullDimAt xbar` and
  `topologicalKrullDimAt xbar = (d : WithBot ℕ∞)`.
- The final conjunct states the advertised particular conclusion
  `topologicalKrullDimAt (g.asFiber x) = (d : WithBot ℕ∞)`.
  Both dimension functions are local topological dimensions (the infimum over
  open neighbourhoods), not local-ring dimensions.

Dependency interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its first projection, as recorded by
  `def-weil-geometric-fibre` (publicly available through the fibre module).
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`, which asks
  that every irreducible component with its subspace topology has dimension `d`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo` and `asFiber`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  the general chosen-closure predicate `IsAlgClosure` is from its public
  dependency `Mathlib.FieldTheory.IsAlgClosed.Basic`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.

The two non-Mathlib proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`, declaration
`AlgebraicGeometry.fibre_dimension_after_base_change`, and
`WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension`, declaration
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`.
The remaining proof dependencies use the Mathlib finite-type, ring-hom-property,
field-spectrum-surjectivity and pullback-surjectivity APIs imported by the
statement dependencies. The docstring gives all four node proof steps, including
surjective lifting and invariance for arbitrary lifts.

Source checked directly: `literature/stacks-project/algebra.tex`,
`lemma-dimension-at-a-point-preserved-field-extension` (Tag 00P4), and
`literature/stacks-project/varieties.tex`, `lemma-dimension-locally-algebraic`
(Tag 0A21), especially parts (3) and (5). The former preserves local topological
point dimension under field extension; the latter identifies local dimension
with the maximum component dimension through the point. No statement fault or
mathematical dispute was found.

Edge cases checked before writing:

- Empty `T` or `B`: the point binder has no instances; empty geometric fibres
  impose no condition. No nonempty-base or surjectivity hypothesis is added.
- Non-surjective `g`: fibres away from its image may be empty. For any specified
  `x`, the fibre at `g x` is nonempty and its algebraic-closure base change has
  a lift by faithful flatness/surjectivity of field extension.
- `d = 0` is admitted without modification.
- Generic and nonclosed points are included. For instance, the generic point
  of an affine line has local topological dimension one although its local
  ring has dimension zero; the statement uses the former in all clauses.
- Nonreduced fibres and arbitrary characteristic are included. Neither reducedness
  nor smoothness, flatness, separation or a Noetherian base is assumed.
- All schemes and their residue fields use the standard shared universe `u`;
  every algebraic closure in that universe is allowed. There is no unrelated
  smaller test universe or extra equality of universes.

Searches actually run:

- `msearch.py leansearch`, query "Pure geometric fibres imply constant local
  topological dimension on ordinary fibres": eight hits, including
  `AlgebraicGeometry.IsSmoothOfRelativeDimension.mk`, locally constant functions
  and vector-bundle local frames; none states this theorem.
- `msearch.py leanfinder`, query "Pure geometric fibres of a locally finitely
  presented morphism have constant local topological dimension d on ordinary
  fibres": eight hits, including `LocallyOfFinitePresentation`,
  `IsSmoothOfRelativeDimension`, the fibre preimmersion and Jacobson instances,
  and local finite type from finite presentation; none states this theorem.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.Hom.fiber, topologicalKrullDimAt`: zero hits; Loogle
  reported that `topologicalKrullDimAt` is unknown (it is a project declaration).
- `msearch.py grep`, query `IsPureDimension|topologicalKrullDimAt|equidimensional`
  in Mathlib `AlgebraicGeometry`: one hit, a comment in `AlgebraicCycle/Basic.lean`
  saying equidimensionality hypotheses cannot be assumed; no match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `geometric.*[Dd]imension|IsPureDimension|pure.*fibre`, followed by the narrower
  `pure.*fibre.*dimension|geometric.*pure.*fibre|pure.*geometric.*fibre`:
  existing purity definitions and various curve, smoothness and finite-stage
  applications, but no statement with this theorem's hypotheses and clauses.
  The pure-relative-dimension finite-stage theorem was read: its input is already
  ordinary-fibre purity and its conclusion is descent, not the present result.
- `rg` of the exact node id in `lean/WeilConjectures`, and of the proposed full
  declaration/module names in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no existing match.

Validation: every compile uses `scompile.py`. An initial compile detected ambiguous
scheme-to-type coercions in the geometric point binders; writing `↥(pullback ...)`
resolves that ambiguity without changing any mathematical object or hypothesis.
The final compiler and delivery-preflight results are recorded below.

Final `scompile.py` result: exit 0; both the sandbox check and the actual
library-module check passed, each in 1.8 seconds, with no errors or warnings.

## Second reading by Q61

The worker delivers directly; there is no separate worker second reading.
The maintainer provides the independent review, as required by the dispatch brief.
Author self-check against the open node and file: all seven statement dependencies
are reused, local finite presentation is the sole morphism hypothesis, nonempty
geometric-fibre purity is retained, the closure is arbitrary, a lift exists, the
comparison applies to every lift, and the ordinary-fibre conclusion is explicit.
The geometric fibre uses the equivalent iterated-pullback model stated by its
definition node; the ordinary point is `g.asFiber x`. The topological/local-ring
distinction and the empty-fibre case are preserved. No mathematical mismatch
was found. Only the explicit scheme-to-type coercions needed adjustment during
elaboration; no statement correction or dependency repair was needed.

Delivery dry run: `deliver2.py Q61 lem-trf-geometric-pure-fibre-point-dimension
--no-push` returned exit 0 and `OK (dry run)`: preflight and per-file compilation
passed. The packet contains only the module, the item's Lean-record update and
this report.
