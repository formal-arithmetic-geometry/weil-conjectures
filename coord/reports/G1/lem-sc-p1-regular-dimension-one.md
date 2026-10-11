## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveLineRegularDimensionOne` states
`AlgebraicGeometry.ProjectiveLine.noetherian_regular_dim_one`; its only proof is `sorry`.
No definitions, extra nodes, or dependency modules are introduced, and no node statement
is changed.

Hypothesis and clause correspondence:

- “Let k be a field”: `(k : Type u) [Field k]`, with explicit arbitrary universe `u`.
- “P¹_k”: `let X := ProjectiveLine (Spec (.of k))`, the projective-line construction
  underlying the recorded `def-sc-p1-standard` declaration. The import is its recorded
  module `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`; its
  `AlgebraicGeometry.ProjectiveLine.TwistData` docstring identifies the same scheme and
  standard cover. No twist data are hypotheses of this theorem.
- “Noetherian (quasi-compact and locally Noetherian)”: the first two conjuncts are
  `CompactSpace X` and `IsLocallyNoetherian X`. CompactSpace imposes no Hausdorff condition;
  the locally Noetherian class is equivalent to the existence of a Noetherian affine cover.
- “regular”: the third conjunct is
  `∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)`.
  This is literally the one-line specialization in the dependency's `mathlib_match.how`.
  `IsRegularRing` extends `IsNoetherianRing`, so the coordinate ring's Noetherian clause
  is included. No redundant regular-scheme predicate is defined.
- “its dimension is 1”: the fourth conjunct is `X.dim = 1`, using the recorded local-ring
  supremum definition, with value in `WithBot ℕ∞`, not merely an upper bound or a relative
  smooth dimension.

Dependency declarations and source inspected:

- `def-sc-p1-standard`: `AlgebraicGeometry.ProjectiveLine.TwistData` in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`, lines 202–224;
  inspected its full structure and docstring. Its base scheme is arbitrary; specialize
  the underlying `ProjectiveLine` to `Spec k`. Also inspected the underlying abbreviation
  in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, line 401, with two homogeneous
  coordinates indexed by `ULift (Fin 2)`.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter`, lines 280–285, the underlying-space condition with no
  separation assumption.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `Mathlib.AlgebraicGeometry.Noetherian`, lines 56–59; also read the affine-cover theorem
  and equivalences at lines 103–135. This is the dependency's recorded existing declaration.
- `def-weil-regular-scheme`: `IsRegularRing`,
  `Mathlib.RingTheory.RegularLocalRing.Defs`, lines 90–94; also read the regular-local-ring
  definition at lines 48–54. Used the affine-neighbourhood specialization explicitly
  supplied by this dependency's Mathlib match.
- `def-pc-dimension`: `AlgebraicGeometry.Scheme.dim`,
  `Sheaf.AlgebraicGeometry.Dimension`; inspected its docstring and full definition as
  `⨆ x : X, ringKrullDim (X.presheaf.stalk x)`.

The local Stacks TeX is not present in this checkout. Read the source online at
https://stacks.math.columbia.edu/tag/01JE: Example 26.14.4 constructs the projective line
by gluing two polynomial-ring spectra along the inverse-coordinate identification.
The declaration docstring includes all four steps of the DAG proof and names all their
non-elementary inputs.

Edge cases checked: any field, finite or infinite, any characteristic, perfect or imperfect,
is permitted. A field is nontrivial, so the zero ring is excluded exactly by the source's
field assumption. P¹ has the point represented by `(t)` on an affine chart, so the dimension
supremum is nonempty. Its generic point has stalk dimension zero and closed chart points
have dimension one; the statement does not assert every stalk has dimension one. Both
charts, including infinity, are covered by the pointwise existential. No connectedness,
smoothness, algebraic-closedness, or finite-dimensionality assumption is added.

Searches actually run:

- `msearch.py ... leansearch "projective line scheme over a field regular Noetherian dimension one"`:
  unavailable, Internal Server Error; no match established by this tool.
- `msearch.py ... leanfinder "projective line over a field is regular Noetherian and has dimension one"`:
  eight hits on linear projectivization cardinalities/finrank and field ring dimension;
  none is this scheme theorem.
- `msearch.py ... loogle "AlgebraicGeometry.ProjectiveLine, IsLocallyNoetherian, IsRegularRing"`:
  zero hits, unknown identifier `AlgebraicGeometry.ProjectiveLine`.
- `msearch.py ... grep "ProjectiveLine|projectiveSpace.*regular|projective.*dimension" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` of source `WeilConjectures` for ProjectiveLine and regularity/dimension, and of
  repository `lean/Sheaf` and `dag/lean_names_upstream.json` for the combined assertion:
  no exact statement. Source `ProjectiveSpace.Curve` states only
  `topologicalKrullDim_projectiveLine_le_one`, not equality of the local-ring supremum;
  source `ProjectiveSpace.LineSmooth` gives smoothness and integrality. Source
  `AlgebraicGeometry.Regular` defines `IsRegular` by regular stalks, but our statement
  uses the existing dependency's explicit affine formulation without introducing a copy.
- `grep -rn "lem-sc-p1-regular-dimension-one"` of source `WeilConjectures`: no hit.
- Checked the proposed full declaration name against Mathlib, source and project Lean:
  no collision.

No STATEMENT-DISPUTED finding or node fault. Validation: `scompile.py` returned exit code 0 (compiled in 1.7 s), with no
errors or warnings. `deliver2.py --no-push` printed OK: the commit compiles and
passes preflight except for the independent second reading, which the second reader
writes. Nothing was pushed.

## Second reading by G1

I independently opened the item, all five statement-dependency nodes and their
recorded declarations, the delivered Lean, and the original Stacks TeX fetched
read-only from https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex
at `example-projective-line`. The local literature checkout has no Stacks TeX.
The source introduces an arbitrary field and glues Spec k[x] to Spec k[y] with
inverse coordinates; there is no algebraic-closedness, perfectness, characteristic,
or infinitude assumption. I also read Properties `definition-regular` in its raw
TeX, and Tags 00OQ and 00KG online. The source supports the node as written.

Object, hypothesis and conclusion checklist (all verdicts PASS):

- Object/hypothesis: an arbitrary field k. Lean `(k : Type u) [Field k]`, with
  explicitly declared `universe u`, introduces precisely that object and assumption.
  No additional instance or premise is required.
- Object: P¹_k = Proj k[x₀,x₁]. Lean `let X := ProjectiveLine (Spec (.of k))`
  uses the projective line underlying the recorded `ProjectiveLine.TwistData`
  declaration of def-sc-p1-standard, not a newly defined scheme or supplied twist.
  I opened TransitionUnits, including all TwistData fields, and ProjectiveSpace:
  the latter's `ProjectiveLine` is the relative integral-model construction with
  coordinate index `ULift (Fin 2)`, hence two homogeneous coordinates. Its standard
  affine charts identify the object with the two-chart projective line intended
  here. The source notes that its direct absolute-Proj comparison is not yet
  implemented; that missing comparison proof is not an extra hypothesis or a
  different geometric statement. We use the dependency's existing construction.
- Conclusion: quasi-compact. Lean `CompactSpace X` uses the recorded CompactSpace
  definition of def-weil-pbc-quasi-compact-scheme. I read its `isCompact_univ`
  field in Mathlib.Topology.Defs.Filter: it adds no Hausdorff condition.
- Conclusion: locally Noetherian. Lean `IsLocallyNoetherian X` is the recorded
  pqf-def-locnoeth predicate. I read its `component_noetherian` field and
  `isLocallyNoetherian_of_affine_cover` / `isLocallyNoetherian_iff_of_affine_openCover`:
  its every-affine-open formulation is equivalent to the node's existence of
  a Noetherian affine cover. Together with CompactSpace this is exactly the
  stated Noetherian-scheme conclusion.
- Conclusion: regular. Lean
  `∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing Γ(X, U)`
  preserves the point-before-neighbourhood quantifier order and requires a regular
  Noetherian coordinate ring on an affine neighbourhood of every point. I read
  def-weil-regular-scheme's statement and mathlib_match.how, and the complete
  Mathlib IsRegularLocalRing and IsRegularRing signatures: IsRegularRing extends
  IsNoetherianRing and requires regular localizations at every prime. Thus the
  Noetherian clause is present, with no added hypothesis. This is the dependency's
  explicit one-line scheme specialization, not a private regularity definition.
- Conclusion: dimension exactly one. Lean `X.dim = 1` uses def-pc-dimension's
  recorded Scheme.dim. I opened Sheaf.AlgebraicGeometry.Dimension and its data
  `⨆ x : X, ringKrullDim (X.presheaf.stalk x)`. Equality in WithBot ℕ∞ states the
  supremum is exactly one, not merely a bound or a relative dimension.

Edge cases: arbitrary small or large field universes are admitted by `Type u`
and the lifted two-coordinate index; there is no independent testing universe
that could make a hypothesis vacuous. Finite fields, characteristic two, arbitrary
positive characteristic, characteristic zero, and imperfect fields are included.
A zero ring cannot be a Field, just as in the source. The empty scheme and an
empty coordinate index are not objects of this node: the index has two elements,
and the chart prime (t) supplies a point over every field. The generic point has
stalk dimension zero; the theorem only requires the supremum to be one. Infinity
is included in the point quantifier. No varying n or n = 0 case is silently excluded:
the statement is specifically P¹, not a theorem parametrized by n.

Independent searches, using different queries from the worker:

- `msearch.py G1 lem-sc-p1-regular-dimension-one leanfinder "The scheme Proj of
  the homogeneous polynomial algebra in two variables over any field is a
  Noetherian regular curve of Krull dimension 1"`: eight results, including Proj
  and its finite-type/proper/quasi-compact structure maps; no exact theorem.
- `msearch.py ... loogle "IsRegularRing, Polynomial"`: the sole result is
  Polynomial.isRegularRing_of_isRegularRing, a ring theorem, not this scheme fact.
- `msearch.py ... grep "Proj.*regular|projective.*Noetherian|projective.*dim.*one"
  AlgebraicGeometry`: zero hits. Independently ran rg over source WeilConjectures,
  repository lean/Sheaf, and Mathlib/AlgebraicGeometry for projective-line,
  regularity, Noetherianity and dimension alternatives; no combined theorem.
  Opened source ProjectiveSpace.Curve: its theorem gives only topological
  dimension ≤ 1. Opened LineSmooth: smoothness of relative dimension one and
  integrality are not this four-clause statement with the local-ring supremum.
  Also opened source Regular's IsRegular signature. It is a stalkwise predicate;
  without local Noetherianity it does not carry the dependency's whole general
  regular-scheme definition. No duplicate predicate is introduced in this delivery.
- The worker's LeanSearch service failure remains documented above; successful
  independent LeanFinder, Loogle and grep searches supplement it.

H5–H9: there are no new definitions or hollow data, no proved theorem, and just
one named theorem with `by sorry`. Module and declaration docstrings identify
01JE and the blueprint item. The four proof paragraphs faithfully retain the
node's four steps, including the lower dimension bound from (0) < (t) and the
named dependencies. Imports supply the projective line, locally Noetherian
class, regular-ring class and scheme dimension; none is extraneous. All variables
and the sole universe are bound, lines are at most 100 characters, and the full
name has no collision. The node lean.statement was checked byte-for-byte against
the signature. No new nodes, dependency modules or statement correction are
present, so H12/H13 and the corrected-citer checks are inapplicable.

Mismatches found: none. Changes: appended this independent review only; left
correct Lean and node fields untouched. Validation is recorded below.

Second-reader validation: scompile.py compiled the delivered module in 1.7 seconds
with exit code 0 and no warnings. deliver2.py --no-push printed
`OK (dry run): commit 79ffea5f8 passes the preflight and compiles; nothing pushed`.
