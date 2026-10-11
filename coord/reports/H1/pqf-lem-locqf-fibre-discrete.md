## Worker report

The module `lean/Sheaf/AlgebraicGeometry/FiniteDiscreteFiber.lean` states
`AlgebraicGeometry.Scheme.Hom.finite_discrete_fiber_and_isQuasiFiniteAtPoint`.
It introduces no definitions. Its sole theorem has proof `by sorry`.

Clause-by-clause rendering:
- Schemes X and S: `{X S : AlgebraicGeometry.Scheme.{u}}`, with explicit universe `u`.
- Morphism f: `(f : X ⟶ S)`.
- Point s in S: `(s : S)`; no closed-point restriction.
- Locally of finite type: `[AlgebraicGeometry.LocallyOfFiniteType f]`.
- Finite set-theoretic fibre at this point: `(hf : (f ⁻¹' {s}).Finite)`.
  This is only the specified fibre, not a hypothesis about all fibres.
- The scheme-theoretic fibre is a finite space: `Finite (f.fiber s)`.
- The same space is discrete: `DiscreteTopology (f.fiber s)`.
- Quasi-finite at every point lying over s:
  `∀ x : X, f x = s → IsQuasiFiniteAtPoint f x`.

Dependency declarations read and used:
- `pqf-def-quasifinite`: `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`,
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`. Its full definition uses
  affine neighbourhoods and a finite-type ring map quasi-finite at the prime.
  The same module also records `IsLocallyQuasiFinite`, `IsQuasiFinite` and
  `HasFiniteFibres`; these are not additional hypotheses of this theorem.
- `def-weil-pbc-scheme-conventions` is a pointer-only convention node (its
  `lean.convention` record has no module/declaration). We use its referenced
  Mathlib notions `AlgebraicGeometry.Scheme` in `Mathlib.AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`. Their definitions/docstrings
  were read. No replacement convention definition is needed.
- The fibre notion already occurs in `pqf-def-quasifinite` and the convention
  record: `AlgebraicGeometry.Scheme.Hom.fiber`, `Mathlib.AlgebraicGeometry.Fiber`.
  Read its signature, pullback definition and `fiberHomeo` docstring. The
  `def-pc-scheme-fibre` node (already a proof dependency) records the same notion.
  The sole import brings all these existing notions into scope.

Edge cases checked before writing: the empty scheme and the empty fibre give
finite discrete spaces with a vacuous pointwise conclusion. A singleton fibre
may be nonreduced or have nontrivial residue field extension: discreteness
concerns its underlying space, and no reducedness or rationality is asserted.
The point s can be nonclosed. No Noetherian, separated, quasi-compact, finite
morphism, nonempty fibre, or characteristic assumption is imposed. Arbitrary
scheme universe u is explicitly bound. There is no identified statement fault.

Searches for an existing statement:
- msearch.py leanfinder, query “A locally finite type scheme morphism with finite
  fibre at a point has finite discrete fibre and is quasi-finite at each point
  above it”: eight related hits, including `Scheme.Hom.discrete_fiber` and the
  finite-carrier fibre instance, both requiring an IsFinite morphism; no exact
  match for the statement here.
- msearch.py loogle, query `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt,
  DiscreteTopology`: zero hits.
- msearch.py grep, query `finite_preimage_singleton|discrete.*[Ff]iber|[Ff]iber.*discrete`
  in AlgebraicGeometry: eleven related hits. Read
  `LocallyQuasiFinite.of_finite_preimage_singleton`, which requires finiteness
  of ALL fibres and concludes Mathlib local quasi-finiteness, not this statement.
  Mathlib `Scheme.Hom.QuasiFiniteAt` is stalk-based and omits finite type;
  the recorded Stacks predicate is required here.
- msearch.py leansearch, query “locally finite type scheme morphism finite fibre
  discrete and quasi finite at points”: unavailable, Internal Server Error.
- rg in the source project's AlgebraicGeometry and this project's
  lean/Sheaf/AlgebraicGeometry for `quasi[Ff]inite|QuasiFiniteAt|
  pqf-lem-locqf-fibre-discrete`: related isolated-point/stratification lemmas,
  no identical statement.
- rg across all source `WeilConjectures` and project `lean/Sheaf` for
  `finite_discrete_fiber_and_isQuasiFiniteAtPoint|finite.*discrete.*fiber|
  finite.*discrete.*fibre|pqf-lem-locqf-fibre-discrete`: no matching declaration
  or node attachment (one unrelated docstring about a ring spectrum).
- rg for this item in `dag/lean_names_upstream.json`: no recorded attachment.

Source check: the blueprint source file is absent from this machine's
literature checkout. The node includes its complete statement and reviewed
proof. Independently opened https://stacks.math.columbia.edu/tag/01TH:
under locally finite type, being isolated in the fibre is equivalent to
quasi-finiteness at the point. This supports the final step of the recorded
proof. The module docstring carries all steps and their DAG node ids.

Validation: scompile.py H1 pqf-lem-locqf-fibre-discrete compiled this module on
the server in 1.6 seconds, exit code 0, with no warnings. No local compilation
or proof was performed. No new nodes, dependency modules, or statement
corrections were needed. The independent second reading is left to the
second reader.

## Second reading by H1

I independently read the sandbox node and module, the complete statements and
records of both statement dependencies, and their actual Lean declarations.
The blueprint Markdown is absent locally and its recorded public raw URL
returned 404. I fetched the pinned Stacks source `morphisms.tex` at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` into the sandbox scratchpad and read
`section-quasi-finite`, `definition-quasi-finite` (01TD),
`lemma-quasi-finite-at-point-characterize` (01TH), and
`lemma-finite-fibre` (lines 3728 onwards). The last lemma states exactly this
node: locally finite type, one finite set-theoretic fibre, finite discrete
scheme-theoretic fibre, and quasi-finiteness at each point over that point.
The section imposes no additional standing hypothesis. The separate online
01TD and 01TH pages agree with the pinned TeX.

Object, hypothesis, and conclusion checklist:

- Arbitrary schemes X and S: `{X S : AlgebraicGeometry.Scheme.{u}}`.
  Verdict: exact. Mathlib's Scheme is the convention node's recorded notion;
  the common explicitly bound universe is the scheme category's universe.
- A morphism f from X to S: `(f : X ⟶ S)`. Verdict: exact; no structure
  morphism over an unspecified field or additional base is substituted.
- An arbitrary point s of S: `(s : S)`. Verdict: exact; not only closed points.
- f locally of finite type: `[AlgebraicGeometry.LocallyOfFiniteType f]`.
  Verdict: exact. I read FiniteType.lean's class, which requires finite-type
  section maps on affine pairs. It does not require quasi-compactness.
- The specified set-theoretic fibre is finite: `(hf : (f ⁻¹' {s}).Finite)`.
  Verdict: exact; no assertion about any other fibre is assumed.
- X_s has finitely many underlying points: `Finite (f.fiber s)`.
  Verdict: exact. I read Fiber.lean: `fiber` is the pullback along
  `S.fromSpecResidueField s`, and `fiberHomeo` identifies its underlying space
  with the subspace `f ⁻¹' {s}`. This is also the recorded declaration of
  def-pc-scheme-fibre and the fibre convention in pqf-def-quasifinite.
- X_s has the discrete topology: `DiscreteTopology (f.fiber s)`.
  Verdict: exact; this concerns the actual scheme topology, not an arbitrarily
  installed discrete topology or reduced scheme structure.
- At every x lying over s, f is quasi-finite:
  `∀ x : X, f x = s → IsQuasiFiniteAtPoint f x`. Verdict: exact, including
  the order of quantifiers and the restriction to this one fibre.
  I read QuasiFiniteMorphism.lean's definition: affine U containing x,
  affine V, U ≤ f⁻¹V, the appLE algebra, finite type, and
  `Algebra.IsQuasiFiniteAtPrime` at `hU.primeIdealOf ⟨x, hx⟩`.
  I also read QuasiFiniteAtPrime.lean: the canonical fibre-spectrum point is
  isolated. This renders Stacks 01TD and its recalled algebra definition.
  No extra algebra or finite-type instance is imposed on the theorem's inputs.

The pointer-only scheme-conventions dependency fixes no new object; its
Mathlib Scheme and LocallyOfFiniteType declarations are the ones used here.
The pqf-def-quasifinite recorded module is imported and its actual predicate
is used, with no private copy. No missing notion, new definition node,
dependency module, or statement correction is needed.

Edge cases: X empty and an empty fibre give finite discrete spaces and a
vacuous pointwise conclusion. If S is empty there is no s to supply, exactly
as in the source. A singleton fibre may be nonreduced and may have a
nontrivial residue-field extension; neither is excluded. Nonclosed s is
allowed. All characteristics and arbitrary scheme universe u are covered.
There is no index set, numerical parameter, or characteristic binder to
restrict. In affine charts the zero ring gives an empty spectrum and is not
excluded. No Noetherian, separatedness, quasi-compactness, nonemptiness, or
field assumption on X or S has been added.

Independent searches (not merely the worker's searches):

- LeanFinder through msearch.py: `finite set theoretic fibre locally finite
  type morphism isolated points discrete topology`; eight results. The
  discrete-fibre theorem and finite-fibre instance require IsFinite f;
  they are stronger-hypothesis special cases, not this statement.
- Loogle through msearch.py: `AlgebraicGeometry.Scheme.Hom.fiber,
  DiscreteTopology`; zero results.
- LeanSearch through msearch.py: `scheme morphism locally of finite type
  finite fiber isolated point quasi finite`; service returned Internal
  Server Error, recorded as unavailable, with no mathematical verdict.
- Mathlib grep through msearch.py:
  `of_finite_preimage_singleton|quasiFiniteAt_iff_isOpen_singleton_asFiber|discrete_fiber`;
  fifteen results. I opened QuasiFinite.lean:303 and :395.
  `LocallyQuasiFinite.of_finite_preimage_singleton` assumes every fibre finite,
  whereas `quasiFiniteAt_iff_isOpen_singleton_asFiber` starts with an isolated
  point and uses Mathlib's stalk-based QuasiFiniteAt. Neither states this item.
- Independent rg of WeilConjectures/AlgebraicGeometry and this project's
  lean/Sheaf/AlgebraicGeometry for `isolated.*[Ff]ib|[Ff]ib.*isolated|
  finite_discrete|finite.*[Ff]ib|[Ff]ib.*discrete` found related finite,
  etale, isolated-point, and stratification statements, no exact statement.
  Exact declaration-name and blueprint-id rg over all WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json returned no attachment.

H5/H6/H8/H9: one theorem with `by sorry`, no definition or proof added.
Its module and declaration docstrings give the source and exact blueprint id.
The proof docstring follows the node's sole proof step: affine finite-type
maps, fibre-algebra base change and open fibre spectra, fibre homeomorphism,
finite-spectrum discreteness, the open-cover argument, and the affine
isolated-point criterion giving the recorded quasi-finite predicate; it names
all eight cited nodes. The single dependency import is used. Namespace and
file topic are appropriate; all lines are at most 100 characters; u, X, S,
f, s, hf, and x are explicitly bound. The node's lean.statement is verbatim
the theorem signature before `:=`.

Mismatches and changes: none found. The mathematical node, Lean module, and
Lean record are unchanged; this independent second-reading section is added.

Second-reader validation: scompile.py compiled the unchanged module on the
server in 2.5 seconds, exit code 0, without warnings. An exact string check
confirmed the recorded signature and a line-width check passed. The delivery
dry run printed OK: commit 7942021f4 passed preflight and compiled.
