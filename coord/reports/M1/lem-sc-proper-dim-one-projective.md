## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.ProperProjective` states
`AlgebraicGeometry.isProjective_of_isProper_of_dim_le_one`, with proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:
- A field k: `{k : Type u} [Field k]`, for an explicitly declared universe u.
- A scheme X over k: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. The morphism f is the
  given structure map; no chosen or canonical structure is assumed.
- Proper over k: `[IsProper f]`, exactly Mathlib properness. Its universally closed
  component implies quasi-compactness, so its locally finite type component is finite type.
- Topological Krull dimension at most one: `(hdim : X.dim ≤ 1)`, using the recorded
  dependency's `Scheme.dim`. The dependency module's `Scheme.dim_eq_topologicalKrullDim`
  identifies it with the topological dimension, including the empty scheme.
- An integer N ≥ 0 and a closed immersion into projective N-space over k:
  `IsProjective f` includes `IsHProjective.exists_closedImmersion`, whose signature is
  `∃ (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)), IsClosedImmersion i ∧
  i ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = f`, specialized to `S = Spec (.of k)`.
  Thus n includes zero, there are n+1 homogeneous coordinates, and the equation says
  the closed immersion is over k.
- Equivalently projective over k: the conclusion is `IsProjective f` itself, exactly
  the convention of def-pc-projective-morphism. Its additional quasi-compactness is
  already implied by the properness hypothesis, not an added restriction.

Dependency declarations used, all read with full signatures and docstrings:
- def-pc-dimension: `Sheaf.AlgebraicGeometry.Dimension`, `AlgebraicGeometry.Scheme.dim`;
  its dimension/topological-dimension identification is also read in that module.
- def-pc-projective-morphism: `Sheaf.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective` and its parent `AlgebraicGeometry.IsHProjective`.
- def-weil-proper-morphism: Mathlib leaf, `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`. The leaf has no lean record; mathlib_match is usable.

Source: https://stacks.math.columbia.edu/tag/0A26, Lemma 33.43.4, read directly because
this machine does not have literature/stacks-project/varieties.tex. The lemma asserts
H-projectivity of a proper scheme of dimension at most one over a field. The node's
projectivity convention is equivalent under properness. The module docstring carries
both steps of the node's proof and names every proof dependency they use.

Edge cases checked before writing:
- Empty X: no Nonempty binder; Scheme.dim is the empty supremum, hence bottom, and
  the conclusion permits the empty closed subscheme of projective space.
- Dimension zero: allowed by ≤ 1, including finite field schemes and nonreduced
  finite schemes; there is no equality-to-one or integrality hypothesis.
- Dimension one: singular, reducible, nonreduced, and disconnected proper schemes
  are included. No smoothness, connectedness, geometric condition, or characteristic
  assumption is imposed.
- Any field, including finite and imperfect fields, is allowed.
- Projective N-space includes N = 0; natural n encodes precisely an integer N ≥ 0.
- Universe u is arbitrary; field and scheme use the library's common universe
  convention. All variables and universes are explicitly bound.

Searches for an existing statement:
- msearch.py leanfinder, query "A proper scheme of dimension at most one over a field
  is projective": eight hits, including properness of Proj, proper/affine finite
  criterion, and compactness of universally closed schemes; no matching theorem.
- msearch.py loogle, query "AlgebraicGeometry.IsProper": twelve results, the proper
  class and closure properties; no projectivity theorem.
- msearch.py grep, query "projective_of_isProper|IsProjective|dim.*projective" in
  AlgebraicGeometry: zero Mathlib hits.
- msearch.py leansearch, query "proper scheme over a field dimension at most one
  projective": service unavailable (Internal Server Error); no verdict assigned.
- rg of `projective_of|IsProjective|krullDim` in source WeilConjectures/AlgebraicGeometry
  and repository lean/Sheaf/AlgebraicGeometry: existing projective definition and
  curve dimension hypotheses found, no theorem with the item's conclusion.
- rg of `topologicalKrullDim|def IsProjective|projective_of` in Mathlib/AlgebraicGeometry:
  Artinian dimension-zero facts only, no matching projectivity theorem.
- rg of `lem-sc-proper-dim-one-projective|isProjective_of_isProper` in the source
  WeilConjectures and repository lean/Sheaf: only a proof-docstring citation in
  Sheaf/AlgebraicGeometry/GenusInvariant.lean, no matching declaration.
- rg of the proposed declaration name and item id in dag/lean_names_upstream.json,
  source WeilConjectures, and repository lean/Sheaf: only that same docstring citation;
  no declaration name collision.

Validation: scompile.py M1 lem-sc-proper-dim-one-projective on the module returned
exit code 0, compiled in 1.6 seconds, with no warnings or errors.
No STATEMENT-DISPUTED issue or node fault found. Independent second reading remains
for the second worker; no second-reading section is claimed here.


## Second reading by M1

Independent verdict: the Lean says exactly what the node says. No mismatch found;
no Lean or node repair needed. Only this second-reading section was added.

Source read first: [Stacks Tag 0A26](https://stacks.math.columbia.edu/tag/0A26) and
[the actual varieties.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex),
chapter Notation and section Curves through lemma-dim-1-proper-projective.
The local Stacks checkout is absent. In the online TeX, the lemma is at lines
8472–8484, rather than the older line numbers in the node. The chapter convention
only fixes k as a ground field. Although the section defines curves as varieties,
this lemma explicitly concerns arbitrary proper schemes; it does not assume
integrality, smoothness, nonemptiness, or an algebraically closed ground field.
Its H-projectivity conclusion is precisely the embedding asserted by the node.

Object/hypothesis/conclusion checklist, in the node's order:

- Field k: `{k : Type u} [Field k]`. PASS: arbitrary field, no characteristic,
  perfection, infinitude, or algebraic-closure assumption.
- Scheme X over k: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. PASS: f is the
  specified structure morphism, not a canonical morphism chosen independently.
- Proper over k: `[IsProper f]`. PASS: opened the Mathlib class in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, extending `IsSeparated f`,
  `UniversallyClosed f`, and `LocallyOfFiniteType f`. Opened the
  `UniversallyClosed` quasi-compactness instance at line 167: this supplies the
  remaining finite-type requirement of def-weil-proper-morphism. No extra
  Noetherian, finiteness, or separation binder occurs.
- Topological Krull dimension at most one: `(hdim : X.dim ≤ 1)`. PASS:
  opened def-pc-dimension and its recorded module
  `Sheaf.AlgebraicGeometry.Dimension`. `Scheme.dim` is the supremum of
  `ringKrullDim (X.presheaf.stalk x)` over points x. Read the signature and
  docstring of `Scheme.dim_eq_topologicalKrullDim`: it equates this quantity
  with the node's topological dimension, also for empty X. The comparison's
  proof is postponed, as appropriate to stage 2; the dimension data is concrete.
- Empty dimension is minus infinity: the same `Scheme.dim` supremum is bottom
  for empty X in `WithBot ℕ∞`. PASS: no Nonempty instance is required.
- Exists integer N ≥ 0 and a closed immersion over k into classical P^N_k:
  `IsProjective f`, through its `IsHProjective` parent, has the field
  `exists_closedImmersion : ∃ (n : ℕ) (i : X ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)),
  IsClosedImmersion i ∧ i ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = f`.
  PASS: instantiate S with Spec k. Natural n is exactly a nonnegative integer;
  the n+1 coordinates give projective dimension n, and the equation is the
  over-k condition. The existential is after all hypotheses. Opened
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: this is base change of
  the projective integral model, and its structure map is the pullback fst.
- Equivalently projective over k in def-pc-projective-morphism's convention:
  the conclusion `IsProjective f` uses precisely the recorded declaration in
  `Sheaf.AlgebraicGeometry.Morphisms.Projective`. PASS: opened both class
  signatures and docstrings. The additional parent `QuasiCompact f` is already
  entailed by properness, so the conclusion has the same strength as the
  asserted closed embedding under the given hypotheses.

Edge cases: empty X is included and can embed as the empty closed subscheme;
dimension zero and one both satisfy the inequality, including disconnected,
reducible, singular and nonreduced proper schemes. N = 0 is permitted. Finite,
imperfect, and positive-characteristic fields are included. There is no index
family or zero object in this statement. The arbitrary universe u and the common
scheme/field universe follow the dependency signatures; any two object sizes can
be accommodated in a common universe. `ULift` lifts the finite coordinate type
without changing its cardinality. No universe is fixed to zero; all variables and
universes are explicitly bound.

Independent searches (2026-10-11), using alternative words:

- msearch LeanFinder: “A complete algebraic curve, possibly reducible or
  nonreduced, admits a closed embedding in projective space”. Eight hits,
  including Proj properness, Proj itself and closed-immersion facts; no theorem
  giving a projective embedding for the node's general proper schemes.
- msearch Loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsProper`.
  Two hits, `IsClosedImmersion.iff_isProper_and_mono` and
  `IsClosedImmersion.eq_proper_inf_monomorphisms`; neither constructs an
  embedding into projective space. An earlier two-string query was rejected
  by the service parser and is not counted as a negative search result.
- msearch LeanSearch: “A complete curve over an arbitrary field embeds into
  projective space”. Service unavailable (Internal Server Error); no verdict
  inferred from that failure.
- rg case-insensitive conceptual searches for projectivity with properness,
  dimension or curves and closed embeddings into projective space in Mathlib
  AlgebraicGeometry, source WeilConjectures/AlgebraicGeometry, and project
  lean/Sheaf/AlgebraicGeometry. Opened the nearby source candidates:
  `IsCurve.exists_projectiveClosure` assumes `IsIntegral U` and gives an open
  immersion into a closure; `exists_smooth_projectiveCompactification` assumes
  a perfect field, geometric connectedness, normal local rings and dimension
  exactly one; `IsCurve.isQuasiProjective` assumes smoothness and only gives
  quasi-projectivity. None is the node's statement. The newly landed project
  `exists_closed_open_immersion_projectiveSpace_of_dim_le_one` was also opened;
  it only gives an immersion, not the required closed immersion. No duplicate.
- rg of the proposed declaration in dag/lean_names_upstream.json returned no
  collision. Existing projective-space and dimension notions were reused.

H5/H6/H8/H9: one named theorem with only `sorry`; no definition data or extra
proved theorem. Module and declaration docstrings identify Tag 0A26 and the item.
Both proof steps and every proof dependency of the node are in the theorem
 docstring: quasi-projectivity, separated ambient space, properness of the
immersion, closed image, closed-immersion criterion, and projectivity. Imports
supply properness, dimension and projectivity. Lines are within 100 characters.
The node's lean.statement was compared mechanically with the signature and is
verbatim equal. No new nodes, dependency modules, or statement corrections are
present, so H12/H13 and corrected-citer checks introduce no further obligations.

Validation by the second reader: scompile.py returned exit code 0, compiled
in 1.6 seconds with no errors or warnings. deliver2.py --no-push printed OK:
the delivery passes preflight and compiles.
