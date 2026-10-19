## Worker report

The module Sheaf.AlgebraicGeometry.CurveProjectiveDenseCompletion states
AlgebraicGeometry.exists_projective_dense_completion_of_dim_le_one, with sorry proof only.
Source read: Stacks varieties.tex, lemma-dim-1-projective-completion (Tag 0BXV), including its
scheme-image proof and the generic-point dimension argument. No statement correction.

Hypothesis and clause correspondence:
- Field k: `{k : Type u} [Field k]`.
- Scheme X over k: `{X : Scheme.{u}} [X.Over (Spec (.of k))]`.
- Separated structure map: `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`, as fixed by the convention node.
- Dimension at most one: `hdim : topologicalKrullDim X ≤ 1`.
- Completion and its k-structure: existential `C : Scheme.{u}`, `g : C ⟶ Spec (.of k)`.
- Projective in the node H-projective convention: `IsHProjective g`.
- Dimension bound: `topologicalKrullDim C ≤ 1`.
- Open immersion over k: `a : X ⟶ C`, `IsOpenImmersion a`, and
  `a ≫ g = X ↘ Spec (.of k)`.
- Dense image: `DenseRange a`.
- Scheme-theoretically dense image: `∀ U : C.Opens, Function.Injective (a.app U)`.
  Scheme.Hom.app U is the structure sheaf map on U, from sections on U to sections on
  its inverse image. Injectivity on all opens is precisely injectivity of the sheaf map.
- Finite complement: `(Set.range a)ᶜ.Finite`.
- All boundary points closed: `∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C)`.
- Reduced choice when X reduced: `IsReduced X → IsReduced C` for the same completion.
  This simultaneous clause is valid because the sheaf injection into sections on reduced X
  forces reducedness, exactly as step 7 of the node explains.
- Empty choice when X empty: `IsEmpty X → IsEmpty C`. Density already forces this.

Dependency declarations read and used:
- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Scheme.Hom.app.
- def-weil-pbc-scheme-conventions has no declaration of its own; its finite-type and
  separated meanings are LocallyOfFiniteType, QuasiCompact, IsSeparated, from the
  corresponding Mathlib.AlgebraicGeometry.Morphisms modules.
- Mathlib.Topology.KrullDimension: topologicalKrullDim.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective: AlgebraicGeometry.IsHProjective
  (server #print confirmed the finite-coordinate closed-immersion field).
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsReduced.

Proof dependency imports cover Noetherian facts, immersions, scheme image, properness,
projective space, DimOneQuasiProjective and ClosedIrreducibleDimensionTrdeg. The docstring
carries all eight node proof steps with their dependency IDs. No proof is supplied.

Edge cases checked: empty X (dimension bottom, empty completion and boundary); dimension
zero; mixed zero/one dimensional components; nonreduced X (no reducedness hypothesis added);
arbitrary characteristic and arbitrary field; already projective X (empty boundary allowed).
All universes and variables are explicitly bound. No local notation or copied definitions.

Searches performed with msearch.py:
- leanfinder: "A separated finite type scheme of dimension at most one over a field admits
  a dense projective completion": eight hits on Proj properness and dominant maps; no match.
- loogle: "AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsOpenImmersion": no hits,
  IsHProjective unknown to the public Mathlib index.
- grep: "projective.*completion|dense.*completion|completion.*projective" in AlgebraicGeometry:
  zero hits.
- rg with the same expressions and the item ID in the upstream WeilConjectures and
  lean/Sheaf trees: only unrelated formal-completion projective embedding theorems.
  No existing declaration states the result.

## Dependency modules

`def-kun-projective`: no new module is needed. Its canonical projectivity repair has
already landed in the current base, pointing to the existing
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective.IsHProjective` declaration.
This delivery preserves that landed node exactly and makes no dependency-record edit.
The server #print shows its closed immersion into ℙ(n; S) for finite n. This is exactly
finite-dimensional projective-space embeddability: for nonempty n enumerate it by
Fin (N+1), and for empty n the empty projective space embeds into P^0. No added
hypotheses, new notion, or replacement scheme is involved.

Current validation (2026-10-15): the canonical `def-kun-projective` projectivity
repair is already landed in the refreshed base, so this delivery preserves that node
and its dependency links without editing or duplicating it. The required
`deliver2.py --no-push` dry run was rerun against that refreshed current base and
printed OK (commit 9483fae566 passed preflight and server compilation; nothing was
pushed). The current `scompile.py --source` interface returned the complete canonical
upstream Projective module, including `IsHProjective` and its finite-coordinate
embedding field. No alias, duplicate definition, or tool workaround is needed.
Fresh LeanFinder, Loogle, Mathlib grep and upstream/side rg searches confirmed the
no-match results recorded above. The Lean file, theorem statement, and dependency
links are unchanged; this repair updates only this report, and the resulting commit
should be re-pushed for normal independent review.

The following section preserves the earlier independent second reading verbatim; its
final validation failures describe the earlier tooling and are superseded by the
successful current dry run above. This worker does not claim another independent reading.

## Earlier second reading (a previous round; superseded)

Independent reader: read the sandbox item node and theorem, all seven statement dependency
nodes, their recorded declarations, the projectivity dependency repair, the two geometric
proof dependency modules, and Stacks varieties.tex, Notation and Tag 0BXV
(lemma-dim-1-projective-completion, lines 9231–9261). The chapter assumes only that k is
a field. No smoothness, irreducibility, reducedness, perfectness or characteristic assumption
is implicit here. No statement_change exists or is needed; no new definition nodes exist.

Object, hypothesis and conclusion inventory, with verdicts:

- Ground field k: `{k : Type u} [Field k]`. Mathlib Algebra/Field/Defs.lean:180 extends
  CommRing and DivisionRing. Exactly the node's arbitrary nontrivial field. PASS.
- Scheme X and its k-structure: `{X : Scheme.{u}} [X.Over (Spec (.of k))]`.
  Mathlib Scheme is a locally affine locally ringed space; its specified structure map
  is `X ↘ Spec (.of k)`. Exactly the dependency notions. PASS.
- Separated: `[IsSeparated (X ↘ Spec (.of k))]`; the class requires the diagonal to be
  a closed immersion (Morphisms/Separated.lean:44). No stronger property. PASS.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`. Read the affine finite-type section-map condition
  in Morphisms/FiniteType.lean:43 and compact-open preimage condition in
  Morphisms/QuasiCompact.lean:43. Their conjunction is exactly the scheme-conventions
  dependency's finite-type meaning, not finite presentation. PASS.
- Dimension hypothesis: `(hdim : topologicalKrullDim X ≤ 1)`. Read
  Topology/KrullDimension.lean:39: `krullDim (IrreducibleCloseds X)`, valued in
  `WithBot ℕ∞`; it counts chains of nonempty irreducible closed subsets. PASS.
- Completion with k-structure: `∃ (C : Scheme.{u}) (g : C ⟶ Spec (.of k))`.
  A specified structure map gives precisely a k-scheme. PASS.
- Projectivity: `IsHProjective g`, after removing the redundant `HProjective` alias.
  The live server #print gives the canonical class with field
  `exists_isClosedImmersion : ∃ n, ∃ (_ : Finite n), ∃ i,
  IsClosedImmersion i ∧ i ≫ (ProjectiveSpace n S ↘ S) = f`.
  This is finite-coordinate projective-space embeddability. Enumerating any nonempty
  finite n gives Fin (N+1); zero coordinates give the empty scheme, which also embeds
  in P^0. Conversely Fin (N+1) is finite. Thus it is precisely def-kun-projective's
  H-projective convention, with no extra quasi-compactness hypothesis. Semantic PASS;
  source-publication/checker limitation recorded below.
- Completion dimension: `topologicalKrullDim C ≤ 1`, using exactly the same notion. PASS.
- Open immersion: existential `(a : X ⟶ C)` and `IsOpenImmersion a`.
  Mathlib OpenImmersion.lean:38 uses the locally ringed space open-immersion predicate,
  giving both open embedding and isomorphism of the restricted structure sheaf. PASS.
- Morphism over k: `a ≫ g = X ↘ Spec (.of k)`. This expresses the k-linearity implicit
  in the source's immersion into a projective k-scheme. PASS.
- Topological density: `DenseRange a`, the underlying scheme map's dense image. PASS.
- Scheme-theoretic density: `∀ U : C.Opens, Function.Injective (a.app U)`.
  Read Scheme.lean:179: a.app U maps Γ(C,U) to Γ(X,a⁻¹U), precisely the components of
  O_C → a_*O_X. Componentwise injectivity is injectivity of this map of sheaves. PASS.
- Finite boundary: `(Set.range a)ᶜ.Finite`. No enumeration or nonemptiness required. PASS.
- Boundary points closed: `∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C)`.
  Together with the preceding clause this says exactly finite set of closed points. PASS.
- Reduced choice: `IsReduced X → IsReduced C`. Read Properties.lean:69: every ring
  of sections is reduced, the dependency node's equivalent criterion. The same C works:
  the injective restriction maps into section rings of reduced X kill all nilpotents.
  Hence the simultaneous implication does not strengthen the existence assertion. PASS.
- Empty choice: `IsEmpty X → IsEmpty C`. Density already forces it for the same C. PASS.
- Quantifiers: arbitrary input k and X, then one C, g and a satisfying all conclusions;
  each open and each boundary point is quantified inside that choice. PASS.

Edge cases: empty X has bottom dimension and forces empty C by density; the finite
boundary may be empty. Dimension zero and mixed zero/one-dimensional components are
included by ≤ 1. Nonreduced X is allowed; no regularity or smoothness instance is added.
Every characteristic and imperfect fields are covered. There is no index-set parameter
or natural-number parameter whose empty/zero case is omitted. All binders and universe u
are explicit. A common universe for k and X is the standard Scheme universe encoding;
any pair of sizes is covered after lifting to a common larger universe, with no additional
size bound or test-object quantification.

Independent searches (recorded with msearch.py, using different terms from the worker):
- leanfinder: "A separated algebraic curve over any field has a compactification with
  finite boundary in a projective scheme": eight hits, on Proj properness and related
  facts, none the requested statement.
- loogle: `"compactification"`: zero hits.
- grep in Mathlib/AlgebraicGeometry: `compactif|complet.*curve|curve.*complet`: zero hits.
- rg in upstream WeilConjectures and project lean/Sheaf: inspected curve compactification
  results, notably exists_smooth_properCompactification_of_perfectField, whose
  PerfectField, smooth relative curve and geometric connectedness hypotheses exclude
  this node's general schemes. No equivalent theorem was found. The requested theorem
  name and HProjective alias name have no existing declaration in either source tree.

Dependency repair and mismatches found:
- The delivery's HProjectiveAlias module merely renamed an existing usable canonical
  predicate to evade the dependency checker. Its own report explicitly identified this
  purpose. This is unnecessary under H4 and is a workaround forbidden by AGENTS.md §3.
  Removed that module, changed the theorem and its verbatim lean.statement to
  IsHProjective, and restored the def-kun-projective record to the existing canonical
  upstream declaration. The proposition is unchanged by this repair.
- The old side Projective.lean really defines another IsHProjective, rather than
  reexporting the canonical class; importing it alongside the proof dependencies is
  unusable. The dependency note now describes that actual mismatch.
- Canonical upstream source is absent from the pinned local source checkout and the
  group clone's upstream tree. Therefore full source-text review of that class is
  unavailable. The actual compiled declaration and field were inspected using only
  scompile.py; no replacement definition or object was invented.
- The initial probe used the old side class's field name exists_closedImmersion and
  correctly failed after printing the canonical class. Corrected the probe to the
  canonical exists_isClosedImmersion field and reran it.

The theorem docstring follows all eight proof steps and includes the exact source and
blueprint ID. No hollow definition, local notation, new proof, unbound variable or
statement correction was introduced. The only delivered theorem remains a named sorry.
The signature in the node is extracted verbatim from the file. All proof imports were
retained; existing proof modules were read and not changed.

Validation of the reviewed repair: scompile.py compiled CurveProjectiveDenseCompletion
cleanly in 1.6 s (also compiled the side-only imported ClosedIrreducibleDimensionTrdeg
in 1.5 s). The corrected canonical-class probe compiled in 1.4 s. All ran on the
server, nice 19, two threads, with 60 seconds per file. An explicit text check confirmed
that lean.statement equals the file signature and that lines are at most 100 characters.

Final second-reader dry run: deliver2.py --no-push failed with exactly two reasons:
(b) the dependency checker only permits existing dependency repairs through Sheaf modules,
rejecting the canonical existing WeilConjectures class; (d) the canonical Projective.lean
source is absent from the pinned source checkout. The second-reading requirement now
passes. Nothing was pushed. These require maintainer checker/source-publication alignment;
AGENTS.md §3 forbids editing or working around the tools, and the human isolation brief
forbids inventing a substitute dependency. The reviewed canonical statement and complete
report remain in the sandbox; no read-only source or validation tool was manually edited.


## Earlier second reading (a previous round; superseded)

Independent current reading, 2026-10-15: opened the item node and its Lean module,
all seven statement dependency nodes, their definition signatures, the repaired
projectivity node, and Stacks varieties.tex, Notation and
lemma-dim-1-projective-completion (Tag 0BXV). The chapter assumes only that k is
a field; the nearby definition of a variety does not impose integrality on this
lemma about schemes. Read the two imported geometric proof interfaces as well.
There are no new definition nodes, sibling dependency modules, or statement_change.

Inventory of the node, matched item by item with the Lean (all PASS):

- Object k, an arbitrary field: `{k : Type u} [Field k]`. Read Mathlib's Field
  class extending CommRing and DivisionRing; this is the node's nontrivial field.
- Object X, a k-scheme: `{X : Scheme.{u}} [X.Over (Spec (.of k))]`. Scheme is
  a locally affine locally ringed space; Over specifies the structure morphism
  `X ↘ Spec (.of k)`. No different base scheme or unspecified map is substituted.
- Hypothesis separated: `[IsSeparated (X ↘ Spec (.of k))]`. Its class says the
  diagonal is a closed immersion, exactly the scheme-conventions node.
- Hypothesis finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` together
  with `[QuasiCompact (X ↘ Spec (.of k))]`. Read the affine section ring-map
  finite-type condition and the compact-open-preimage condition. Their conjunction
  is precisely the convention node's finite type, without extra finite presentation.
- Hypothesis dimension at most one: `(hdim : topologicalKrullDim X ≤ 1)`.
  Mathlib defines this dimension as `krullDim (IrreducibleCloseds X)` in
  `WithBot ℕ∞`, matching chains of nonempty irreducible closed subsets.
- Output object C and its k-structure: `∃ (C : Scheme.{u})
  (g : C ⟶ Spec (.of k))`. An explicit g supplies the specified k-scheme.
- Conclusion projective over k: `IsHProjective g`. Independently retrieved the
  complete server source with `scompile.py --source
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective`. The class requires
  `∃ (n : Type u) (_ : Finite n) (i : C ⟶ ℙ(n; Spec (.of k))),
  IsClosedImmersion i ∧ i ≫ ℙ(n; Spec (.of k)) ↘ Spec (.of k) = g`.
  For nonempty finite coordinates this is a finite positive number N+1 after
  reindexing; for empty coordinates the projective scheme is empty and embeds
  into P^0. Conversely ULift (Fin (N+1)) is finite. Thus this is exactly
  def-kun-projective, including its N=0 and empty-source cases.
- Conclusion dimension of C at most one: `topologicalKrullDim C ≤ 1`, using
  the identical dimension notion and no purity or nonemptiness condition.
- Output open immersion: existential `(a : X ⟶ C)` and `IsOpenImmersion a`.
  Read Mathlib's locally ringed space open-immersion abbreviation: it identifies
  X with the open subscheme, including its structure sheaf.
- Conclusion over k: `a ≫ g = X ↘ Spec (.of k)`. This expresses the source's
  immersion and closure over the given ground field.
- Conclusion dense image: `DenseRange a`, for the underlying continuous map.
- Conclusion scheme-theoretically dense image:
  `∀ U : C.Opens, Function.Injective (a.app U)`. Read Scheme.Hom.app:
  its domain is Γ(C,U), its codomain Γ(X,a⁻¹U), and its value is the component
  of the structure sheaf morphism. Injectivity on all opens is exactly
  injectivity of O_C → a_*O_X, not only injectivity on global sections.
- Conclusion finite complement: `(Set.range a)ᶜ.Finite`.
- Conclusion boundary points closed:
  `∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C)`. Combined with the
  preceding clause, precisely a finite set of closed points, possibly empty.
- Conditional reduced choice: `IsReduced X → IsReduced C`. Read IsReduced's
  sectionwise reducedness definition and its equivalence with stalkwise
  reducedness. The same C works, since injection into each reduced section ring
  of X forces its section ring reduced. The simultaneous implication therefore
  does not strengthen the node's conditional existential choice.
- Conditional empty choice: `IsEmpty X → IsEmpty C`. Density forces this for
  the same C, so this also matches the node without strengthening it.
- Quantifiers: arbitrary input k and X with only the stated hypotheses, followed
  by a single C, g, a satisfying all clauses; all opens and boundary points are
  quantified within this choice. No added Noetherian, smoothness, regularity,
  perfectness, characteristic, connectedness, or irreducibility assumption.

Edge cases: empty X has bottom dimension and forces empty C; the boundary can
be empty. Dimension zero, mixed zero/one-dimensional components, and nonreduced
schemes are included. Arbitrary characteristics and imperfect fields are allowed.
There is no external index set or degree parameter. Universe u is explicitly
bound, and no test-scheme universe restriction or equality is introduced; the
standard common universe for a field and its schemes covers arbitrary sizes
on passing to a common ambient universe. No variable is left implicit.

Independent searches, with alternative wording:

- msearch LeanFinder: "A scheme of dimension zero or one has an open embedding
  into a projective scheme with finitely many missing closed points": eight
  results on Proj construction, open charts and properness; no equivalent theorem.
- msearch Loogle: `"compactification"`: zero hits.
- msearch grep: `compactif|complet.*curve|curve.*complet`: results are general
  topological compactifications, not this scheme theorem. Direct rg restricted
  to Mathlib/AlgebraicGeometry with that expression has no matches.
- Direct rg on the upstream and side AlgebraicGeometry trees finds curve
  compactification statements. Opened upstream
  exists_smooth_properCompactification_of_perfectField: it requires PerfectField,
  IsCurve, SmoothOfRelativeDimension 1, and GeometricallyConnected, so does not
  state this general dimension-at-most-one theorem. The requested declaration
  name does not already occur in either read-only source tree.

Dependency repair review: def-kun-projective's old side module defines a second
class with the same full name as the canonical upstream class. Opened that side
module and the actual upstream source retrieved from the server. The delivered
existing:true upstream record removes that conflict and retains exactly the
node's finite closed-embedding convention. No alias, private definition, arbitrary
map, choice object, or new theorem is introduced by this repair. The source access
problem described in the historical report is resolved by the supported --source
interface, and is not a current blocker.

No mathematical mismatch was found in the current delivery; the Lean and node
records are unchanged by this reading. Added this independent current review to
the report. The named theorem has only a sorry proof. Its source/blueprint
module and declaration docstrings carry all eight node proof steps, including
Noetherianity, scheme-theoretic closure, component generic points, dimension,
finite closed boundary, reducedness, and emptiness. No hollow definition or
file-local notation is present. Checked verbatim equality of lean.statement
with the file signature and the 100-column limit.

Validation: scompile.py compiled the delivered CurveProjectiveDenseCompletion module
in 1.7 s and its side-only ClosedIrreducibleDimensionTrdeg import in 1.5 s,
with no errors or warnings, on the server at nice 19, two threads, 60 seconds
per file. The independent current deliver2.py --no-push printed OK: commit
c61eb70db0 passes preflight and compiles. The final delivery reruns both checks.


## Second reading by NX

Independent second reader, 2026-10-15. Opened the current item node, Lean module,
all seven statement dependency nodes and their defining signatures, Stacks varieties.tex
Notation and Tag 0BXV (lemma-dim-1-projective-completion), and both imported geometric
proof modules. Read the canonical projectivity source through scompile.py --source
WeilConjectures.AlgebraicGeometry.Morphisms.Projective. The chapter assumes only a
field k; the definition of a variety does not impose integrality on this scheme lemma.
There is no statement_change, no new definition node and no delivered dependency module.

Object/hypothesis/conclusion inventory and Lean correspondence (each PASS):

- Ground field k: `{k : Type u} [Field k]`. Field extends CommRing and DivisionRing,
  including nontriviality. No characteristic or perfectness restriction.
- Scheme X over k: `{X : Scheme.{u}} [X.Over (Spec (.of k))]`. Scheme is a locally
  affine locally ringed space; Over carries the specified map `X ↘ Spec (.of k)`.
- Separated: `[IsSeparated (X ↘ Spec (.of k))]`, the closed-immersion diagonal condition.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`. The former is the affine section-map finite-type
  condition and the latter compact-open-preimage condition; together exactly the
  finite-type convention node. No finite-presentation or Noetherian assumption is added.
- Dimension at most one: `(hdim : topologicalKrullDim X ≤ 1)`. This is
  `krullDim (IrreducibleCloseds X) : WithBot ℕ∞`, counting strict chains of nonempty
  irreducible closed subsets, with bottom dimension for the empty scheme.
- Completion object and k-structure: `∃ (C : Scheme.{u}) (g : C ⟶ Spec (.of k))`.
- Projectivity: `IsHProjective g`. Its canonical class requires a closed immersion
  into projective space indexed by a finite coordinate type, over the specified base.
  Nonempty finite coordinates reindex to Fin (N+1); empty coordinates yield empty
  projective space and an empty source, also embeddable in P^0. This is exactly
  def-kun-projective's finite projective-space embedding convention.
- Completion dimension: `topologicalKrullDim C ≤ 1`, the same dimension predicate.
- Open immersion: existential `(a : X ⟶ C)` with `IsOpenImmersion a`, the locally
  ringed-space open-immersion predicate, including the restricted structure sheaf.
- Over k: `a ≫ g = X ↘ Spec (.of k)`, respecting the given k-structure.
- Dense image: `DenseRange a`, density of the underlying topological image.
- Scheme-theoretic density: `∀ U : C.Opens, Function.Injective (a.app U)`.
  Scheme.Hom.app U is Γ(C,U) → Γ(X,a⁻¹U); injectivity at every open is precisely
  injectivity of O_C → a_*O_X, not merely the global-section condition.
- Finite complement: `(Set.range a)ᶜ.Finite`.
- Closed boundary points: `∀ c : C, c ∉ Set.range a → IsClosed ({c} : Set C)`.
  These two clauses together give exactly a finite set of closed points.
- Reduced choice: `IsReduced X → IsReduced C`. IsReduced is sectionwise reducedness,
  equivalent to stalkwise reducedness. The same completion works because the preceding
  sheaf injection kills every nilpotent section; this simultaneous clause does not
  strengthen the node's conditional existence assertion.
- Empty choice: `IsEmpty X → IsEmpty C`. Density forces this for the same completion.
- Quantifier order: arbitrary k and X with these hypotheses, then a single C, g and a
  satisfying all conclusions, with the opens and boundary points quantified inside.

Edge cases: empty X is allowed and forces empty C, bottom dimension and empty boundary.
Dimension zero and mixed zero/one-dimensional components are allowed. Nonreduced schemes,
imperfect fields and every characteristic are included. Already projective schemes can
have empty boundary. Projective embedding dimension N=0 and empty coordinates are covered.
There is no external degree or index-set binder. Universe u and all variables are explicit;
the standard common ambient universe of k and Scheme introduces no test-object restriction
or additional universe equality. No regularity, smoothness, connectedness or irreducibility
hypothesis occurs.

Independent searches, with different wording from the first worker:

- msearch LeanFinder: "Separated finite type schemes with Krull dimension at most one
  admit projective compactifications with closed finite boundary": eight hits on Proj
  properness, finite type, separatedness and compactness; no equivalent statement.
- msearch Loogle: `"dense", "IsOpenImmersion"`: zero hits.
- msearch grep: `compactification|compactify|projective_dense`: 25 hits, all general
  topological compactification material, not this algebraic scheme theorem.
- Direct rg with those terms on upstream WeilConjectures, project lean/Sheaf and
  Mathlib/AlgebraicGeometry: inspected Curve/Compactification.lean, notably
  exists_smooth_properCompactification_of_perfectField. It requires PerfectField,
  IsCurve, SmoothOfRelativeDimension 1 and GeometricallyConnected, so is not this
  general theorem. Other matches concern Nagata compactification, specialized smooth
  curves or formal algebraization; no exact match and no duplicate declaration found.

Mismatch repaired: the sandbox retained a stale def-kun-projective node copy whose lean
record differed from the already landed canonical record, contrary to the current worker
report. Removed this unnecessary dependency copy from the delivery. The canonical existing
class is used directly by the theorem; no alias or replacement definition is needed.
The theorem module, item statement, dependency links and verbatim lean.statement are
unchanged. Earlier historical reviews remain above for provenance; this is the current
independent reading, and no dependency repair is being re-delivered.

Docstrings name the source and blueprint and reproduce all eight proof steps: Noetherian
quasi-compactness, immersion and scheme image, finite type of C, generic points, dimension
comparison, finite closed boundary, reducedness and emptiness. No hollow definition,
private notion, local notation or proved theorem is introduced. The sole theorem has a
sorry proof. Checked exact equality of lean.statement with the file signature and the
100-column limit (maximum 92). Read DimOneQuasiProjective and
ClosedIrreducibleDimensionTrdeg: they supply the stated geometric proof interfaces and
are existing imports, not modules delivered here.

Validation: scompile.py compiled CurveProjectiveDenseCompletion in 1.6 s, and its
side-only ClosedIrreducibleDimensionTrdeg import in 1.4 s, on the server at nice 19,
two threads and a 60-second per-file limit. No errors or warnings. The initial compile
invocation used a path relative to the read-only repository, where this new module is
absent; rerunning with its absolute sandbox path resolved the invocation error.
The mandatory dry run and final delivery follow this report.
