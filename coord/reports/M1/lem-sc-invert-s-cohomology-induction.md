## Worker report

The module defines the statement `AlgebraicGeometry.quasiCompactOpen_induction` in
`lean/Sheaf/AlgebraicGeometry/QuasiCompactOpenInduction.lean`.  It uses Mathlib's
`Scheme`, `CompactSpace`, `QuasiSeparatedSpace`, `Scheme.Opens`, `IsCompact`, and
`IsAffineOpen` to render the node's objects and hypotheses.

The hypothesis that `X` is a quasi-compact scheme is rendered by `[CompactSpace X]`;
the hypothesis that `X` is quasi-separated is rendered by `[QuasiSeparatedSpace X]`.
`P : X.Opens → Prop` is the property of open subschemes of `X`.  The affine clause is
`h_affine : ∀ U, IsAffineOpen U → P U`.  The gluing clause is
`h_union : ∀ U V, IsCompact (U : Set X) → IsAffineOpen V → P U → P V →
P (U ⊓ V) → P (U ⊔ V)`, expressing that for quasi-compact `U` and affine `V`,
property on `U`, `V`, and `U ∩ V` implies property on `U ∪ V`.  The conclusion is
`∀ U, IsCompact (U : Set X) → P U`, i.e. every quasi-compact open; `P ⊤` is the
instance `U = ⊤`, representing the final “in particular X” clause (top is compact
under `[CompactSpace X]`).

The dependency notions are used from Mathlib: `AlgebraicGeometry.Scheme` (the
`def-pc-scheme` leaf), `CompactSpace` (the `def-weil-pbc-quasi-compact-scheme`
leaf), and `QuasiSeparatedSpace` together with `IsAffineOpen` (the scheme-convention
leaf).  No project dependency module is needed.

Edge cases checked: `U` and `V` may be bottom or top opens; the index-free property
binder includes the empty open; arbitrary universes are represented by explicit
`universe u`; no finite, nonempty, or separatedness assumption is added.  The top
open is covered by the conclusion because a compact scheme has compact underlying
space.

Searches for an existing declaration: `msearch.py ... leanfinder` with query
“induction principle quasi-compact open schemes property affine union intersection”
returned `AlgebraicGeometry.compact_open_induction_on`, whose type requires `P ⊥`
and only adjoining an affine open, so it is not the node's intersection-gluing
statement; other hits were unrelated.  `msearch.py ... loogle` with query
“QuasiCompact IsAffineOpen IsCompact opens induction” returned no hits (unknown
identifier `QuasiCompact`).  `msearch.py ... grep` with query
“quasiCompactOpen_induction|compact_open_induction_on” in Mathlib/AlgebraicGeometry
returned no corresponding project declaration.  `rg` searches of Mathlib,
`WeilConjectures`, and project `lean/Sheaf` found no declaration of this theorem.

No statement correction or `STATEMENT-DISPUTED` note is required.

## Earlier second reading (a previous round; superseded)

Pending independent second reading by the next worker; this worker has not supplied
or claimed an independent review.

The source was read at https://stacks.math.columbia.edu/tag/08DR because the local
`literature/stacks-project/coherent.tex` is absent. It agrees with the node.
`P` is syntactically allowed on all opens, but all applications in the hypotheses
and conclusion are to quasi-compact opens: affines are compact, intersections are
compact in a quasi-separated space, and finite unions are compact. Extending a
property from the compact-open subtype to all opens imposes no constraint on it.
Mathlib `quasiSeparatedSpace_iff_quasiSeparated` identifies the space class with
quasi-compactness of the structure morphism's diagonal. `IsAffineOpen` is defined
as `IsAffine` of the open subscheme. `compactSpace_iff_quasiCompact` identifies
`CompactSpace X` with quasi-compactness of its structure morphism.
The precise candidate `compact_open_induction_on` was opened and read at
Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:241, including its signature.
The signature and docstrings of Scheme, Scheme.Hom, CompactSpace, QuasiSeparated,
IsAffine, and IsAffineOpen were also opened. The convention dependency has no
module or declaration: it explicitly collects the existing Mathlib notions.
No name match occurred in dag/lean_names_upstream.json or in the upstream source
for the node ID or the chosen full declaration name.

## Second reading by M1

Independently read the item node and the full delivered module, then Stacks
`coherent.tex`, lines 545–587, obtained from
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex,
and the rendered tag https://stacks.math.columbia.edu/tag/08DR. The surrounding
section adds no standing hypothesis: the lemma explicitly assumes only qcqs.
The node reproduces this statement. No statement correction is present or needed.

Object/hypothesis/conclusion inventory and match:

- Scheme X: `(X : Scheme.{u})`. Read `Scheme` and `Scheme.Hom` in
  `Mathlib/AlgebraicGeometry/Scheme.lean:42,74`; a locally ringed space locally
  isomorphic to spectra of commutative rings, as `def-pc-scheme` requires. Exact.
- X quasi-compact: `[CompactSpace X]`. Read the class in
  `Mathlib/Topology/Defs/Filter.lean:283`: compactness of the whole underlying
  space, without Hausdorffness, exactly the match recorded by
  `def-weil-pbc-quasi-compact-scheme`. Exact.
- X quasi-separated: `[QuasiSeparatedSpace X]`. Read the class in
  `Mathlib/Topology/QuasiSeparated.lean:47`, `QuasiSeparated` in
  `Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:50`, and
  `quasiSeparatedSpace_iff_quasiSeparated` at line 133. The equivalence identifies
  compact intersections of compact opens with the quasi-compact diagonal of
  X → Spec Z. Read the convention node and its referenced
  `def-weil-quasi-separated-morphism`; this is exactly the scheme-level notion
  they specify, with no separatedness assumption. Exact.
- Property P of quasi-compact open subschemes: `(P : X.Opens → Prop)`.
  Read `Scheme.Opens` at Scheme.lean:71 and `IsAffineOpen` at
  AffineScheme.lean:251, which is `IsAffine U` for the canonical open subscheme.
  A predicate is permitted on all opens but its values on noncompact opens
  are never used: affine opens are compact, U is explicitly compact, the
  overlap is compact by quasi-separatedness, and the union is compact by
  finite-union compactness. An arbitrary predicate on the compact-open
  subtype extends to all opens, e.g. by returning False outside the subtype;
  conversely restriction recovers it. Thus this presentation imposes no extra
  hypothesis or extra conclusion on P. Exact.
- Every affine open has P: `h_affine : ∀ U : X.Opens, IsAffineOpen U → P U`.
  Read `IsAffine` at AffineScheme.lean:59 (canonical isomorphism to Spec Γ),
  so this means affine open subschemes, not basic opens of a fixed chart. Exact.
- For quasi-compact U and affine V, P(U), P(V), P(U ∩ V) imply P(U ∪ V):
  `h_union` binds U and V, then `IsCompact (U : Set X)`, `IsAffineOpen V`,
  `P U`, `P V`, `P (U ⊓ V)`, and concludes `P (U ⊔ V)` in that order.
  Infimum and supremum are intersection and union of opens. No compactness
  assumption on V beyond affineness, or extra overlap assumption, is added. Exact.
- P holds for every quasi-compact open: conclusion
  `∀ U : X.Opens, IsCompact (U : Set X) → P U`. Exact.
- In particular P(X): instantiate that same conclusion at `U = ⊤`; its carrier
  is `Set.univ`, compact by `CompactSpace.isCompact_univ`. An explicit redundant
  conjunct is unnecessary. Exact.

Edge cases: bottom and top opens are allowed, including the empty scheme.
The empty open is affine (Spec of the zero ring), so the affine assumption
provides the empty-cover base case; no nonempty-ring assumption is present.
The docstring explicitly includes this base case. There is no index-set binder
or cohomological-degree binder in this induction principle; an empty cover or
n = 0 in its finite-cover proof is covered by the empty-open case. Characteristic
is unrestricted, and there is no base field, Noetherian or finiteness instance.
Explicit `universe u` and `Scheme.{u}` work at arbitrary universe level; all
variables in the signature are bound.

Independent searches (2026-10-11), with different wording from the worker:

- LeanFinder via `msearch.py`: “A predicate on open subsets of a scheme follows
  from affine cases and gluing a compact open with an affine chart using their
  overlap”. Returned `compact_open_induction_on`, `of_affine_open_cover`,
  `reduce_to_affine_global`, and related cover lemmas. Opened the exact signature
  of `compact_open_induction_on` in Morphisms/QuasiCompact.lean:241: it requires
  P(bottom) and closure under adjoining an affine without any overlap hypothesis,
  and does not assume qcqs. It is a useful proof tool but not this statement.
  The other hits concern affine-only predicates or locality/isomorphism hypotheses.
- LeanSearch via `msearch.py`: “Induction on compact open subschemes using affine
  charts and union intersection gluing”. Service returned Internal Server Error;
  no mathematical verdict is inferred from its unavailability.
- Grep via `msearch.py`: `induction|IsAffineOpen.*Prop|P.*⊓` in Mathlib's
  AlgebraicGeometry directory. Hits included the finite-cover induction and
  unrelated intersections; no duplicate of this overlap-gluing principle.
- Direct `rg` for `compact_open_induction|quasiCompactOpen_induction|08DR|` plus
  induction/open word combinations in upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`. No declaration with this
  statement or chosen name; upstream hits are particular affine-cover arguments,
  not the general induction principle. Also read the upstream Properties module
  around its compact-open arguments: these are extension-of-opens lemmas.

There are no new definition nodes or dependency modules in this delivery.
The convention node deliberately collects existing definitions rather than
introducing a private notion; the delivered module uses those Mathlib definitions.
No hollow definition or extra proved theorem is present. The sole theorem has
`by sorry`; its source/blueprint docstring follows all three node proof steps,
including separatedness of the smaller opens, the compact separated overlap,
and the final specialization W = X. Imports are used and lines meet 100 columns.

No mathematical mismatch was found; the Lean module was preserved. The only
record adjustment stores `lean.statement` with the signature's exact whitespace
rather than its previous whitespace-normalized form, to satisfy the brief's
verbatim requirement. `## Worker report` remains intact.

Validation: `scompile.py M1 lem-sc-invert-s-cohomology-induction` compiled the
49-line module cleanly on the server in 1.6 seconds (exit 0, no warnings).
