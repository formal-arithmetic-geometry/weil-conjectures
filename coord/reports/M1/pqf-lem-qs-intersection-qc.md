## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection` states
`AlgebraicGeometry.compactSpace_inter_of_quasiSeparated`. Its only proof is `sorry`.
No definitions, additional nodes, or dependency modules are needed; the item's node changes
only in `lean`.

Correspondence with every hypothesis and conclusion:

- “Let X be a scheme”: `(X : Scheme.{u})`, with the universe explicitly declared.
- “quasi-separated”: `[QuasiSeparated (terminal.from X)]`. This is the diagonal-based
  definition recorded by `def-weil-quasi-separated-morphism`, referenced through the
  conventions node. The terminal scheme is Spec Z. This does not use the automatically
  quasi-separated identity morphism. Mathlib's `quasiSeparatedSpace_iff_quasiSeparated`
  identifies precisely this hypothesis with topological quasi-separatedness.
- “U,V subset X open subschemes”: `(U V : X.Opens)` and their canonical restrictions
  `U.toScheme`, `V.toScheme`. Every open subscheme is represented this way.
- “U,V quasi-compact”: `[CompactSpace U.toScheme] [CompactSpace V.toScheme]`, exactly
  compactness of their underlying spaces without a Hausdorff condition.
- “U cap V”: `(U ⊓ V).toScheme`, the restriction to the intersection open.
- “is quasi-compact”: `CompactSpace (U ⊓ V).toScheme`.
- “is an open subscheme”: built into `U ⊓ V : X.Opens` and `Scheme.Opens.toScheme`;
  no extra proposition is required to assert the openness of an already bundled open.

Dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` is explicitly a collection of pointers, with
  `lean.convention = true` and null declaration/module. It calls for using the underlying
  Mathlib notions, rather than inventing a bundled conventions definition.
- Its relevant leaves are `def-pc-scheme`, with `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` in `Mathlib.AlgebraicGeometry.Scheme`, and
  `def-weil-quasi-separated-morphism`, with `AlgebraicGeometry.QuasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. Their source signatures and
  docstrings were read.
- `def-weil-pbc-quasi-compact-scheme` is a Mathlib leaf whose record is `CompactSpace`
  in `Mathlib.Topology.Defs.Filter`. Its definition and docstring were read; it requires
  `IsCompact Set.univ` and adds no separation hypothesis.
- `AlgebraicGeometry.Scheme.Opens` (Scheme.lean) and `Scheme.Opens.toScheme`
  (`Mathlib.AlgebraicGeometry.Restrict`, lines 44–48) give the canonical open subscheme.
  The sole import `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` supplies these
  notions and the terminal scheme construction transitively.

Edge cases checked before writing: empty X; U or V empty; disjoint opens (empty
intersection); U = V; U or V = top when X is quasi-compact. All are included and the
conclusion is correct. No compactness of X, affineness, Noetherian, separated, nonempty,
or base-field assumption is added. Universe u is unrestricted. Compactness of an open
subscheme and compactness of its subset of X agree by `isCompact_iff_compactSpace`;
there is no strengthening hidden in the subspace encoding.

Searches (2026-10-11):

- `msearch.py ... leansearch "The intersection of two quasi-compact open subschemes of a
  quasi-separated scheme is quasi-compact"`: service unavailable (Internal Server Error).
- `msearch.py ... leanfinder "In a quasi-separated scheme the intersection of two
  quasi-compact open subschemes is quasi-compact"`: eight results, including
  `quasiSeparatedSpace_iff_forall_affineOpens`, the affine case and the topological
  quasi-separatedness equivalence; no exact scheme theorem with the diagonal hypothesis.
- `msearch.py ... loogle "QuasiSeparatedSpace.inter_isCompact"`: the topological
  class projection, whose full signature was read. It uses a topological
  `QuasiSeparatedSpace` hypothesis, rather than the recorded diagonal-based scheme
  hypothesis, and is therefore a proof ingredient rather than the exact declaration.
- `msearch.py ... grep "inter_isCompact|isCompact_inter" Topology/QuasiSeparated.lean`:
  class projection and construction of quasi-separated spaces from a compact-open basis.
- `rg` of these names and intersection/compactness patterns in Mathlib's AlgebraicGeometry,
  the source `WeilConjectures`, and this project's `lean/Sheaf`: the quasi-separatedness
  equivalence and applications of the topological projection, no matching scheme theorem.
  `pqf-lem-qs-intersection-qc` occurs in a landed proof docstring, not as a declaration.
- `rg` of `compactSpace_inter_of_quasiSeparated|quasiCompact_open_inter` in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no naming collision.

Source check: the named blueprint markdown file is not present on this machine. The node
contains the statement and full two-step proof; these are reproduced in the theorem's
signature and docstring. The mathematical input was checked against Mathlib's
`quasiSeparatedSpace_iff_forall_affineOpens` and Stacks Project Lemma 26.21.6,
[Tag 01KO](https://stacks.math.columbia.edu/tag/01KO), which gives the affine intersection
criterion. This supplies the node's proof by finite affine decompositions.
No statement correction or disputed statement.

Validation: `scompile.py M1 pqf-lem-qs-intersection-qc` compiled the module on the server
in 1.6 seconds with exit code 0 and no warnings. Delivery dry run follows; the second
reader will provide the independent reading and push.


## Second reading by M1

I independently read the sandbox node and complete Lean module, the two statement
dependency nodes and the relevant leaves of the conventions node, and the actual
blueprint source on the server:
`literature/blueprint/master/blueprint/sec-nagata-compactification/`
`sk-prop-nagata-sketch-zmt/pqf-lem-qs-intersection-qc.md`.
The source was retrieved by read-only SSH because this machine lacks the literature copy.
Its statement agrees verbatim with the node; its proof uses finite affine decompositions
and the preimage of the affine rectangle under the quasi-compact diagonal.
I also read Stacks `schemes.tex` from the Stacks project's raw GitHub source, labels
`section-separation-axioms`, `definition-separated` (01KK, items 2 and 4), and
`lemma-characterize-quasi-separated` (01KO). These impose no ambient Noetherian,
separated, quasi-compact, base-field, or characteristic assumption. For the absolute
scheme notion the base is Spec Z, so the common-affine-base qualification in 01KO
holds for every pair of affine opens.

Object/hypothesis/conclusion checklist (H3):

1. Object X, an arbitrary scheme: `(X : Scheme.{u})`. PASS. I read `Scheme` and
   `Scheme.Hom` in Mathlib `AlgebraicGeometry/Scheme.lean`: a locally ringed space with
   local affine charts and its morphisms. This is `def-pc-scheme`, reached through the
   conventions node, with no additional structure assumed.
2. Hypothesis X quasi-separated: `[QuasiSeparated (terminal.from X)]`. PASS. I read
   `def-weil-quasi-separated-morphism` and Mathlib's class `QuasiSeparated`, whose sole
   field is `QuasiCompact (pullback.diagonal f)`. Mathlib `Limits.lean` identifies
   Spec Z (with ULift when needed) as terminal. The terminal map therefore expresses
   exactly the absolute definition in 01KK; it is not a tautological identity map.
   `quasiSeparatedSpace_iff_quasiSeparated` also confirms the topological equivalence.
3. Objects U and V, open subschemes of this same X: `(U V : X.Opens)`. PASS. I read
   `Scheme.Opens` and `Scheme.Opens.toScheme` in Mathlib `Scheme.lean` and
   `Restrict.lean`: the latter is the restriction of X to the open subspace.
   Its canonical inclusion is an open immersion. Every open subscheme is represented
   by this restriction, up to the canonical isomorphism.
4. Hypothesis U quasi-compact: `[CompactSpace U.toScheme]`. PASS. The dependency
   `def-weil-pbc-quasi-compact-scheme` records `CompactSpace`; I read its definition
   in `Topology/Defs/Filter.lean`, compactness of the whole underlying space without
   a separation condition. Subspace compactness agrees with subset compactness by
   `isCompact_iff_compactSpace`.
5. Hypothesis V quasi-compact: `[CompactSpace V.toScheme]`. PASS, for the same reason.
   There is no compactness assumption on X and no affine hypothesis on either open.
6. Conclusion's object U intersection V: `(U ⊓ V).toScheme`. PASS. Meet in the opens
   lattice is the set intersection with its open proof, and `toScheme` gives its
   induced scheme structure, rather than an unrelated scheme.
7. Conclusion quasi-compact: `CompactSpace (U ⊓ V).toScheme`. PASS; exactly the same
   quasi-compact scheme notion as in the two hypotheses.
8. Conclusion open subscheme: already carried by `U ⊓ V : X.Opens` and `toScheme`.
   PASS. There is no missing existential or structural requirement. Quantifiers
   introduce X first, then its opens U and V, then the two compactness assumptions.

Edge cases: X empty, either open empty, disjoint opens, U = V, and an open equal to
all of X are covered. In particular an empty intersection is a compact empty scheme;
no nonemptiness instance is requested. Empty finite affine covers are allowed in the
proof. The zero-ring affine scheme is included. There is no integer parameter or
characteristic restriction. The explicitly bound universe u is arbitrary; the opens
and their restrictions have the same universe as X, with no test-object quantifier
whose universe could make a hypothesis vacuous.

Independent H4 searches, using different queries from the first reader:

- `msearch.py M1 pqf-lem-qs-intersection-qc leansearch
  "Two compact opens in a scheme with quasi compact diagonal have compact intersection"`:
  service unavailable (Internal Server Error); no verdict attributed to that service.
- LeanFinder query `Compactness of the meet of two compact open subsets in a scheme
  whose diagonal is quasi compact`: eight hits. I inspected the affine criterion,
  the diagonal class field, and the topological/diagonal equivalence. Other hits concern
  equalizers or the diagonal itself, not this intersection statement.
- Loogle query `CompactSpace, AlgebraicGeometry.Scheme.Opens`: twelve hits concerning
  global sections, basic opens, quasi-affineness, and related scheme facts; no exact
  declaration of this statement.
- `rg` for `compactSpace.*inter|[Ii]nter.*[Cc]ompact|inter_isCompact|isCompact_inter`
  across Mathlib AlgebraicGeometry, the source `WeilConjectures`, and project
  `lean/Sheaf`: uses of the topological intersection projection, finite affine cover
  constructions, compactification intermediates, and spectral statements. None is the
  same scheme intersection declaration. In particular `compactSpace_intermediate`
  is about a compactification intermediate with a Noetherian base, not this notion.
- I opened Mathlib `Topology/QuasiSeparated.lean`, including
  `QuasiSeparatedSpace.inter_isCompact` and `IsCompact.inter_of_isOpen`.
  They conclude subset compactness under a topological quasi-separatedness instance;
  neither has the recorded diagonal-based scheme hypothesis and open-scheme conclusion.
  They are proof ingredients through the equivalence and subspace conversion, as the
  stage-1 reviewed node already records. No duplicate definition is introduced.

H8 proof reading: I opened the proof nodes
`lem-pqf-finite-affine-cover-qc-open` and
`lem-weil-pbc-quasi-separated-affine-cover-criterion`, and read their recorded Mathlib
signatures in `Morphisms/QuasiCompact.lean` and `Morphisms/QuasiSeparated.lean`.
The first gives the finite affine decomposition (including the empty case), and
clause (1) of the second gives compact affine intersections with precisely the
quasi-separated hypothesis in force. The theorem docstring records both steps and
finite-union compactness/openness. Module and theorem docstrings both name the source
and `(blueprint: pqf-lem-qs-intersection-qc)`.

No H3 mismatch found; no Lean or node change was needed. No new definition node,
dependency module, statement correction, private notion, hollow definition, local
notation, or proved theorem is present. The sole theorem proof remains `sorry`.
Every variable and universe is explicitly bound; the only import supplies the scheme,
open restriction, terminal map, and diagonal property used in the signature.
The node's `lean.statement` is verbatim the file's theorem signature. The existing
Worker report is retained; the second reading adds this independent evidence.

Second-reader validation: `scompile.py M1 pqf-lem-qs-intersection-qc` compiled the
43-line module on the server in 2.0 seconds, exit code 0, without warnings.
