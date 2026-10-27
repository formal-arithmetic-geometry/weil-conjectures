## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeSizeOpenCoverBound` states
`AlgebraicGeometry.Scheme.cardinalSize_le_openCover`. Its only proof is `sorry`.
No definition, helper theorem, new node, or dependency repair is introduced.
The item's TeX statement, accepted split, and proof dependencies are unchanged.
Its statement dependencies gain the already landed `def-sfb-scheme-cardinal-size`.

The previous BLOCKED ending concerned Q120's reviewed stage-1 split, not a Lean
statement. On resumption this node is `split` with no `lean` or `reviewed_lean`,
and coord/queue.tsv lists it at stage 2. There is no item repair note. The
2026-10-22 stage handoff in coord/brief-stage2.md §0 explicitly permits this work.
The accepted Q120 proof is preserved, including its reuse of
`lem-sfb-open-cover-scheme-size`.

Correspondence of every hypothesis and clause:

- A scheme X is `(X : Scheme.{u})`, using Mathlib's recorded Scheme structure.
- An arbitrary set I indexing opens is `{I : Type v} (U : I → X.Opens)`.
  Universe v is independent of u; there is no finiteness or nonemptiness binder.
- The open-cover equality is `(hU : (⨆ i : I, U i) = ⊤)`, precisely union = X.
- Each member carries its induced open scheme structure `(U i).toScheme`,
  Mathlib's restriction of X to that open subset, rather than a separately chosen
  scheme or an arbitrary map.
- The size s(Z) is the existing `Z.cardinalSize`: its full definition is
  `max Cardinal.aleph0 (max (Cardinal.mk Z.affineOpens)
  (⨆ V : Z.affineOpens, Cardinal.mk ↥Γ(Z, V.1)))`.
  Mathlib defines `Z.affineOpens` as `{V : Z.Opens | IsAffineOpen V}`;
  thus these are affine open subsets, not presentations with multiplicities.
  `Γ(Z, V.1)` is the structure-sheaf section ring on the corresponding open.
- The conclusion is `Cardinal.lift.{v} X.cardinalSize ≤
  max Cardinal.aleph0 (max (Cardinal.lift.{u} (Cardinal.mk I))
  (⨆ i : I, Cardinal.lift.{v} (U i).toScheme.cardinalSize))`.
  These are exactly s(X), aleph_0, |I|, and sup_i s(U_i). Lifts place
  cardinals in `Cardinal.{max u v}` without changing them mathematically.
  The indexed family is small in this common universe, so its conditional
  supremum is a genuine supremum (`Cardinal.bddAbove_range`).
- For an empty I the cover equation forces X empty, the index cardinal and
  indexed supremum are zero, and both sides of the inequality are aleph_0.
  The definition of size of the empty scheme is aleph_0: its affine opens and
  section rings contribute only finite cardinalities. The explicit aleph_0
  term is already in the node and is retained.
- No quasi-compactness or quasi-separatedness assumption on X or any U_i
  appears. No characteristic, ring, separation, or nonzero condition is added.

Declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its local_affine
  field and full signature/docstring, `Scheme.Hom`, and `Scheme.Opens` (the recorded
  declaration for def-pc-scheme).
- `Sheaf.AlgebraicGeometry.SchemeCardinalSize`:
  `AlgebraicGeometry.Scheme.cardinalSize` (full definition and source docstring
  read; recorded by the landed def-sfb-scheme-cardinal-size node).
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, defined by
  `X.restrict U.isOpenEmbedding`, with its docstring.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.affineOpens` and `IsAffineOpen`.
- Cardinal.mk, Cardinal.lift, Cardinal.aleph0 and indexed suprema from Mathlib's
  cardinal API, publicly available through SchemeCardinalSize.

The sole proof dependency lem-sfb-open-cover-scheme-size has no Lean record or
Mathlib match in the read repository. Therefore it has no recorded module to
import yet; the docstring preserves the accepted proof plan, applying its
identical bound with Y = X and Y_i = (U i).toScheme. No second definition of size
is made. Read the cited Stacks source locally: sets.tex lines 311–326 (size) and
524–561 (Tag 000Q and proof). The existing explicit aleph_0 correction addresses
exactly the empty cover; no further statement correction is needed.

Edge cases checked mathematically before writing: empty I and X; a nonempty
family of empty opens; a singleton cover U = X; repeated opens; arbitrary
uncountable index sets; an uncountable disjoint union of points (the |I| term
cannot be dropped); non-quasi-compact and non-quasi-separated schemes. No
STATEMENT-DISPUTED fault was found.

Searches, all using the prescribed batch2/msearch.py wrapper where applicable:

- LeanFinder: “The cardinal size of a scheme is bounded by the cardinality of an
  arbitrary open covering and the sizes of its members” — 8 hits, including
  Scheme.OpenCover, OpenCover.iSup_opensRange and openCoverOfIsOpenCover;
  cover APIs only, no size estimate.
- Loogle: `"Scheme", "Cardinal"` — 0 hits.
- Mathlib grep, subdirectory AlgebraicGeometry:
  `(cardinalSize|cardinal|mk_le).*(openCover|affineOpens)|(openCover|affineOpens).*(cardinalSize|cardinal|mk_le)`
  — 0 hits.
- LeanSearch: “The number of affine opens and cardinalities of their section
  rings of a scheme are bounded by the cardinality of an open cover and the
  sizes of its members” — 8 hits, affineOpens and affine/open-cover definitions,
  compact-cover and induction APIs; no cardinal estimate. The SizeOf hit concerns
  syntactic data size, not the mathematical cardinal size.
- `rg` of lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  cardinalSize, cardinalSize_le_openCover and the item id — the existing
  SchemeCardinalSize definition and its locally-finite-type bound consumer;
  no open-cover size theorem or conflicting proposed name.
- Read the exact-duplicate DAG statement lem-sfb-open-cover-scheme-size, and the
  already recorded def-sfb-scheme-cardinal-size; the former has no declaration,
  the latter is reused. No new notion node is needed.

Validation: scompile.py Q94 lem-sfb-scheme-size-open-cover-bound with the delivered
module passed in both sandbox and library contexts (8.8 s and 10.2 s), with no
errors or unexpected warnings. All universes and variables are explicitly bound
and autoImplicit is disabled.

## Second reading by Q94

A separate pass by the same dispatched worker reread the item, dependency records,
source definition and full delivered signature. No independent agent was started,
as the dispatch expressly prohibits that. Checked each binder: Scheme.{u}, Type v,
open subsets, and union = top are exactly the node's input. Checked each maximum
entry and the left side against the recorded size definition; all four cardinal
quantities have the intended meaning. The lifts preserve unrestricted index
universes and the induced open-scheme structures are canonical restrictions.
Empty covers remain admitted and the countable term is explicit. No extra
hypothesis, missing conclusion, private size definition, or non-sorry proof was
found. The signature copied into lean.statement is verbatim from `theorem` to
before `:=`; the only non-lean node edit is the authorized addition of the landed
size-definition node to stmt_deps. No mathematical correction was made.
