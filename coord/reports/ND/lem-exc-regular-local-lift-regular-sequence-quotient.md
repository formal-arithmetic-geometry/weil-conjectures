## Worker report

The module `Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient` states
`RingTheory.isRegularLocalRing_of_regularSequence_quotient`, with its sole proof
left as `sorry`. It introduces no definitions. The node copy changes only `lean`.
The statement and five-step proof were checked against the node and
[Stacks Tag 00NU](https://stacks.math.columbia.edu/tag/00NU), second assertion.
The local Stacks source archive is absent, so the public source was opened.

Each hypothesis and clause is rendered as follows:

| Node text | Lean |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| Noetherian | `[IsNoetherianRing R]`, meaning every ideal is finitely generated |
| Local with unique maximal ideal m | `[IsLocalRing R]`; `maximalIdeal R` is its unique maximal ideal |
| A finite sequence of length r, with r ≥ 0 | `(xs : List R)`; its length is the natural number `xs.length` |
| Every sequence element lies in m | `(hmem : ∀ x ∈ xs, x ∈ maximalIdeal R)` |
| A regular sequence in R | `(hseq : RingTheory.Sequence.IsRegular R xs)` |
| R/(x₁,…,xᵣ) is regular local | `[IsRegularLocalRing (R ⧸ Ideal.ofList xs)]` |
| R is regular local | `IsRegularLocalRing R` |

The list encoding retains order, repetitions, and every finite length, including
zero. A typeclass binder for quotient regularity is the same mathematical premise
as an explicit proof argument. All universes and variables are explicitly bound.
`IsLocalRing` includes nontriviality, as required by existence of a unique maximal
ideal. `IsRegularLocalRing` includes the Noetherian and local clauses and equates
the maximal ideal's minimum generator count with Krull dimension.

Dependency declarations were read in full with their docstrings:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, from
  `def-weil-pbc-noetherian-ring`; also read `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.RingTheory.Regular.RegularSequence`:
  `RingTheory.Sequence.IsRegular`, from `def-weil-pbc-regular-sequence`;
  also read `IsWeaklyRegular` and its indexed quotient criterion. With the module
  equal to R, this is precisely the regular-sequence predicate in the node.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, recorded in
  `def-weil-regular-scheme`'s `lean.declarations` and `mathlib_match`;
  also read `of_spanFinrank_maximalIdeal_le`. Only the ring clause is used here.

The stated proof inputs are imported without `public`:
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem` (the finite local dimension instance,
`lem-weil-pbc-noetherian-local-finite-krull-dimension`) and
`Mathlib.RingTheory.KrullDimension.Regular`
(`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`,
`lem-weil-pbc-dimension-quotient-nonzerodivisor`). Their source signatures were
read. The declaration docstring carries all five proof steps and their node inputs.

Edge cases checked mathematically before writing:

- `xs = []`: `Ideal.ofList [] = ⊥`; regularity is transported across
  `R/(0) ≃ R`. No positive-length premise or extra hypothesis excludes this case.
- Quotient dimension zero: its maximal ideal uses the empty generating list;
  adjoining the last regular element gives the preceding one-dimensional case.
- A field R: its maximal ideal is zero, so only the empty sequence is regular
  in the maximal ideal; a nonempty list of zeroes cannot act injectively on R.
- The zero ring is excluded by the node's unique-maximal-ideal assumption and
  by `IsLocalRing`, rather than by any added nontriviality assumption.
- Repeated elements are permitted as input lists, with regularity testing them
  on the successive quotients. No distinctness or domain assumption was added.

Searches for an exact existing statement (all on 2026-10-16):

- `msearch.py leanfinder`, query
  `regular local ring quotient by regular sequence ambient regular local ring`:
  eight hits, including regular-sequence localization, the successive-quotient
  criterion and the local weak-regularity criterion; none concludes regularity
  of the ambient local ring.
- `msearch.py loogle`, query `IsRegularLocalRing quotient regular sequence`:
  zero hits, with unknown identifier `quotient`; this query is inconclusive.
- `msearch.py leansearch`, query
  `A Noetherian local ring with regular local quotient by a regular sequence is regular local`:
  eight hits, including `RingTheory.Sequence.IsRegular`, quotient Noetherianity,
  and the dimension-drop and regular-sequence dimension formulas. None is the item.
- `msearch.py grep`, query `isRegularLocalRing.*quotient|regular.*quotient`,
  restricted to `RingTheory/RegularLocalRing`: zero hits.
- `rg` in the pinned Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for regular-local quotient and regular-sequence terminology: upstream
  `IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient` assumes R
  is already regular and cannot supply this implication; the upstream singleton
  quotient result has the opposite direction. Read their complete signatures.
  Project `RootAlgebraRegularAtRoot` has a private singleton lifting proof only,
  neither a public declaration nor the general regular-sequence statement.
- `grep -rn` for the exact node ID in upstream: no hits. `rg` for the chosen
  declaration name in Mathlib, upstream, project sources and
  `dag/lean_names_upstream.json`: no hits.

No statement correction, missing notion, dependency-interface repair, or
STATEMENT-DISPUTED issue was found. The initial statement compiled cleanly with
`scompile.py`; the final file is checked again by the required delivery dry run.
The independent second reading is left to the dispatched second reader.


## Second reading by ND

Independent second reader, 2026-10-16. I opened the shared node, sandbox node,
module, all three statement-dependency records, their actual Mathlib definitions,
and both proof-input signatures. The statement is exact; no Lean or node repair
was needed. This reading adds only this review report.

The local `literature/stacks-project/algebra.tex` archive is absent. I independently
read the [upstream algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex),
`lemma-regular-mod-x` (lines 23568–23582), its surrounding regular-local-ring
section, the chapter conventions, and the regular-sequence definition. I also
checked [Stacks Tag 00NU](https://stacks.math.columbia.edu/tag/00NU).
The chapter assumes commutative unital rings and defines local as having exactly
one maximal ideal. The lemma assumes a Noetherian local ring throughout; its
second assertion lifts regularity from a regular-sequence quotient. There is no
field, characteristic, excellence, domain, or finite-type hypothesis to inherit.
The node's explicit maximal-ideal membership is consistent with the source:
a nonzero final quotient makes the generated ideal proper in this local ring.

My object/hypothesis/conclusion checklist, made from the node before comparing:

| Node item | Actual Lean rendering | Verdict |
| --- | --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]` | Exact, unital, arbitrary universe u. |
| R is Noetherian | `[IsNoetherianRing R]` | Exact: all ideals finitely generated. |
| R has a unique maximal ideal m | `[IsLocalRing R]`, `maximalIdeal R` | Exact: the class includes nontriviality, and `maximal_ideal_unique` identifies this ideal. |
| A finite ordered sequence x₁,…,xᵣ, r ≥ 0 | `(xs : List R)` | Exact: r is its natural length; all finite tuples, including the empty tuple, are represented. |
| Every xᵢ lies in m | `(hmem : ∀ x ∈ xs, x ∈ maximalIdeal R)` | Exact; list membership tests every entry without imposing distinctness. |
| The sequence is regular on R | `(hseq : RingTheory.Sequence.IsRegular R xs)` | Exact specialization to the self-module R. |
| The quotient is by the ideal of the full sequence | `R ⧸ Ideal.ofList xs` | Exact: `ofList` is `Ideal.span {r | r ∈ xs}`. |
| That quotient is regular local | `[IsRegularLocalRing (R ⧸ Ideal.ofList xs)]` | Exact premise, expressed as a Prop-valued typeclass. |
| R is regular local | conclusion `IsRegularLocalRing R` | Exact, with no additional conclusion or existential choice. |

Dependency-interface audit: `def-weil-pbc-noetherian-ring` records
`IsNoetherianRing` in `Mathlib.RingTheory.Noetherian.Defs`; I read its abbreviation and
`isNoetherianRing_iff_ideal_fg`. The regular-sequence dependency records
`RingTheory.Sequence.IsRegular` in
`Mathlib.RingTheory.Regular.RegularSequence`; I read both structure fields:
`regular_mod_prev` requires injective scalar multiplication on each prefix
quotient and `top_ne_smul` requires the final quotient to be nonzero. On the
self-module these are exactly the node's ring conditions, with no extra instance.
`def-weil-regular-scheme` explicitly records `IsRegularLocalRing` among its
ring declarations in `Mathlib.RingTheory.RegularLocalRing.Defs`; I read that
class and `of_spanFinrank_maximalIdeal_le`. Its equality between minimal generator
count and Krull dimension is equivalent to the node's generator criterion.
No scheme clause is used. All three recorded modules are public imports.
The finite-dimension instance and the dimension-drop theorem in the two ordinary
proof imports have precisely the Noetherian/local and regular-element hypotheses
used in proof steps 3–4. No dependency module or new definition node is needed.

Edge cases: the empty list gives the zero ideal and quotient canonically
isomorphic to R; its regular-sequence nonzero condition is already provided by
locality. There is no positive-length binder. A zero-dimensional final quotient
is permitted, with an empty generating family in the proof. A field is permitted
in every characteristic and permits only the empty regular sequence inside its
zero maximal ideal. The zero ring is excluded by the node's unique-maximal-ideal
condition, exactly as by `IsLocalRing`; it has no maximal ideal. Repetitions and
zero entries are not syntactically excluded; regularity decides whether they
satisfy the hypotheses. There is no index-universe restriction: lists of R and
its ideal quotient lie in R's arbitrary universe. Empty schemes and coefficient
universes are inapplicable to this ring statement.

Independent searches used different terminology from the first reader:

- `msearch.py leanfinder`: “A regular local quotient by a complete intersection
  ideal implies the ambient Noetherian local ring is regular”: eight results,
  concerning regular sequences, smoothness, localization, or DVR criteria;
  none is this implication.
- `msearch.py loogle`: `IsRegularLocalRing (_ ⧸ _) → IsRegularLocalRing _`:
  successful search with zero hits.
- `msearch.py leansearch`: “In a Noetherian local ring, lifting a minimal
  generating set of the maximal ideal from a regular quotient by a nonzero
  divisor proves regularity”: eight results, including dimension-drop formulas,
  regular-sequence induction and Nakayama; none concludes ambient regularity.
- `msearch.py grep`: `IsRegularLocalRing.*(of|quotient)|00NU`, restricted to
  `RingTheory/RegularLocalRing`: nine hits, regular-local criteria and polynomial
  localization results, not this statement.
- Independent `rg` searches of the pinned Mathlib, upstream `WeilConjectures`,
  and shared `lean/Sheaf` for `00NU`, `isRegularLocalRing_of`, regularity-lifting
  terminology, and quotient names. I opened the upstream
  `IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient` signature:
  it already assumes `[IsRegularLocalRing R]` and only supplies ideal generators.
  I also opened `AdjoinRoot`'s private `lift_regular` in
  `RootAlgebraRegularAtRoot` and the private singleton proof in
  `RegularIntegralDivisorBoundary`. Neither is a public general sequence
  statement, so neither can replace this module with an exact existing record.
  The chosen full declaration name has no existing collision.

H5/H6/H8/H9: the sole declaration is a theorem with exactly `by sorry`, so there
is neither proved material nor a hollow definition. Its docstring includes the
source, blueprint ID, and all five node proof steps: successive local
Noetherian quotients, regular next element and quotient identification,
dimension drop, lifting generators, and descending induction including length
zero. Module documentation, namespace, bound universe/variables, and line
widths are correct. I checked mechanically that `lean.statement` is verbatim
the theorem signature and that only the node's `lean` field differs from the
shared base. No statement correction or citer audit is required. Mismatches
found: none; changes: this independent report only.
