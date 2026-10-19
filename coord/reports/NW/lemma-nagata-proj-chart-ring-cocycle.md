## Worker report

Recorded an existing published declaration family; no Lean module is added and no
proof or definition is rewritten. The main declaration is
`HomogeneousLocalization.Away.overlapEquiv_cocycle` in
`WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
The record also lists `Away.overlapEquiv`, `Away.overlapEquiv_awayMap_left`,
`Away.overlapEquiv_awayMap_right`, `Away.overlapEquiv_self`, and
`Away.overlapEquiv_symm`, all in the namespace `HomogeneousLocalization`.

The older local upstream source ends before the chart-coherence section. I read
the full published section, including signatures and docstrings, using
`scompile.py --source WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
The server source contains the family identified by the node's existing audit.

Clause-by-clause correspondence:

- A commutative graded ring is `[CommRing A]`, `𝒜 : ι → σ`,
  `[SetLike σ A]`, `[AddSubgroupClass σ A]`, `[GradedRing 𝒜]`.
  Specialize `ι` to `ℕ`; its additive-monoid and decidable-equality instances
  are available. No ring universe is restricted.
- Positive-degree homogeneous elements are `hf : f ∈ 𝒜 d`,
  `hg : g ∈ 𝒜 e`, `hh : h ∈ 𝒜 e'`, specialized to positive natural
  degrees. The published coherence identities are more general and hold for
  all these degrees, so this includes every instance in the node.
- The chart ring `(R_(f))_0` is exactly `HomogeneousLocalization.Away 𝒜 f`,
  the declaration recorded by `def-nagata-homogeneous-localization-degree-zero`
  in `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`. I read its
  definition and `Away.mk` and `Away.mk_surjective`: these are fractions
  `a/f^n` with numerator degree `n • d`, modulo ordinary localization.
- The restriction of the f-chart to the overlap is represented by
  `Away 𝒜 (f*g)`. This is genuinely the restriction, not an unrestricted
  map from the f-chart to the g-chart: Mathlib's
  `HomogeneousLocalization.Away.isLocalization_mul hf hg rfl hd`,
  with `hd : d ≠ 0`, identifies it as localization of `Away 𝒜 f`
  at `Away.isLocalizationElem hf hg = g^d/f^e`, under the algebra
  structure induced by `awayMap 𝒜 hg rfl`. I read this full signature,
  its docstring, the definition of the localizing element, and `awayMap_mk`.
  Swapping f,g gives `Away 𝒜 (g*f)` as the g-chart restriction.
- The canonical equivalence between these restriction models is
  `Away.overlapEquiv 𝒜 f g : Away 𝒜 (f*g) ≃+* Away 𝒜 (g*f)`.
  It is the equality-induced `Away.congr 𝒜 (mul_comm f g)`, not an
  arbitrarily chosen equivalence. The left and right `awayMap` compatibility
  lemmas say that it identifies the restrictions from both original chart
  rings; `awayMap_mk` gives the stipulated homogeneous-fraction formula.
- Identity for equal charts is precisely `Away.overlapEquiv_self`:
  `Away.overlapEquiv 𝒜 f f = RingEquiv.refl _`.
  This is identity on the self-overlap model `Away 𝒜 (f*f)`;
  localization at `f^d/f^d = 1` also identifies that model with the f-chart.
- Inversion under exchanging the charts is `Away.overlapEquiv_symm`:
  `(Away.overlapEquiv 𝒜 f g).symm = Away.overlapEquiv 𝒜 g f`.
- The triple overlap is `Away 𝒜 z`, `hz : z = f*g*h`.
  The three conjuncts of `Away.overlapEquiv_cocycle` say that restriction
  after each of the transitions fg, gh, fh agrees with direct restriction
  to this same ring. The recorded theorem expresses the cocycle using the
  common triple-overlap model: all three induced transitions are the identity,
  so the gh transition composed with the fg transition equals the fh
  transition. I also read `awayMap_awayMap` (composition of restrictions)
  and `Away.awayMap_overlapEquiv` (the restriction compatibility).
  Product-localization applied again realizes these as the triple restrictions
  of the double-overlap equivalences. Thus these are the same canonical maps
  as the node's comparisons through the common ring `A_fgh`, expressed using
  that ring itself as a model rather than new named iterated localizations.

The blueprint source was read in full at
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-def-nagata-sketch-data/lemma-nagata-proj-chart-ring-cocycle.md`.
It explicitly describes using the canonical maps into the common product
localizations and checking equality there, as does the published family.
No statement correction, new node, dependency repair, or disputed statement.

Edge cases checked: the zero ring, zero or nilpotent homogeneous elements,
zero divisors, repeated f,g,h, and unequal positive degrees. None of the
published declarations requires a domain, a nonzero element, cancellation in R,
or equal degrees. Localizations may be zero rings. The nonzero-degree
hypothesis needed only for `isLocalization_mul` follows from positivity;
it is not a missing nonvanishing hypothesis on f. The general index type and
general grading API include the node's natural grading without excluding any
ring universe. There is no finite-index or nonempty-index assumption.

Searches performed:

- LeanFinder via msearch: "canonical transition equivalences of homogeneous
  degree zero localization chart overlaps identity inverse cocycle"; eight
  results, mostly fiber-bundle identities and Proj.awayMap_awayToSection,
  no exact Mathlib coherence family.
- Loogle via msearch: `HomogeneousLocalization.Away.overlapEquiv`; no hit
  (unknown identifier in Mathlib). A subsequent search for
  `HomogeneousLocalization.Away.isLocalization_mul` returned the exact
  ring-localization identification used above.
- Mathlib grep via msearch: `overlapEquiv|isLocalization_mul` in
  `RingTheory/GradedAlgebra`; hit `Away.isLocalization_mul` at line 887.
- LeanSearch via msearch: "homogeneous localization chart overlap equivalence
  cocycle"; service unavailable (Internal Server Error), recorded as such.
- Direct rg for `overlapEquiv|lemma-nagata-proj-chart-ring-cocycle` in the
  local upstream and project Lean trees: no declaration in the stale local
  upstream; a mention in `NagataAffineProjScalarExtension.lean` only.
  Broader `overlapEquiv|chart.*cocycle` likewise found no duplicate family
  in the project. The item's audit pointed to the exact upstream family;
  the published-source query confirmed all six declarations and docstrings.

Validation: the deliver2 dry run checks every recorded declaration on the
server with a generated #check probe, then runs server preflight. No local
compiler is used. The dry run printed OK: the declaration checks compiled and server preflight
passed except for the expected second-reading section, which the fresh reader
will supply. Nothing was pushed.

## Second reading by NW

I independently opened the node copy, the exact blueprint source, Stacks
`constructions.tex` at `lemma-standard-open` (Tag 01M4), the dependency node
`def-nagata-homogeneous-localization-degree-zero`, Mathlib's actual `Away`,
`Away.mk`, `Away.mk_surjective`, `awayMap`, `awayMap_mk`,
`Away.isLocalizationElem`, and `Away.isLocalization_mul`, and the current
published upstream module returned anew by `scompile.py --source`.
The local upstream checkout lacks the published ChartCocycle section; I did
not infer absence from that stale checkout.

Object/hypothesis/conclusion checklist, with independent verdicts:

1. The underlying object is an arbitrary commutative ring R with an N-grading.
   The published section binds `{ι σ A : Type*} [CommRing A] [SetLike σ A]
   [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ)
   [GradedRing 𝒜]`. Setting ι to N and σ to additive subgroups supplies exactly
   the node's graded rings. These are structures of the grading, not extra
   Noetherian, domain, finiteness, or field hypotheses. Verdict: matches.
2. The elements f,g,h have arbitrary positive degrees d,e,k. The main theorem
   has `{d e e' : ι} {f g h z : A}`, `hf : f ∈ 𝒜 d`, `hg : g ∈ 𝒜 e`,
   `hh : h ∈ 𝒜 e'`, and `hz : z = f*g*h`. Specializing to positive natural
   degrees covers every requested triple; z is merely an explicit name for
   the product. There is no equal-degree assumption. Verdict: matches.
3. The chart object is the dependency's actual
   `HomogeneousLocalization.Away 𝒜 f`, not an independently defined ring.
   Its constructor is x/f^m with x in degree m*d, and mk_surjective verifies
   these representatives exhaust it, including the nilpotent case.
   Verdict: exactly the dependency's notion.
4. The restrictions on the double overlap are Away at fg and gf. I checked
   `Away.isLocalization_mul hf hg rfl hd` with hd : d ≠ 0: with algebra map
   `awayMap 𝒜 hg rfl`, Away at fg localizes Away at f at
   `Away.isLocalizationElem hf hg = g^d/f^e`. The swapped theorem gives the
   other restricted chart. This is precisely B_f^g and B_g^f from the node's
   proof, in alternative localization models. Positivity supplies hd.
   Verdict: matches; no unlocalized map A_f → A_g is asserted.
5. The canonical transition is `Away.overlapEquiv 𝒜 f g`, explicitly
   `Away.congr 𝒜 (mul_comm f g)`. The left/right compatibility lemmas identify
   the canonical maps from both original charts. Mathlib's `awayMap_mk`
   sends x/f^m to x*g^m/(fg)^m. This establishes the canonical comparison
   through A_fg required by the node, rather than an arbitrary isomorphism.
   Verdict: matches.
6. Identity on the self overlap is `Away.overlapEquiv_self f`:
   `Away.overlapEquiv 𝒜 f f = RingEquiv.refl _`. Its object is Away at f*f;
   the localizing element f^d/f^d is 1, so this also represents the whole
   original chart, as in the node. Verdict: matches.
7. Exchange of charts is `Away.overlapEquiv_symm f g`:
   `(Away.overlapEquiv 𝒜 f g).symm = Away.overlapEquiv 𝒜 g f`.
   Verdict: exactly the inverse clause.
8. The triple overlap is Away at z=f*g*h. The three conjuncts of
   `Away.overlapEquiv_cocycle` compare the fg, gh, and fh transitions followed
   by their respective restrictions into this same ring. Each becomes the
   identity in the common model. Thus their induced automorphisms compose
   as beta_gh beta_fg = beta_fh. This is the node's cocycle after the
   canonical comparison with A_fgh, not a claim that a double-overlap
   equivalence already has the domain of another double-overlap equivalence.
   I also read `awayMap_awayMap`: successive chart restrictions agree with
   restriction by the product multiplier. Applying isLocalization_mul to
   (fg,h), (gf,h), (gh,f), and (fh,g) verifies these are restrictions to the
   triple overlap; its source degree is positive in every case. Localization
   uniqueness transports the equalities back to the T_f,T_g,T_h models of
   the node proof. Verdict: matches all three transitions and the cocycle.

The Stacks context assumes only a graded ring and homogeneous positive-degree
standard-open indices. It imposes no integral-domain, Noetherian, or
nonvanishing assumption. The node's use of products fits this context.
The existing family is more general in grading and degrees; its indicated
specialization has exactly the requested meaning. I found no mismatch to
repair, no statement_change, no new node, and no dependency module.

Edge cases: the zero ring, zero homogeneous indices, nilpotent indices, zero
divisors, and repeated indices all remain allowed. The overlap may be the zero
ring (the corresponding scheme is empty); the universal property and the
identities remain valid. Fractions with exponent m=0 are included by the
natural exponent binder. Degree zero is excluded only by the node's own
positivity condition when identifying chart restrictions; the existing
coherence formulas themselves even allow it. There is no index-family,
nonempty-set, characteristic, or scheme-size restriction. The independent
Type* binders do not identify the ring and grading universes.

Independent H4 searches: msearch Loogle query
`HomogeneousLocalization.Away.isLocalization_mul` returned the exact Mathlib
localization theorem. LeanFinder query `degree zero localization standard Proj
charts change order of product triple intersection compatibility` returned
Proj SpecMap/awayMap and pullbackAway identities, no competing ring-coherence
family. Direct rg for `overlapEquiv|awayMap_awayMap|isLocalization_mul|chart.*[Cc]oher`
in both project Lean and upstream Lean found applications of the Mathlib
localization theorem, but no second chart-coherence implementation in those
local trees. Reading the current server source positively established the
existing six-declaration family. The worker's recorded failed LeanSearch call
is retained as unavailable rather than reported as a successful search.

H5/H6/H8/H9: no new data or proof is written. The existing overlapEquiv has
real equality-transport data; the proof terms and signatures in the published
section are present. The existing declaration docstrings identify this
blueprint and explain the triple restriction formulation. There is no sandbox
module whose binders, imports, or docstrings need repair. The recorded main
signature was checked against the published declaration verbatim. Second
reading changed only this report; the correct existing declaration record is
preserved. Server declaration probes and preflight are run by deliver2 below.
