## Worker report

The module `Sheaf.RingTheory.QuasiFiniteMonogenicIntegralClosure` states
`Algebra.quasiFiniteAtPrime_monogenic_integralClosure`, with its sole proof `sorry`.
No definitions are added. The node is unchanged except for its `lean` record.

Source checked: [Stacks Project, Algebra, Tag 00Q8](https://stacks.math.columbia.edu/tag/00Q8),
including the proof. The local `literature/stacks-project/algebra.tex` is absent on this
machine, so the authoritative tag page was opened instead. Its statement agrees with the node.
The declaration docstring records all nine proof steps, including the split's expanded arguments.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| R is a commutative ring | `(R : Type u) [CommRing R]` |
| I is an ideal of R[X] | `(I : Ideal (Polynomial R))` |
| S = R[X]/I, with its canonical R-algebra | Every occurrence of S is `Polynomial R ⧸ I`; Mathlib supplies its quotient algebra structure |
| S is of finite type over R | The canonical `Algebra.FiniteType R (Polynomial R ⧸ I)` instance is synthesized for `IsQuasiFiniteAtPrime`; it follows from polynomial finite type and quotient finite type, so no extra assumption is needed |
| q is a prime ideal of S | `(q : PrimeSpectrum (Polynomial R ⧸ I))`, with ideal `q.asIdeal` |
| R → S is quasi-finite at q | `(hq : IsQuasiFiniteAtPrime R (Polynomial R ⧸ I) q)` |
| S' is the integral closure of R in S | `integralClosure R (Polynomial R ⧸ I)` |
| There exists g in S' | `∃ g : integralClosure R (Polynomial R ⧸ I)` |
| g is not in q | `(g : Polynomial R ⧸ I) ∉ q.asIdeal` |
| S'_g → S_g is the inclusion-induced localization map | `Localization.awayMap (integralClosure R (Polynomial R ⧸ I)).val.toRingHom g` |
| This map is an isomorphism | `Function.Bijective` of this ring homomorphism; a bijective ring hom is exactly a ring isomorphism |

The source and target types of `awayMap` are respectively `Localization.Away g` and
`Localization.Away ((integralClosure R (Polynomial R ⧸ I)).val.toRingHom g)`.
The latter denominator is the image of g in S, definitionally the subtype coercion.
This specifies the canonical map, rather than merely an unrelated isomorphism of the two rings.
The localization functor sends the fraction y/g^n to its identical fraction in S_g.

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`;
  read its constructor, finitely supported coefficient representation and docstring.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `Algebra.FiniteType`; read the class signature and docstring. Imported transitively
  by the required `Sheaf.RingTheory.QuasiFiniteAtPrime` module.
- `def-weil-pbc-ring-map-quasi-finite-at-prime`:
  `Sheaf.RingTheory.QuasiFiniteAtPrime`, `Algebra.IsQuasiFiniteAtPrime`;
  full signature, definition and docstring read. It asks for the singleton of the
  corresponding prime of the residue-field fibre to be open, exactly the node's notion.
- `def-weil-pbc-integral-closure`: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`; read the signature, docstring and carrier `{r | IsIntegral R r}`.
- `def-weil-ring-localization-away`: `Mathlib.GroupTheory.MonoidLocalization.Away`,
  `Localization.Away`; read its definition as localization at `Submonoid.powers`.
  `Mathlib.RingTheory.Localization.Away.Basic` supplies its ring structure and
  `Localization.awayMap`, whose full signature and implementation were read.

Edge cases checked before writing: R may be the zero ring, and I may be the unit
ideal; then the quotient has no prime, so the prime binder makes those cases vacuous
without adding nontriviality assumptions. I = 0 is permitted; no quasi-finite prime
exists in the polynomial algebra, as the source's fibre argument shows. Nilpotents,
zero divisors and positive characteristic are all allowed; no domain, reducedness,
Noetherian or characteristic hypotheses were added. An element outside a prime cannot
be zero or nilpotent. The quotient lives in the same universe as R by construction;
`universe u` is arbitrary, so the literal polynomial quotient imposes no universe
restriction beyond that already intrinsic to the statement. No `let` occurs in the signature.

Searches for an existing statement (all msearch calls are recorded in searches.jsonl):

- LeanSearch, query `monogenic polynomial quotient quasi finite at prime integral closure localization isomorphism`:
  service unavailable (Internal Server Error); no verdict assigned to this unavailable service.
- LeanFinder, same query: eight hits including `Algebra.QuasiFiniteAt`,
  `Algebra.ZariskisMainProperty` and finite-type integral quasi-finiteness.
  These do not state this node with its recorded isolated-point quasi-finiteness.
- Loogle, query `Algebra.ZariskisMainProperty`: eleven hits including `.of_finiteType`
  and `.of_finiteType_of_weaklyQuasiFiniteAt`; the hypotheses use Mathlib's different
  quasi-finiteness predicates and are not the node's literal statement.
- msearch grep, query `ZariskisMainProperty|integralClosure.*Away|monogenic` in RingTheory:
  hits in Zariski's Main Theorem, smooth integral closure, and étale material.
  The monogenic lemma `.of_adjoin_eq_top` is private and uses WeaklyQuasiFiniteAt;
  the public general theorem also uses a different quasi-finiteness predicate.
- `rg` for `monogenic|integralClosure.*Away|IsQuasiFiniteAtPrime` in the source project
  and `lean/Sheaf/RingTheory`: no exact existing monogenic statement. The project
  `Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime` in
  `Sheaf.RingTheory.ZariskisMainAway` is the more general finite-type theorem, a different
  DAG node, not a declaration with this polynomial-quotient signature.
- `grep -rn` for this node's id in the source project: no hits.
- Name-clash `rg` in Mathlib, source, project and `dag/lean_names_upstream.json`:
  no existing `quasiFiniteAtPrime_monogenic_integralClosure` declaration.

All dependency records are usable. No statement correction, missing notion, or dispute.
The initial server single-file compile passed (exit 0, 1.5 seconds), with no warnings.


## Second reading by E1

Independent reading with the item's node, module and all five statement-dependency
nodes open. Verdict: the Lean states exactly the node's claim; no mismatch found.
No Lean, node, signature or proof-plan change was needed. This section and the
independent search records are the only additions.

Source read independently: Stacks `algebra.tex`, fetched read-only from
`https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex` into
sandbox `scratchpad/algebra.tex` because the repository's literature copy is absent.
Read lines 30735–30781 (label `lemma-quasi-finite-monogenic`, Tag 00Q8), the start
of the Zariski's Main Theorem section at 30454, and the chapter conventions.
Also opened https://stacks.math.columbia.edu/tag/00Q8. The chapter allows the zero
ring and assumes rings commutative with 1; the section concerns finite-type maps.
There is no domain, injectivity, Noetherian or characteristic assumption throughout.
The proof explicitly uses the inclusion-induced localization map, as does the node.

The object's, hypothesis's and conclusion's checklist, written from the node:

| Node object, hypothesis or clause | Lean rendering and verdict |
| --- | --- |
| A commutative ring R | `(R : Type u) [CommRing R]`; exact, including the zero ring. |
| An ideal I in the one-variable polynomial ring R[X] | `(I : Ideal (Polynomial R))`; exact. |
| S is R[X]/I with its canonical R-algebra structure | `Polynomial R ⧸ I` throughout; canonical polynomial and quotient algebra instances, with no arbitrary additional map. Exact. |
| S is of finite type over R | The `Algebra.FiniteType R (Polynomial R ⧸ I)` argument of `IsQuasiFiniteAtPrime` is synthesized, rather than imposed as an extra assumption. `FiniteType.lean` lines 98–105 give the quotient and polynomial instances. Exact. |
| A prime ideal q of S | `(q : PrimeSpectrum (Polynomial R ⧸ I))`; its underlying ideal is `q.asIdeal`. This bundles precisely the ideal and its primality proof. Exact. |
| R → S is quasi-finite at q | `(hq : IsQuasiFiniteAtPrime R (Polynomial R ⧸ I) q)`; exactly the recorded dependency definition, with the canonical contraction and corresponding fibre prime. |
| S' is the integral closure of R in S | `integralClosure R (Polynomial R ⧸ I)`; exactly the subalgebra of elements integral over R, with its subtype ring. |
| There exists g in S' | `∃ g : integralClosure R (Polynomial R ⧸ I)`; exact, after all input objects and hypotheses. |
| g is outside q as an element of S | `(g : Polynomial R ⧸ I) ∉ q.asIdeal`; exact, after coercion along the inclusion. |
| S'_g → S_g is the map y/g^n ↦ y/g^n | `Localization.awayMap (integralClosure R (Polynomial R ⧸ I)).val.toRingHom g`; exact canonical localization of the subalgebra inclusion. Its domain is `Localization.Away g`, its codomain `Localization.Away (val g)`. |
| This map is an isomorphism | `Function.Bijective` of that ring homomorphism; precisely invertibility of the specified homomorphism, equivalent to a ring equivalence with that underlying map. Exact. |

Dependency signatures and implementations checked independently:
`Polynomial` in `Mathlib.Algebra.Polynomial.Basic` (lines 67–76) is the finitely
supported coefficient representation; `Algebra.FiniteType` in
`Mathlib.RingTheory.FiniteType` (lines 36–40) means the top subalgebra is finitely
generated; `integralClosure` in
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (lines 215–223) has carrier
`{r | IsIntegral R r}`. `Localization.Away` in
`Mathlib.GroupTheory.MonoidLocalization.Away` (lines 137–143) localizes at
`Submonoid.powers`, and `Localization.awayMap` in
`Mathlib.RingTheory.Localization.Away.Basic` (lines 496–499) is the induced map
between those localizations. Each is the dependency node's stated notion.

Read the entire recorded `Sheaf.RingTheory.QuasiFiniteAtPrime` module.
`Algebra.IsQuasiFiniteAtPrime` takes precisely commutative rings, their algebra,
finite type and a prime, and asks for openness of the singleton of the corresponding
prime in `p.asIdeal.Fiber S`. Checked `Ideal.Fiber` and
`PrimeSpectrum.preimageHomeomorphFiber` in Mathlib's
`RingTheory/LocalRing/ResidueField/Fiber.lean`: this is the residue-field tensor
fibre and its canonical spectrum homeomorphism. The tensor ordering κ(p) ⊗ S
agrees with the node's S ⊗ κ(p) by the canonical swap; the corresponding prime is
preserved. No dependency needs repair, no private notion is introduced, and there
are no new definition nodes or dependency modules in the delivery.

Edge cases: if R is the zero ring or I is the unit ideal, S is the zero ring and
has no prime, so the binder q correctly makes the assertion vacuous. I = 0 is
allowed; polynomial fibres have no isolated primes, so hq cannot hold. Nilpotents,
zero divisors, noninjective structure maps and every characteristic remain allowed.
For instance I = (X) is an integral quotient and the required localization can be
at 1. No empty-index restriction is introduced; there is no index or degree binder
in the signature. The n = 0 relation in the proof plan is correctly vacuous, and
localization denominators include the zeroth power. An element outside a prime is
neither zero nor nilpotent, without adding a separate hypothesis. The arbitrary
universe u covers every ring carrier, and polynomial, quotient, subalgebra and
localization stay in that universe: there is no independent test universe or extra
smallness restriction. Every variable and universe is explicitly bound.

Independent searches (recorded by msearch in searches.jsonl):

- LeanFinder: `single generator algebra isolated fibre prime integral elements invert one element`.
  Eight hits, notably `Algebra.ZariskisMainProperty`, its equivalences and integral
  special cases; none states the polynomial quotient claim with the recorded predicate.
- Loogle: `integralClosure`. Twelve hits, including the existing subalgebra and
  basic integral-closure lemmas; confirms reuse of the established notion, no matching theorem.
- LeanSearch: `polynomial quotient integral closure local isomorphism quasi finite`.
  Service returned Internal Server Error, recorded unavailable, with no negative verdict.
- msearch grep: `ZariskisMainProperty|IsQuasiFiniteAtPrime|integralClosure.*localization`.
  Twenty-five hits, including the Zariski main and smooth integral-closure modules.
- Direct rg across Mathlib, `WeilConjectures/`, repository `lean/Sheaf/RingTheory`
  and `dag/lean_names_upstream.json`, with `monogenic`, `integralClosure.*Away`,
  `ZariskisMainProperty` and the proposed declaration name. No exact existing declaration.
  Opened `ZariskisMainTheorem.lean` rather than deciding by its names:
  `.of_adjoin_eq_top` is private (line 464) and takes `WeaklyQuasiFiniteAt`;
  `.of_finiteType` (line 660) uses Mathlib `QuasiFiniteAt`. These do not directly
  state this node with its recorded isolated-fibre predicate. Opened the project's
  `ZariskisMainAway.lean`: its theorem is the general finite-type statement serving
  another node, not this polynomial-quotient signature. The existing definitions are
  all reused; no replacement definition or duplicate exact statement was found.

H5/H6/H8/H9 checks: the module introduces no definitions, only the one named
statement with `by sorry`. Module and declaration docstrings name Tag 00Q8 and the
correct blueprint id. The declaration docstring tracks all nine node proof steps,
including integral transitivity, the coefficient-reduction fibre argument, the
non-quasi-finiteness contradiction, the vacuous base and both induction cases.
Imports are used for the integral closure, away map and recorded quasi-finiteness
predicate; namespace is Algebra, with no Sheaf prefix. Lines are at most 100
characters, and there are no implicit unbound variables or let binders in the
statement. Programmatically checked that `lean.statement` equals the signature
verbatim. No statement correction, disputed statement or citer reassessment is needed.

Independent server single-file compile via scompile passed: exit 0, 1.6 seconds,
no errors and no warnings. No library build was run.
