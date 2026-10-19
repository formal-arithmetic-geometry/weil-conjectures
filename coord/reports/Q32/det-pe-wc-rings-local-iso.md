## Worker report

The node is already stated by the sorry-free slopmaster2 declaration
`Algebra.WeaklyEtale.bijective_localRingHom_of_isStrictlyHenselianLocalRing` in
`WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale` (lines 245--264).  Therefore no
new module is written.  The declaration states the canonical map from the localization
of `A` at `n.comap (algebraMap A B)` to the localization of `B` at the prime `n`,
with `A` and `B` commutative rings, an `Algebra A B` structure, a weakly etale algebra
structure, `n` prime, and strict henselianity of the source localization; its conclusion
is `Function.Bijective` for `Localization.localRingHom ...`.  This is the Lean
form of the node's assertion that the induced local-ring map
`R_m -> B_n` is an isomorphism, with `m = n ∩ R`.

The node has no statement dependencies.  The attached declaration's proof uses the
canonical weakly-etale localization and transitivity instances and the strict-henselian
local weakly-etale bijectivity theorem; no additional assumptions are introduced.

Edge cases checked: the prime `n` supplies the prime contraction used for the source
localization; the source strict-henselian hypothesis is on exactly that localization;
`Localization.localRingHom` uses the canonical map and equality proof `rfl`; no
finite-presentation, ind-etale, nonzero, or characteristic hypothesis is present.
The statement permits arbitrary commutative rings and arbitrary primes, including the
zero/localization cases allowed by the source theorem.

Searches made (recorded in `searches.jsonl`):

- `msearch.py ... grep bijective_localRingHom_of_isStrictlyHenselianLocalRing WeilConjectures`:
  no hits (the attached declaration is in the current upstream source module index).
- `msearch.py ... loogle WeaklyEtale, Localization.localRingHom, IsStrictlyHenselianLocalRing`:
  unavailable/unknown identifier, no result.
- `msearch.py ... leanfinder local rings of a weakly etale algebra over a strictly henselian point`:
  eight Mathlib hits, none matching the theorem.
- `msearch.py ... grep StrictlyHenselianLocalRing WeilConjectures`:
  no hits.
- `msearch.py ... loogle Algebra.WeaklyEtale.bijective_localRingHom_of_isStrictlyHenselianLocalRing`:
  unavailable/unknown identifier, no result.

The node's existing Lean record was attached by the lead on 2026-10-16 after two
remote workers confirmed the statement match; the source file and sorry map show it is
sorry-free.

## Second reading by Q32

I opened the node copy, its exact blueprint source
`main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-wc-rings/det-pe-wc-rings-local-iso.md`,
the claimed upstream theorem with its ambient binders in `IndWeaklyEtale.lean:218-264`,
and the definitions of weak etaleness, strict henselianity and `Localization.localRingHom`.
I also read Stacks `more-algebra.tex`, Theorem Olivier (Tag 092Z,
`theorem-olivier`, lines 30787-30828), and the related stalk argument in
`more-morphisms.tex`, `lemma-weakly-etale-strictly-henselian-local-rings`.
Olivier assumes a local homomorphism of local commutative rings, strict henselianity
of the source, and weak etaleness; it assumes no Noetherianity, finite presentation,
characteristic or field structure.

The worker's existing binding has an H3 mismatch: it drops maximality of the base
prime, replaces the explicitly given `m` and its contraction equality by the
contraction itself, and binds both rings in one universe. Its theorem is useful and
true, but is more general than the node's stated maximal-point assertion. The
worker report's claim of exactly matching hypotheses was therefore inaccurate.
I retained the worker report above as requested and replaced the binding by an
explicit statement of the node in
`lean/Sheaf/RingTheory/StrictHenselianMaximalLocalRingIso.lean`. No mathematical node
statement, dependency list, proof or target was changed; no statement_change is needed.

Object/hypothesis/conclusion checklist, in the order of the node:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Commutative rings R and B | `{R : Type u} {B : Type v} [CommRing R] [CommRing B]` | Exact; independent universes. |
| The ring map R -> B | `[Algebra R B]`, with `algebraMap R B` throughout | Exact algebra encoding of the given ring map. |
| The map is weakly etale | `[Algebra.WeaklyEtale R B]` | Exact Mathlib class: flat structure map and flat multiplication map. |
| Parenthetical ind-etale example | No additional hypothesis | Correct: an example, not a required condition; the stability node supplies the implication. |
| A maximal ideal m of R | `(m : Ideal R) [m.IsMaximal]` | Exact; maximality is now explicitly retained. |
| R_m is strictly henselian | `[IsStrictlyHenselianLocalRing (Localization.AtPrime m)]` | Exact existing class, extending henselian locality with separably closed residue field. |
| A prime ideal n of B | `(n : Ideal B) [n.IsPrime]` | Exact; n need not be maximal. |
| n contracts to m | `(hmn : m = n.comap (algebraMap R B))` | Exact equality, with its orientation chosen for the canonical localization API. |
| The induced map R_m -> B_n | `Localization.localRingHom m n (algebraMap R B) hmn` | Exact canonical map; its defining formula sends r/1 to its image/1. |
| This map is an isomorphism | `Function.Bijective` of that ring homomorphism | Exact: a bijective ring homomorphism has the unique inverse ring homomorphism. |

There is no additional local-map assumption: the displayed localization map is
canonically local. `m.IsPrime` comes from maximality, without another hypothesis.
There is no arbitrary comparison map or chosen inverse. No new definition, hollow
data, private helper, file-local instance/notation, or extra theorem is introduced.
The only postponed theorem is the item itself, with proof exactly `sorry`.
Its module/declaration docstrings name the source and blueprint id; the declaration
docstring follows every step of the node's proof: ind-etale implies weakly etale,
base change to R_m, localization to B_n, composition and locality, then Olivier.
The recorded `lean.statement` is verbatim from the theorem keyword up to the proof delimiter `:=`.
Every variable and universe is explicitly bound, and all lines are at most 100 columns.

The node has no statement dependencies. For proof dependencies I opened both nodes
and their recorded source declarations. `lem-weil-pbc-ind-etale-stability` uses
`Sheaf.RingTheory.IndEtaleStability`, whose `RingHom.indEtale_principalZariski_stability`
includes ind-etale implying weakly etale and weak-etale composition/base change;
`thm-weil-pbc-weak-etale-strict-local` uses
`WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`, whose
`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` has the local-map and
local-target ambient instances required by Olivier. Both proof modules are imported
without `public`. The actual definitions used in the signature are imported publicly
from their owning Mathlib/upstream modules, without private copies.
There are no new nodes or dependency-module repairs to review.

Edge cases: a zero ring has no prime/maximal ideals, so the node and Lean both have
no instances of the hypotheses there. Localization at the given proper primes is
nonzero and local as required, without an added nonzero hypothesis. The empty affine
scheme is thus treated vacuously. There is no index set, degree n, or size/finiteness
parameter. Every characteristic is permitted; R and B have independent universes
`u` and `v`. The theorem never assumes that B_n is strictly henselian or that n is
maximal in B. The order R, B, weak etaleness, m, its strict henselian localization,
n and its contraction equality, and finally bijectivity agrees with the node.

Independent searches (different queries from the first worker):

- `msearch.py ... leansearch "The localization map at primes above a strictly henselian maximal ideal is bijective for a weakly etale ring homomorphism"`:
  eight results, including `bijective_of_isLocalization_isMaximal` and spectrum/product
  localization maps; none is this weak-etale strict-henselian maximal-point statement.
- `msearch.py ... loogle "Localization.localRingHom, Function.Bijective"`:
  three results, concerning a saturated subalgebra, a finite map, or a conductor;
  their hypotheses differ from this node.
- `msearch.py ... grep "localRingHom|henselian" RingTheory/Etale`:
  no Mathlib hits in that subtree. I also ran `rg` for
  `bijective_localRingHom|strictly.henselian.*local|henselian.*[Ii]som` over
  Mathlib/RingTheory, the upstream WeilConjectures/RingTheory and project lean/Sheaf.
  The upstream contraction-prime theorem is the closest match but omits maximality;
  the neighboring algebraMap theorem assumes R itself strictly henselian/local,
  and the stalk-bijectivity class assumes bijectivity rather than deriving it here.
  `RetractionsStrictlyHenselian.lean` instead proves strict henselianity of contraction
  localizations. None is the exact explicit maximal-point statement.
- I checked the proposed new theorem/module names over the project's Lean, all
  upstream WeilConjectures and Mathlib; neither name already occurs.

Validation: `scompile.py Q32 det-pe-wc-rings-local-iso` compiled the sole delivered
module both as a sandbox file and under its actual library module name. Both passed
in 2.7 seconds without warnings or errors. Delivery dry-run and push follow below.

The first dry run detected that my signature extraction accidentally started at the
word "theorem" inside the proof docstring. I corrected `lean.statement` to start at
the actual declaration keyword; this was a record-only repair. The Lean compiled
cleanly in that dry run as well.
