## Worker report

Recorded the exact existing declaration
`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` in
`WeilConjectures.RingTheory.ProEtale.HenselianLocalRing` (source lines 243–248).
No module, definition, proof, or sorry was added. Only the item's `lean` record changes.
The node already had an incomplete attachment record pointing to this same theorem;
this delivery supplies its full stage-2 record. Its existing status is preserved.

Hypothesis and clause correspondence:

- Commutative local rings A and B: ambient `{R S : Type u}`, `[CommRing R]`,
  `[CommRing S]`, `[IsLocalRing S]`; `IsStrictlyHenselianLocalRing R` extends
  `HenselianLocalRing R`, which supplies `IsLocalRing R`.
- The map A → B: `[Algebra R S]` and `algebraMap R S`. Every commutative ring
  homomorphism gives this algebra structure, so this does not restrict the map.
- It is local: ambient `[IsLocalHom (algebraMap R S)]`.
- A is strictly henselian: `[IsStrictlyHenselianLocalRing R]`, exactly the recorded
  dependency class, henselian with separably closed residue field.
- The map is weakly etale: `[Algebra.WeaklyEtale R S]`, exactly the recorded
  dependency's existing notion, flat over R and flat tensor multiplication.
- It is an isomorphism: `Function.Bijective (algebraMap R S)`; a bijective ring
  homomorphism has an inverse ring homomorphism, with no extra hypothesis.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`, its full class fields and the equivalence
  `isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed`.
- `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes `Algebra.WeaklyEtale`
  from `Mathlib.RingTheory.Etale.Weakly`. Read the full class: `flat` and
  `flat_lmul'`. Its principal ind-Zariski construction is irrelevant to this theorem.
- Read the full upstream theorem signature, ambient binders and docstring, and
  confirmed them using `scompile.py --source` against current server sources.

Edge cases: local rings here are nontrivial, as in the source; the zero ring is
therefore not silently lost. Identity maps and arbitrary characteristics remain
allowed. No finite-presentation or ind-etale hypothesis is imposed. The common
universe is arbitrary and accommodates both rings in their maximum universe;
there is no quantified test-ring universe that could render a hypothesis vacuous.
The conclusion concerns the original structure map, not an arbitrary equivalence.
No statement dispute or statement correction was needed.

Searches (2026-10-15):

- `msearch.py ... leanfinder "A local weakly etale map of local rings with strictly
  henselian source is bijective"`: eight Mathlib hits, including the distinct
  formally-unramified finite-type algebraically-closed-field theorem; no exact hit.
- `msearch.py ... loogle
  "Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing"`: zero hits,
  unknown identifier in the Mathlib search index.
- `msearch.py ... grep "WeaklyEtale|bijective_of_isStrictlyHenselianLocalRing"
  RingTheory`: five hits in `Mathlib/RingTheory/Etale/Weakly.lean`, giving the class
  and its universe transport, not this theorem.
- `rg -n "bijective_of_isStrictlyHenselianLocalRing|class WeaklyEtale|def WeaklyEtale"`
  in upstream `WeilConjectures` and project `lean/Sheaf`: exact theorem at upstream
  `RingTheory/ProEtale/HenselianLocalRing.lean:245`, with existing uses in both trees.
- `grep -rn "thm-weil-pbc-weak-etale-strict-local"` in upstream `WeilConjectures`:
  no blueprint-id occurrence; the declaration-name match above is exact.

Validation: delivery dry run checks the existing declaration on the server and
runs the maintainer's preflight. No new Lean file exists to compile separately.

## Second reading by NX

Independently read the complete node and blueprint source, Stacks more-algebra.tex
lines 30787–30829 (Tag 092Z, theorem-olivier), the existing theorem including its
ambient binders and preceding section boundaries, and the current server source
using `scompile.py --source WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`.
The source theorem assumes no additional section-wide finiteness or Noetherian
hypothesis. Its statement is exactly the node's statement.

Object/hypothesis/conclusion checklist, with verdicts:

- Two commutative rings A and B: `{R S : Type u} [CommRing R] [CommRing S]`.
  Correct; neither is restricted to a field, domain, or finite algebra.
- Both are local: `[IsLocalRing S]` is ambient; locality of R follows by the
  actual class inheritance `IsStrictlyHenselianLocalRing R` extends
  `HenselianLocalRing R`, which extends `IsLocalRing R`. Correct.
- A specified ring map A → B: `[Algebra R S]` supplies `algebraMap R S`.
  Correct: every commutative ring homomorphism supplies such an algebra structure.
- The specified map is local: `[IsLocalHom (algebraMap R S)]` is ambient.
  Correct; it concerns this map, not the mere existence of a local map.
- A is strictly henselian: `[IsStrictlyHenselianLocalRing R]`. Correct after
  reading the dependency node and upstream class fields: henselian and separably
  closed residue field. Read also the upstream equivalence with the conjunction.
- The map is weakly etale: `[Algebra.WeaklyEtale R S]`. Correct after reading the
  dependency node, its recorded module `Sheaf.RingTheory.IndPrincipalZariski`,
  and Mathlib's class in RingTheory/Etale/Weakly.lean. The fields are flatness
  over R and flatness of tensor multiplication; no ind-etale assumption is added.
- The original map is an isomorphism: `Function.Bijective (algebraMap R S)`.
  Correct and equivalent: a bijective ring homomorphism has a ring-hom inverse.
  This does not replace the map by an unrelated isomorphism.

Edge cases: `IsLocalRing` extends `Nontrivial`, matching the source convention
that local rings have a maximal ideal, so zero rings/empty affine schemes are
outside both statements. Identity maps, separably closed fields, mixed and positive
characteristics, and non-Noetherian local rings remain included. No index, degree,
or positivity parameter occurs. The common universe u is arbitrary; both rings
can be placed in the maximum of their universes (Lean's cumulative Type universes),
so no mathematical pair of rings is excluded. There is no lower-universe universal
test object that could make a hypothesis vacuous. All binders are accounted for.

Independent searches used different phrasing from the worker:

- LeanFinder: `weakly etale algebra local homomorphism strictly henselian implies
  ring equivalence` returned eight etale-algebra hits, none this statement.
- Loogle: `IsStrictlyHenselianLocalRing, Function.Bijective` returned no hits
  (the Mathlib index does not know this upstream class).
- `rg` for `strictly.henselian|StrictlyHenselian|bijective_of_henselianLocalRing`
  in project Sheaf, upstream RingTheory, and Mathlib RingTheory/Etale found the
  existing upstream theorem and its uses; a focused `rg` for both bijectivity
  theorem names across the entire upstream and project confirmed the exact match.
  Mathlib's `WeaklyEtale.ulift_iff` also explicitly supports universe transport.

No mismatch was found, and no Lean or node change was needed in this second
reading. The recorded `lean.statement` is verbatim the existing lemma signature
through its result. The signature contains no hidden extra section assumptions.
There are no new definition nodes, dependency modules, hollow definitions, or
postponed proofs in this delivery. Existing source docstrings and proofs are
preserved; no duplicate module is written merely to add blueprint documentation.
No statement correction or citer audit is required. Validation uses the server
existing-declaration preflight; there is no delivered Lean file to compile.
