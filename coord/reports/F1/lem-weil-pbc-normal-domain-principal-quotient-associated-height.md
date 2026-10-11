## Worker report

Module: `Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight`.
Declaration: `Ideal.height_eq_one_of_mem_associatedPrimes_quotient_span`.
It states the item with a `sorry` proof; it introduces no definition.

Hypothesis and clause correspondence:
- The commutative integral domain A is `{A : Type u} [CommRing A] [IsDomain A]`.
  The universe `u` is explicitly bound and arbitrary.
- Noetherian is `[IsNoetherianRing A]`, exactly every ideal being finitely generated.
- Normal domain is `[IsIntegrallyClosed A]` together with `[IsDomain A]`, the
  domain clause of the normal-ring dependency, not a new predicate.
- The nonzero element is `{a : A} (ha : a ≠ 0)`. There is no nonunit assumption.
- The principal quotient A/aA is `A ⧸ Ideal.span {a}`, the quotient ring viewed
  as an A-module with its canonical module structure.
- An arbitrary associated prime is `{p : Ideal A}` with
  `hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})`. Mathlib's definition uses
  radicals, but `isAssociatedPrime_iff` under the retained Noetherian hypothesis
  makes this exactly prime and equal to the annihilator of an element. Its witness
  cannot be zero: the annihilator of zero is the unit ideal, which is not prime.
  Thus it is exactly the node's nonzero-witness definition, without extra hypotheses.
- The conclusion `p.height = 1` says both clauses: `(0) < p` and absence of
  strict prime chains of length greater than one ending at p. On prime ideals,
  `PrimeSpectrum.height_eq_orderHeight` identifies ideal height with order height,
  defined as the supremum of chain lengths ending below or at p. In a domain `(0)`
  is the least prime, so height one forces `(0) < p`; conversely that strict chain
  and the node's upper bound force height exactly one.

Dependency declarations read and used:
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, with `isNoetherianRing_iff_ideal_fg` confirming its meaning.
- `def-weil-pbc-normal-ring`: its mathlib_match gives `IsDomain` and
  `IsIntegrallyClosed`, read in `Mathlib.Algebra.Ring.Defs` and
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. This item uses the
  normal-domain clause. No localization predicate is necessary in the statement.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`; its source and `Order.krullDim` were read. The statement uses
  the corresponding prime-chain invariant `Ideal.height` from
  `Mathlib.RingTheory.Ideal.Height`, not the dimension of the whole ring.
- Association and quotient use Mathlib's existing `associatedPrimes`,
  `isAssociatedPrime_iff`, `Ideal.span` and `Ideal.instHasQuotient`.

Source checked: https://stacks.math.columbia.edu/tag/031T, Lemma 10.157.6 (1),
including its proof and the comment explaining the unit case. The repository's
`literature/stacks-project/algebra.tex` is absent on this machine, so the primary
source was read online. The theorem docstring reproduces all six DAG proof steps
and names their dependencies. The item deliberately only extracts the height
assertion from (1), as already stated in its stage-1 record.

Edge cases checked before writing:
- If a is a unit, A/aA is zero and has no associated primes; the implication is
  vacuous, as required by the source. This includes fields and a = 1.
- a = 0 is excluded explicitly; including it would allow the height-zero prime
  of a domain, so the nonzero hypothesis is essential.
- A = 0 is excluded by IsDomain, matching integral domain in the node.
- p = (0) cannot meet the association hypothesis when a is nonzero, since a
  annihilates the quotient and therefore belongs to every such prime.
- No finite ring-dimension, local-ring or characteristic restriction is added;
  normal Noetherian domains of any characteristic and dimension are included.
- A chain of length zero is allowed by height's definition; height one excludes
  neither that chain nor its length-one witness, only lengths above one.

Searches made (all msearch calls used group F1 and this item):
- LeanFinder: "In a Noetherian normal integral domain associated primes of quotient
  by a nonzero principal ideal have height one". Eight hits: principal ideal
  theorem and quotient-dimension inequalities, none about all associated primes
  of normal-domain principal quotients. No exact match.
- Loogle: "IsIntegrallyClosed, IsAssociatedPrime". Zero hits.
- LeanSearch: "associated primes of a nonzero principal quotient of a Noetherian
  integrally closed domain have height one". UNAVAILABLE: Internal Server Error.
- msearch grep: "IsIntegrallyClosed|associatedPrimes|IsAssociatedPrime" in
  RingTheory/Ideal/AssociatedPrime. Fifteen hits in Basic/Finiteness/Localization;
  none give the requested integrally-closed height theorem.
- rg of "associatedPrimes|IsAssociatedPrime|principal.*height|height.*principal"
  in WeilConjectures and lean/Sheaf found related depth, localization and
  associated-prime lemmas, but no identical statement.
- rg of the node id in WeilConjectures and dag/lean_names_upstream.json found no
  recorded source declaration.
- rg of the proposed declaration and module names in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json found no collision.

No statement correction, disputed statement, new node or dependency module is needed.

## Second reading by F1

I reread the node statement, its Stacks source (Tag 031T, Lemma 10.157.6(1)), and the Lean declaration.
The objects and hypotheses correspond item by item:

- The commutative ring is Lean `{A : Type u} [CommRing A]`; the explicit universe is arbitrary.
- Integral-domain and normal-domain assumptions are `[IsDomain A]` and `[IsIntegrallyClosed A]`, exactly the
  normal-domain clause recorded by `def-weil-pbc-normal-ring`; no localization or field assumption is added.
- Noetherianity is `[IsNoetherianRing A]`, the Mathlib notion matching the node's finitely-generated-ideal
  condition.
- The nonzero element is `{a : A} (ha : a ≠ 0)`, with no nonunit hypothesis.
- The quotient is the canonical A-module `A ⧸ Ideal.span {a}`.
- The associated prime is `{p : Ideal A}` with
  `hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})`. Under the retained Noetherian hypothesis,
  Mathlib's `isAssociatedPrime_iff` removes the radical and gives an annihilator of an element; primality
  excludes the zero witness, so this is the node's stated nonzero-witness notion.
- The conclusion is `p.height = 1`. `Ideal.height` is the strict-prime-chain height, so this is exactly
  the node's two clauses: `(0) ⊊ p` and no strict chain of length greater than one ending at `p`.

I checked edge cases: a unit `a` gives the zero quotient and hence no associated prime (vacuous implication);
`a = 0` is correctly excluded; `IsDomain A` excludes the zero ring; `p = (0)` cannot be associated when
`a ≠ 0`; fields, arbitrary characteristic, arbitrary dimension, and height-zero chains are covered.
No independent test-algebra universe, local-ring, finite-dimension, or characteristic restriction appears.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with LeanFinder, Loogle, LeanSearch, and `rg` for
associated-prime/normal-domain/height variants and the proposed declaration. The only matches were general
associated-prime, height, and principal-ideal lemmas; no exact theorem or competing definition exists.

No mismatch was found. The worker module already compiles cleanly with only the permitted `sorry` proof,
its declaration signature is copied verbatim into the node's `lean.statement`, and no definition or dependency
module is needed. The source confirms that the unit case is vacuous and that all associated primes have height
one.
