## Worker report

Module: `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`.
Declaration: `Ideal.associatedPrimes_fractionalPrincipalQuotient`.
This delivery states the node, with `sorry` as the only theorem proof. No new
notion, new node, dependency module, or statement correction is needed.

Hypothesis and clause correspondence:

- The commutative ring A is `(A : Type u) [CommRing A]`.
- Noetherian is `[IsNoetherianRing A]`.
- Normal integral domain is `[IsDomain A] [IsIntegrallyClosed A]`, precisely
  the domain clause of def-weil-pbc-normal-ring, not an extra general-ring normality predicate.
- The fraction field is `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`.
  The universes of A and K are explicitly bound and independent; there is no
  quantification over test algebras that could become vacuous.
- The nonzero fraction is `(y : K) (hy : y ≠ 0)`.
- `J = A ∩ yA` is constructed, without any hypothesis or postponed data, by
  `let J : Ideal A := (Submodule.span A ({y} : Set K)).comap (Algebra.linearMap A K)`.
  `Ideal A` is Mathlib's abbreviation for `Submodule A A`. Membership means that
  the image of a in K is in the A-span of y. By `Submodule.mem_span_singleton`, this
  means `∃ b : A, b • y = algebraMap A K a`, equivalently
  `∃ b : A, algebraMap A K a = y * algebraMap A K b` by commutativity and symmetry.
  This is exactly the set in the node, including fractions outside A.
- An arbitrary associated prime is quantified by
  `∀ p ∈ associatedPrimes A (A ⧸ J), ...`. Mathlib's definition initially uses a
  radical annihilator, but `isAssociatedPrime_iff` under the stated Noetherian
  hypothesis identifies it with a prime annihilator of an element. Such an
  element is necessarily nonzero: the zero element's annihilator is the whole
  ring, which is not prime. Thus this is exactly the node's convention.
- No embedded associated primes is `p ∈ J.minimalPrimes`: by
  `Ideal.IsMinimalPrime`, p is prime, contains J, and is minimal among such primes.
- Height one is `p.height = 1`. For a prime, Mathlib height is the supremum of
  lengths of strict chains of primes below it, so in a domain this is equivalent
  to the node's `(0) < p` with no longer chain ending at p. The two conclusions
  appear together as a conjunction for every associated prime.

Recorded statement dependencies, read in full at their source declarations:

- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its docstring and `isNoetherianRing_iff_ideal_fg` give every
  ideal finitely generated. Available through the associated-prime/height imports.
- def-weil-pbc-normal-ring: its mathlib_match gives `IsDomain`,
  `IsIntegrallyClosed`, and `Localization.AtPrime`. The statement uses its normal
  domain clause, so the latter localization construction is not needed here.
  `IsIntegrallyClosed` is read from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`; it means integral closure
  in `FractionRing A` and applies equally to any chosen fraction field.
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim` defines chain dimension. Its prime-chain notion is used through
  Mathlib's `Ideal.height` in `Mathlib.RingTheory.Ideal.Height`; that file's
  `Ideal.primeHeight` docstring and definition give the precise chain meaning.

Other existing Mathlib notions used: `associatedPrimes`, `isAssociatedPrime_iff`
from `Mathlib.RingTheory.Ideal.AssociatedPrime.Basic`; `Ideal.minimalPrimes` and
`Ideal.IsMinimalPrime` from `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`;
`Submodule.span`, `Submodule.comap`, and `Algebra.linearMap` for J. The project
module `Sheaf.RingTheory.AnnihilatorAssociatedPrimes` was also read; its definition
is not needed because the Noetherian equivalence already gives exactly the
required associated primes without defining anything again.

Source verification: the local `literature/stacks-project/algebra.tex` is absent
on this machine, so I read the authoritative
[Stacks Tag 031T](https://stacks.math.columbia.edu/tag/031T), Lemma 10.157.6,
clause (3). It agrees with the node. The declaration docstring includes every
step of the node's alternative direct proof: write y=a/b; identify J by
bc ∈ aA; inject A/J into A/aA preserving annihilators; apply
lem-weil-pbc-normal-domain-principal-quotient-associated-height; deduce minimality
by excluding the chain (0)<q<p. This is the node's agent-written proof, not a
claim that Stacks uses that identical route.

Edge cases checked before writing:

- y=1 or y an A-unit: J=A, quotient zero, and the associated-prime set is empty.
- A a field, with any nonzero y in K: again J=A and the assertions are vacuous.
- A=ℤ, K=ℚ, y=2/3: J=2ℤ, whose only associated prime is (2), minimal and height one.
- A=ℤ, y=1/2: J=ℤ although y is not integral; no properness assumption is added.
- y=0 would give J=0 and associated prime (0) of height zero; it is correctly
  excluded by hy, exactly as in the node.
- The zero ring is excluded by IsDomain, matching integral domain in the node.
- No characteristic, positivity of dimension, finite-dimensionality, locality,
  Dedekind-domain assumption, or universe restriction is introduced.

Searches actually run (msearch log is searches.jsonl):

- LeanFinder: "In a Noetherian integrally closed domain the quotient by the
  intersection with a nonzero principal fractional ideal has associated primes
  minimal of height one". Eight hits concern Dedekind factorization or
  `Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing`; none state this result.
- Loogle: "Ideal.associatedPrimes, Ideal.height". No hits; it reports unknown
  identifier Ideal.associatedPrimes (the actual module-level name is associatedPrimes).
- LeanSearch: "associated primes of quotient by intersection principal fractional
  ideal in a Noetherian normal domain are minimal and height one". The service
  returned Internal Server Error; recorded as unavailable, not as a negative result.
- Mathlib grep via msearch: "fractional.*principal|associatedPrimes|IsAssociatedPrime"
  in RingTheory/Ideal. Fifteen hits locate the standard associated-prime APIs and
  localization/finiteness lemmas; none gives this statement.
- Direct rg of Mathlib/RingTheory for fractional/principal and normal/associated
  combinations finds fractional-ideal operations and factorization, no matching theorem.
- Direct rg of WeilConjectures and lean/Sheaf for the node id and fractional
  principal/quotient names finds only citations in other modules, no statement.
- Direct rg of WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  associatedPrimes/height combinations and the chosen declaration name finds no
  existing declaration with this statement or name.

Validation: scompile.py on the exact delivery module returned exit code 0,
compiled in 1.3 seconds, with no warnings. No proofs have been supplied.

## Second reading by F1

I independently read the sandbox node and module, all three statement dependency
nodes and their Mathlib declarations, and the source lemma and proof. The local
Stacks .tex is absent. I read Tag 031T on the Stacks site and fetched upstream
`algebra.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
locating `lemma-normal-domain-intersection-localizations-height-1`. Its opening
hypotheses are exactly Noetherian normal domain and fraction field; clause (3)
adds a nonzero fraction and asserts both absence of embedded primes and height
one. There is no additional standing hypothesis. No statement correction,
new definition node, or dependency module is present or needed.

Object/hypothesis/conclusion checklist (each verdict is exact):

1. Commutative ring A: `(A : Type u) [CommRing A]`. The source's domain is
   commutative, and no locality or finite dimension is assumed.
2. Noetherian: `[IsNoetherianRing A]`. I opened Noetherian/Defs.lean: the
   abbreviation is `IsNoetherian A A`, and `isNoetherianRing_iff_ideal_fg`
   identifies it with every ideal finitely generated, as its dependency says.
3. Normal integral domain: `[IsDomain A] [IsIntegrallyClosed A]`. I opened
   IntegralClosure/IntegrallyClosed.lean: this is integral closure in
   `FractionRing A`, precisely the domain clause of def-weil-pbc-normal-ring.
   The general-ring localization clause of that node is not needed here.
4. Fraction field K: `(K : Type v) [Field K] [Algebra A K]
   [IsFractionRing A K]`. This specifies the inclusion and fraction-field
   property; it does not replace A by a field or impose a finite extension.
5. Nonzero fraction: `(y : K) (hy : y ≠ 0)`. No integrality, membership in A,
   nonunit, or properness condition has been added.
6. Intersection ideal J: `let J : Ideal A := (Submodule.span A ({y} : Set K)).comap
   (Algebra.linearMap A K)`. I opened Submodule/Map.lean, Span/Defs.lean and
   Algebra/Defs.lean. Comap is inverse image; the algebra linear map is the
   algebraMap; singleton span membership is `∃ b : A, b • y = algebraMap A K a`.
   Since the algebra action is multiplication, commutativity and symmetry give
   `algebraMap A K a = y * algebraMap A K b`. This is exactly the node's
   A-intersection-yA, using existing constructions rather than a private notion.
7. Quotient: `A ⧸ J` with its canonical A-module structure is the node's A/J.
8. Associated prime convention and quantifier: `∀ p ∈ associatedPrimes A (A ⧸ J)`.
   I opened AssociatedPrime/Basic.lean, including the definitions and
   `isAssociatedPrime_iff`. Under the already required Noetherian assumption,
   membership means p prime and p equal to the annihilator of some quotient
   element. The element cannot be zero, whose annihilator is the unit ideal.
   Thus it is exactly the node's prime annihilator of a nonzero class.
   The project's AnnihilatorAssociatedPrimes.lean defines the arbitrary-ring
   convention without radicals; here the established Noetherian equivalence
   makes the Mathlib notion exact, without duplicating that definition.
9. No embedded associated primes: `p ∈ J.minimalPrimes`. I opened
   MinimalPrime/Basic.lean: this is `Minimal (fun q => q.IsPrime ∧ J ≤ q) p`.
   It is minimality among ALL primes containing J, as requested.
10. Every such associated prime has height one: `p.height = 1`, conjoined to
    item 9 under the same universal quantifier. I opened Ideal/Height.lean:
    for prime ideals its height is Order.height on PrimeSpectrum; its
    definition is the supremum of lengths of prime chains below p. I also
    opened KrullDimension/Basic.lean for the dependency's `ringKrullDim`.
    In a domain height one is precisely a chain (0)<p and no longer chain
    ending at p. No independent height hypothesis or extra prime binder exists.

Edge cases: y=1 and any A-unit give J=A and the zero quotient, whose
associated-prime set is empty (also checked the Mathlib subsingleton lemma).
A a field gives the same vacuity for every nonzero y. For A=Z and K=Q,
y=2/3 gives J=2Z whereas y=1/2 gives J=Z; both are covered. Excluding y=0
is necessary and matches the source: it would give J=0 with height-zero
associated prime (0). The zero ring is excluded exactly by integral domain.
Both universes u and v are explicitly bound and independent; there is no
small-universe test-object quantifier. There are no index sets, schemes, n,
or characteristic restrictions to check, and no positive-dimension assumption.

Independent searches (also logged by msearch): LeanFinder query "associated
prime of quotient by colon ideal in an integrally closed Noetherian domain
has height one" found eight nearby height bounds/Dedekind results, none this
statement. Loogle query `associatedPrimes, IsIntegrallyClosed` returned zero
hits. LeanSearch query "Associated primes of a colon principal ideal quotient
in a Noetherian normal domain have height one" returned Internal Server Error;
this service is unavailable, not a negative search result. Direct rg used
`fractionalPrincipalQuotient|fractional.*[Qq]uotient|[Ii]ntersection.*associated|
associated.*[Ii]ntersection` across Mathlib/RingTheory, WeilConjectures,
lean/Sheaf and dag/lean_names_upstream.json; only citations were found. I also
searched `associatedPrimes|IsAssociatedPrime` across all WeilConjectures and
lean/Sheaf and Mathlib's IntegralClosure, FractionalIdeal and Ideal/Colon.lean.
The neighboring project statements concern depth, removal of embedded primes,
power quotients and criteria; none states the present result. No existing
matching theorem or declaration-name collision was found.

H5/H6/H8/H9 review: the only declaration is a theorem with proof `by sorry`;
the ideal is constructed from actual Mathlib data. Both docstrings name 031T
and the exact blueprint id. The proof docstring matches each of the node's
four steps: numerator/denominator and membership; injective multiplication map
and annihilator equality; principal-quotient height theorem; minimality via
(0)<q<p and the zero quotient. All imports supply notions used in the signature,
all lines are within 100 characters, and all parameters/universes are bound.
The node's `lean.statement` is verbatim the signature before `:= by`.

Mismatches found: none. Changes: appended this independent second reading;
retained the correct Lean module and node record unchanged. Independent
scompile.py validation of the exact delivery module completed in 1.4 seconds,
exit code 0, with no warnings.
