## Worker report

The module `Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions` states
`reduced_normal_iff_integrallyClosed_totalFractions` with a single `sorry` proof.
No definitions, dependency modules, or new nodes are needed. The node is unchanged
except for its `lean` record. The theorem docstring gives all five proof steps with
the supporting DAG nodes; nothing is proved at stage 2.

Hypothesis and clause correspondence:

- A commutative ring R: `(R : Type u) [CommRing R]`, with explicit universe `u`.
- Reduced, with no nonzero nilpotents: `[IsReduced R]`.
- Finitely many minimal prime ideals: `(hfinite : (minimalPrimes R).Finite)`.
  No Noetherian or nontrivial assumption is added.
- S is the nonzerodivisors, and Q(R) is localization at S: Mathlib `FractionRing R`
  unfolds to `Localization (nonZeroDivisors R)` even for rings with zero divisors.
  The specified canonical map is `algebraMap R (FractionRing R)`, which is injective
  by `IsFractionRing.injective R (FractionRing R)` without a domain hypothesis.
  These are specified objects and their automatic property, not extra hypotheses.
- Condition (1), a normal ring: `∀ (p : Ideal R) [p.IsPrime],
  IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
- Condition (2): `IsIntegrallyClosedIn R (FractionRing R)`.
  `isIntegrallyClosedIn_iff` expresses exactly injectivity together with
  `∀ {x}, IsIntegral R x → ∃ r, algebraMap R (FractionRing R) r = x`.
- Condition (3): `∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
  (∀ i : Fin n, IsDomain (A i) ∧ IsIntegrallyClosed (A i)) ∧
  Nonempty (R ≃+* (∀ i : Fin n, A i))`.
  Bundled rings supply precisely the commutative ring structures for the factors.
  The dependent function type is their finite product, and `Nonempty` requires a
  ring isomorphism. Both normal-domain conditions occur for every factor.
- Equivalence of all three conditions: `(condition1 ↔ condition2) ∧
  (condition2 ↔ condition3)`; this entails every pairwise equivalence.

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `LocalizedModule` in
  `Mathlib.Algebra.Module.LocalizedModule.Basic`. Its ring specialization is the
  same localization quotient: that module's
  `example_localization_eq_localizedModule` checks this reducibly. We use the
  existing ring specialization `FractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing`, imported transitively by
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. A separate module import
  for `LocalizedModule` would be unused.
- `def-weil-pbc-normal-ring`: its `mathlib_match` specifies `IsDomain`,
  `IsIntegrallyClosed`, and `Localization.AtPrime`. Their signatures and docstrings
  were read in `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. The exact inline formula is
  mandated by `coord/brief-stage2.md` and `coord/STATE.md` (NORMAL RING).
- `def-weil-pbc-integral-closure`: `integralClosure`, `IsIntegral`, and
  `IsIntegrallyClosedIn`, in `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`, and
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`. The last renders the
  integral-closedness clause directly, using the former notions internally.

Edge cases checked before writing:

- The zero ring is allowed. It has no prime ideals, normality is vacuous, its total
  fraction ring is again a singleton, and `n = 0` gives an empty product of normal
  domains. No positive-number-of-factors or `Nontrivial R` binder excludes this case.
- A normal domain is the case `n = 1`; its sole factor can be R itself.
- A product of fields with multiple factors is allowed, so no global domain
  hypothesis appears. A reduced non-normal domain fails (1), (2), and (3).
- Finite factors may be chosen in `Type u`: the source proof uses quotients of R.
  Conversely any product decomposition with larger carriers transports its factors
  to these quotient-size carriers. This introduces no mathematical restriction.
- There is no restriction on characteristic, Noetherianity, or Krull dimension.

Source check: the local `literature/stacks-project/algebra.tex` is absent on this
machine, so I read the statement and proof at https://stacks.math.columbia.edu/tag/030C.
They agree with the node's hypotheses and three conditions. No statement fault
or `STATEMENT-DISPUTED` issue was found.

Searches made using `/home/ubuntu/weil-launcher/msearch.py`, with results recorded
in sandbox `searches.jsonl`:

- LeanFinder: "reduced commutative ring with finitely many minimal primes is normal
  iff integrally closed in its total fraction ring iff a finite product of normal
  domains". Eight hits: Dedekind characterizations, scheme integrality and
  normalization, domain-only integral closedness localization, and normal closure.
  No exact statement.
- Loogle: `IsReduced, IsIntegrallyClosed`. Zero hits.
- LeanSearch: "normal reduced ring finite minimal primes finite product integrally
  closed domains". Service unavailable (Internal Server Error), recorded as such.
- Mathlib grep: `normal.*(ring|domain)|minimalPrimes.*[Ff]inite|IsIntegrallyClosedIn`
  in `RingTheory`. Results concern integral closure, minimal-prime finiteness under
  Noetherianity, and normal closures; none states these three equivalences. The
  `IntegrallyClosed.lean` module docstring explicitly says this theorem is missing.
- `rg` of project `lean/Sheaf`, upstream `WeilConjectures`, and
  `dag/lean_names_upstream.json`: patterns `reduced-normal-iff-integrally`,
  `normal.*total`, `isNormal_iff`, `normal_iff`, `finite.*normal` find supporting
  modules `NormalRingIntegrallyClosedTotal` and `FiniteProductNormal`, but neither
  gives the present equivalences. They were read. The upstream item-id search
  has no hit. The intended full declaration name was also searched across these
  sources and Mathlib, with no collision.

Validation: `scompile.py C1 lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`
compiled the module on the server in 1.4 seconds, exit code 0, with no warnings.

## Second reading by C1

I independently opened the item node, its sandbox Lean module, all three
statement-dependency nodes, their Mathlib declarations, and the nearby project
modules. No mathematical or convention mismatch was found. The Lean module and
node record are retained verbatim; this independent reading is the only change.
There are no new definition nodes, dependency modules, or statement corrections
in this delivery, so H12, H13, and the correction-citer check do not apply.

Source reading: `literature/stacks-project/algebra.tex` is not present locally.
I opened the upstream TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `section-conventions`, `definition-domain-normal`,
`definition-ring-normal`, and `lemma-characterize-reduced-ring-normal`, and
checked https://stacks.math.columbia.edu/tag/030C. The conventions explicitly
allow the zero ring and use commutative rings with identity. The lemma requires
only reducedness and finitely many minimal primes, and states exactly the three
conditions in the item. No assumptions on the surrounding section add anything.
The source label agrees; its current line numbering differs from the node's
older line reference, which does not affect the mathematical source place.

Independent object/hypothesis/conclusion list and correspondence (H3):

1. Object: a commutative ring R with identity. Lean: `(R : Type u) [CommRing R]`.
   Verdict: exact, with an explicitly bound arbitrary universe and no domain,
   field, Noetherian, or nontrivial assumption on R.
2. Hypothesis: R has no nonzero nilpotents. Lean: `[IsReduced R]`.
   Verdict: exact; this is reducedness, not a stronger integral-domain condition.
3. Hypothesis: finitely many minimal prime ideals. Lean:
   `(hfinite : (minimalPrimes R).Finite)`. Verdict: exact. I read
   `Ideal/MinimalPrime/Basic.lean`: `minimalPrimes` consists of minimal primes
   over zero, equivalently minimal elements of `Ideal.IsPrime`. Finiteness is
   assumed directly, without deducing it from a stronger Noetherian hypothesis.
4. Specified objects: S is the nonzerodivisors and Q(R) = S^{-1}R, with
   r mapped to r/1 injectively. Lean: `FractionRing R` and its canonical
   `algebraMap R (FractionRing R)`. Verdict: exact. In
   `Localization/FractionRing.lean`, `FractionRing` is explicitly an abbreviation
   for `Localization (nonZeroDivisors R)`, including rings with zero divisors;
   `IsFractionRing.injective` requires no domain or nontrivial instance. The
   canonical objects are fixed by these definitions, rather than new quantified
   arbitrary rings or maps.
5. Conclusion (1): every prime localization is a normal domain. Lean:
   `∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p) ∧
   IsIntegrallyClosed (Localization.AtPrime p)`. Verdict: exact. I read the
   normal-ring dependency's Mathlib match and the mandated inline convention.
   `Localization.AtPrime p` is localization at `p.primeCompl`; `IsDomain`
   includes nontriviality of that localization, as a domain should. The prime
   instance binder quantifies over every prime, and does not assume R is local.
6. Conclusion (2): every integral total fraction is r/1 for some r in R. Lean:
   `IsIntegrallyClosedIn R (FractionRing R)`. Verdict: exact. I read
   `IsIntegral`, `integralClosure`, `IsIntegrallyClosedIn`, and
   `isIntegrallyClosedIn_iff`. They express roots of monic polynomials and
   injectivity together with `∀ {x}, IsIntegral R x →
   ∃ y, algebraMap R (FractionRing R) y = x`. Injectivity is already automatic
   here, so this abbreviation adds no hypothesis or stronger conclusion.
7. Conclusion (3): R is ring-isomorphic to a finite product of normal domains.
   Lean: `∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
   (∀ i : Fin n, IsDomain (A i) ∧ IsIntegrallyClosed (A i)) ∧
   Nonempty (R ≃+* (∀ i : Fin n, A i))`. Verdict: exact. `CommRingCat` bundles
   precisely a carrier and its commutative ring structure. The Pi ring is the
   finite product, and the witness is a ring equivalence, not just a function
   or a module equivalence. Each factor is a domain and integrally closed in
   its fraction field; no factors are required to be fields. The factors and
   isomorphism are existentially quantified inside condition (3).
8. Conclusion: equivalence of all three conditions. Lean:
   `((1) ↔ (2)) ∧ ((2) ↔ (3))`. Verdict: exact; two adjacent biconditionals
   imply every pairwise equivalence, with no directional implication omitted.

Dependency audit (H4): the `LocalizedModule` declaration recorded on
`def-weil-pbc-module-localization` is the same fraction quotient for M = R:
I read `example_localization_eq_localizedModule`, whose reducible equality
identifies it with `Localization S`. Thus the existing ring specialization
used by `FractionRing` is correct and no private definition is present.
For `def-weil-pbc-normal-ring`, I opened `IsDomain`, `IsIntegrallyClosed`, and
`Localization.AtPrime`, as listed in its match. For
`def-weil-pbc-integral-closure`, I opened the recorded `integralClosure` and
its companion `IsIntegral` and `IsIntegrallyClosedIn` declarations in their
actual modules. All imported notions have the right generality; no missing
notion requires a new node or dependency repair.

Edge cases: the zero ring has no prime ideals, so (1) is vacuous. Its total
fraction ring is singleton (`FractionRing.unique`), so (2) holds. The witness
`n = 0` makes the Pi ring a singleton and all factor conditions vacuous, so
(3) covers the same case. There is no `Nonempty (Fin n)` or `n > 0` requirement.
A normal domain fits with `n = 1`; a product of multiple fields fits without
making R a domain. A reduced non-normal domain such as k[t^2,t^3] has finite
minimal primes but fails each condition, as it should. No characteristic,
Krull-dimension, or finiteness of the underlying ring is imposed. Arbitrary
finite index sets may be reindexed by `Fin n`. Restricting factor carriers to
`Type u` loses no decompositions: after any ring-product isomorphism, each
factor is a quotient of R by the kernel of its coordinate projection, and
therefore has a carrier in the universe of R. Schemes and empty schemes are
not objects of this ring statement.

Independent searches (different queries from the worker; recorded by msearch):

- LeanFinder: `finite minimal spectrum reduced ring splits into integrally
  closed domains via total quotient ring`. Eight hits, including
  `instFiniteMaximalSpectrumOfIsFractionRing`, `isDedekindRing_iff`,
  `isDedekindDomain_iff`, and `PrimeSpectrum.finite_setOf_isMin`. Their displayed
  signatures have stronger Noetherian/dimension/domain hypotheses or different
  conclusions; none gives this three-condition equivalence.
- Loogle: `IsIntegrallyClosedIn, FractionRing, IsDomain`. No hits.
- LeanSearch: `semilocal total quotient ring of a reduced ring normal iff finite
  product of integrally closed integral domains`. The service returned Internal
  Server Error; this search is unavailable, not a negative mathematical result.
- `rg` across Mathlib RingTheory, upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json` for `030C`,
  `total (quotient|fraction)`, `finite.*[Pp]roduct.*[Nn]ormal`,
  `integrallyClosed.*minimal`, `minimal.*integrallyClosed`, and the proposed
  declaration name. No existing full statement or name collision was found.
  I opened `NormalRingIntegrallyClosedTotal.lean`, `FiniteProductNormal.lean`,
  and `TotalQuotientRingMinimalProduct.lean`: respectively they give only
  (1) implies (2), product normality, and a total-fractions decomposition with
  a weak-association hypothesis. None substitutes for this theorem.
  Mathlib's `IntegrallyClosed.lean` mentions Tag 030C in prose, not a declaration.

H5/H6/H8/H9: there is one named theorem with proof `by sorry`, and no definitions
or extra proved statements. Both docstrings name Tag 030C and the item blueprint.
I matched the declaration docstring's five steps to the node's five proof steps:
minimal-prime total-fractions decomposition, normality implying integral
closedness, integral coordinate idempotents splitting R, normality of the
factors by coordinatewise integral closure, and finite-product normality.
The supporting nodes are named at the appropriate steps. Imports supply the
bundled factor rings, minimal-prime set, integral-closedness notion and prime
localizations. The declaration is in the root namespace without a Sheaf prefix;
all variables, the universe u, primes, factors, and indices are bound. The
node's `lean.statement` is verbatim the signature in the file.

No mismatches were found; no Lean or node change was needed. Validation uses
`scompile.py` on the sandbox module and `deliver2.py --no-push` before delivery.
