## Worker report

The module `Sheaf.RingTheory.QuotientLiftFinitePrimeAvoidance` states
`Ideal.exists_quotient_representative_notMem_primes`, with `sorry` as its entire proof.
It adds no definitions, auxiliary theorems, new nodes, or dependency repairs. The node is
unchanged except for its `lean` field. Its source is Stacks Project, Varieties, Tag 09NK,
`lemma-extra-silly`, read in `literature/stacks-project/varieties.tex:9060–9081`.
The declaration docstring gives all five proof steps from the DAG, including the explicit
intersection-ideal witnesses and the use of prime avoidance.

Hypothesis and conclusion correspondence:

- A commutative ring with identity is `{A : Type u} [CommRing A]`, with `universe u`
  explicitly declared. There is no nonzero, domain, Noetherian, or characteristic assumption.
- The ideal is `(I : Ideal A)`. This is Mathlib's existing ideal, whose additive and
  scalar-multiplication closure render the node's explanatory definition.
- The list of `r ≥ 0` prime ideals is `{r : ℕ}` and
  `(p : Fin r → AlgebraicGeometry.Spec (CommRingCat.of A))`. This explicitly uses the
  recorded `def-weil-affine-spectrum` declaration. Its underlying type is definitionally
  `PrimeSpectrum A`; each `(p i).asIdeal` is the corresponding ideal, and
  `PrimeSpectrum.isPrime` supplies properness and the prime product implication.
  A family indexed by `Fin r` is just the node's finite list, with index `i` representing
  the human index `i + 1`. There are no distinctness or incomparability hypotheses.
- The hypothesis `I` is not contained in each listed prime is
  `(hI : ∀ i : Fin r, ¬ I ≤ (p i).asIdeal)`. Ideal order is inclusion.
- The arbitrary residue class is `(fbar : A ⧸ I)`. Mathlib's quotient is the quotient
  by the submodule/additive subgroup of the actual ideal, not an unrelated quotient.
- The asserted lift is `∃ f : A`.
- The clause `f + I = fbar` is `Ideal.Quotient.mk I f = fbar`.
- The clause excluding every listed prime is `∀ i : Fin r, f ∉ (p i).asIdeal`.
  These are exactly the two conjuncts of the conclusion.
- The stated permission for repeated/comparable primes is expressed by the unrestricted
  function `p`; the permission for the empty family is `r = 0`; the permission for the
  zero ring is the absence of a `Nontrivial A` binder.

Dependency declarations read and used:

- Statement dependency `def-weil-affine-spectrum` records `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme`, publicly imported and used directly in the type of
  `p`. Its full definition and the docstring of `Spec.map` were read at lines 469–480.
  No spectrum or prime-ideal definition is copied. The underlying prime-ideal structure
  and `PrimeSpectrum.asIdeal`/`PrimeSpectrum.isPrime` were read in
  `Mathlib.RingTheory.Spectrum.Prime.Defs:27–39`.
- Mathlib's `Ideal.instHasQuotient` and `Ideal.Quotient.mk` in
  `Mathlib.RingTheory.Ideal.Quotient.Defs` supply the quotient and canonical quotient map;
  this module is publicly imported because the conclusion uses it. Its definitions and
  docstrings were read at lines 41–88.
- Proof dependency `lem-weil-pbc-prime-avoidance` records the exact Mathlib match
  `Ideal.subset_union_prime` in `Mathlib.RingTheory.Ideal.Operations`. Its docstring and
  full signature were read at lines 1159–1165. The module is imported privately for the
  planned proof, as required; it is not restated.

Edge cases checked mathematically before drafting:

- For `r = 0`, the hypothesis and avoidance clause are empty universal quantifiers;
  the assertion is ordinary surjectivity of the quotient map.
- The zero ring has no prime ideals, so only the empty-family case has data. Its unique
  quotient class has the unique ring element as a representative.
- For `I = ⊤`, the quotient is the zero ring and `f = 1` avoids every proper prime ideal.
- For `I = ⊥` and a nonempty family, the noncontainment hypothesis cannot hold. For
  the empty family, arbitrary quotient classes still have representatives.
- Repeated primes impose repeated identical conditions. Comparable primes are allowed;
  avoiding the largest of a finite inclusion chain avoids its smaller members.
- No assumption forces pairwise coprimality. For example a proper inclusion between two
  prime ideals is permitted whenever the same ideal `I` is not contained in the larger one.
- No universe restriction is introduced: `A` is in any explicit universe `u`, its quotient
  is in that universe, and the list is finite. There is no quantified test object that
  could make a hypothesis vacuous through a smaller universe.

Searches (2026-10-24, `msearch.py Q57 lem-trf-quotient-lift-finite-prime-avoidance`):

- LeanFinder: `Every residue class modulo an ideal I has a representative outside finitely
  many prime ideals none of which contains I`. Eight hits, including
  `IsDedekindDomain.exists_representative_mod_finset`,
  `IsDedekindDomain.exists_forall_sub_mem_ideal`, and
  `Ideal.exists_forall_sub_mem_ideal`. The first two require a Dedekind domain and distinct
  primes; the last is the pairwise-coprime Chinese remainder theorem. None is this statement.
- Loogle: `Ideal.Quotient.mk, Ideal.IsPrime`. Twelve hits about prime ideals under quotient
  maps, primes over ideals and residue fields, with no coset-avoidance theorem.
- LeanSearch: `Every coset of an ideal not contained in any of finitely many prime ideals
  contains an element outside all of the primes`. Eight hits, including
  `Ideal.subset_union_prime`, its finite and primed variants, and
  `Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver`. Ordinary prime avoidance selects an
  element inside an ideal, rather than inside a prescribed coset. The lies-over result
  requires an essentially finite type quasi-finite algebra. No exact match.
- Mathlib grep: `(avoid|[Ll]ift|coset).*(prime|Prime)|(prime|Prime).*(avoid|[Ll]ift|coset)`
  in `RingTheory`. Twenty-five hits, including the ordinary prime-avoidance lemmas and
  residue-field lifts, with no matching coset assertion. Read the relevant signatures in
  `Ideal/Operations.lean`, `DedekindDomain/Ideal/Lemmas.lean:963–979`,
  `Ideal/Quotient/Operations.lean:255–272`, and `QuasiFinite/Basic.lean:519–524`.
- Project and upstream `rg -n` with the same regex in `lean/WeilConjectures` and
  `lean/Sheaf` returned numerous unrelated lifting lemmas. The potentially relevant
  `PrimeSpectrum.exists_basicOpen_le_of_finite` in upstream
  `Mathlib/AlgebraicGeometry/AffineScheme.lean:300–318` was read: it finds a basic open
  containing a finite set of points and has no prescribed quotient class.
- More focused project/upstream searches used
  `coset.*prime|prime.*coset|residue class.*avoid|quotient.*avoid|representative.*prime`
  and the ring-theory pattern `quotient.*(avoid|representative)|coset.*prime|09NK`.
  The hits concerned unrelated quotient representatives and constructions.
- `grep -rn 'lem-trf-quotient-lift-finite-prime-avoidance' lean/WeilConjectures`, and
  `rg -n 'exists_quotient_representative_notMem_primes|09NK|lemma-extra-silly'` on
  upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no existing declaration
  with the node, source label, or proposed name.

Validation: the prescribed `scompile.py` compiled the delivered file both as the isolated
sandbox module and under `Sheaf.RingTheory.QuotientLiftFinitePrimeAvoidance`, within the
60-second limit (1.3 seconds and 1.4 seconds respectively), with no errors or warnings.
Every variable and universe is explicitly bound. No statement dispute or node fault found.

## Second reading by Q57

A second pass by the same dispatcher-started worker reread the node, its five proof steps,
the Stacks source, and the complete Lean signature. The ring binder includes the zero ring;
`I` is precisely the given ideal; `Fin r` includes the empty list; the points of the recorded
`Spec` are definitionally the required prime ideals. The noncontainment direction is
`¬ I ≤ (p i).asIdeal`, not its reverse. `fbar` ranges over every element of `A ⧸ I` and the
existential element is in `A`; the quotient-map equality and universal nonmembership are
both present. No injectivity, incomparability, properness of `I`, or pairwise-coprimality
restriction was introduced. No mismatch was found and no statement correction was made.
This is a self-check; the maintainer supplies the independent review specified in the brief.
