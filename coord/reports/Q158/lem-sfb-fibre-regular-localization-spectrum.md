# Worker report: lem-sfb-fibre-regular-localization-spectrum

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibre-regular-localization-spectrum.json: statement, split into seven steps; no exact Mathlib match for the whole statement. The statement and all five statement dependencies are unchanged.
- citations.json: nine verbatim statement quotations, one for each cited node in each step.
- searches.jsonl: six actual searches recorded by msearch.py; the six corresponding entries were appended to the item's prior search records without replacing them.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: lem-weil-pbc-noetherian-associated-primes-finite (00LC), lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes (00LD), lem-weil-pbc-prime-avoidance (00DS), and lem-weil-pbc-localization-spectrum-embedding (00E3).

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, homothety-spectrum, associatedPrimes, semilocal and localization vocabulary. The project declarations about depth, regular elements, associated primes under flat base change and semilocal normalization do not state the item. No sorry-containing declaration was treated as finished evidence.

## Wanted literature

None. All mathematical sources used are in literature/stacks-project/.

## Faults and scope

No statement dispute. The item follows Tag 05DE (lemma-homothety-spectrum) faithfully, and its stronger explicit maximal-elements wording is the source's last proof paragraph. The zero-module clause is correct. No hypothesis is changed or added. In particular, B need not be Noetherian, and the map A to B need not be local or flat.

The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor reports None for this item. Its specific from.place and full via list are retained. The inherited unit and chapter records were read, along with the latest blueprint's sk-thm-sf-ctf-stability.proof.md direct-image paragraph; this is a generic algebra subinput of the existing compactification prerequisite chain. Searches of the whole imported blueprint for 05DE and 05BY found zero matches; no blueprint node states this item. The inherited unit record describes an older phrasing of the direct-image route; this delivery changes neither that route nor the unit.

The whole-DAG searches by 00LC, 00LD, 00DS, 00E3, 05BY and associated-prime/localization terminology found the four reused Mathlib leaves. In particular lem-weil-pbc-primes-of-localization gives only prime and principal localizations, so the arbitrary multiplicative-set embedding node is used instead. The quotient-associated-prime comparison is a two-line annihilator calculation, not a new node. The exact proper-ideal argument for maximality is carried in step 6, not hidden in a restated clause.

## Mathlib search assessment

Ran LeanFinder with two phrasings, Loogle with associatedPrimes, IsLocalization, LeanSearch on the spectrum/maximal-associated-prime statement, and two grep searches through RingTheory, exactly as recorded in searches.jsonl and the appended mathlib_searches entries. All six services returned results. Read the hits. The associated-prime localization declarations concern a module after localization, not this scalar-regular localization's semilocal spectrum. The spectrum comap range theorem supplies only the disjoint-primes correspondence (already in the DAG). Read AssociatedPrime/Finiteness.lean:158-183: associatedPrimes.finite is 00LC; Ideal.IsMaximal.mem_associatedPrimes_of_isFractionRing and the finite-maximal-spectrum instance require a Noetherian ring that is its own total fraction ring. Our B need not be Noetherian and Sigma is defined by a module, so these are not one-line specializations. Read LocalProperties/Semilocal.lean:12-81: its finiteness results assume semilocality. Thus the item remains split, not mathlib.

## Review by Q158

I read flat.tex Tag 05DE (lemma-homothety-spectrum), statement and entire proof, and algebra.tex Tags 05BY (lemma-ass-quotient-ring), 00LC (lemma-finite-ass), 00LD (lemma-ass-zero-divisors), 00DS (lemma-silly) and 00E3 (lemma-spec-localization). These are exactly the inputs named by the source proof. I opened the statement of each cited node, rather than relying on its title or proof. There are no new statements to check against another source.

Step 1 uses def-weil-pbc-annihilator-associated-primes, which explicitly defines exact annihilators without a Noetherian assumption. The quotient annihilator formulas show both directions and injectivity of contraction because B to C is surjective. Primality is checked with products of lifts and properness; this is the omitted argument in 05BY, written out here. Multiplicativity of Sigma is composition of the two scalar injections, including the zero module.

Step 2 uses precisely the statement of lem-weil-pbc-noetherian-associated-primes-finite, with R=C and M=Nbar. Both Noetherianity and module finiteness are hypotheses of the item. It does not apply the Noetherian lemma to B. Step 3 similarly applies the zero-divisor-union statement of lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes only over C; the scalar action and step 1 then give the inverse-image complement formula over B. Neither step requires N finite over B.

Step 4 cites lem-weil-pbc-localization-spectrum-embedding for exactly its embedding and disjoint-primes image, and lem-weil-pbc-prime-avoidance for containment of an ideal in one of a finite family of prime ideals. The finite family is supplied by step 2. The avoidance node assumes a nonempty family, so the empty family is treated separately using 0 in every ideal. This avoids an implicit nonzero-module hypothesis.

Step 5 uses def-weil-pbc-module-localization's fraction operations and invertibility of denominators, specialized to the ring as its own module. Multiplication by s/1 and 1/s proves the fraction membership equivalence for any ideal and consequently the inclusion-reflection claim; no separate identification lemma is being assumed.

Step 6 uses the same prime-avoidance statement, now on the contraction K of an arbitrary proper ideal J. K misses Sigma because those images are units, and every fraction in J has numerator in K by step 5. Thus every proper ideal is contained in a prime indexed by Q. This proves both directions of the maximal-ideal classification directly: maximality of J forces equality with that prime, and maximality of q among associated primes forces every proper ideal above its prime to equal it. No unrecorded maximal-ideal-existence theorem or maximal-prime theorem is needed. Finiteness and the final quotient-associated-prime assertion use steps 1 and 2.

Step 7 cites the exact annihilator definition and the fraction definition. On the zero module every annihilator is the whole ring, so no associated prime exists; because 0 is an allowed denominator the fraction relation identifies 1 and 0, and there are no proper ideals. This checks the explicit edge clause without excluding the zero ring localization.

I tested the argument on A=k, B=k, N=k (one associated prime and field localization); N=0 (empty family and zero localization); B=k[x,y], N=B/(x) direct-sum B/(x,y) (comparable associated primes: only (x,y) is maximal); and B=k[x,y]/(xy), N=B (two incomparable minimal associated primes and two localized maximal ideals). The comparable-prime example checks that the statement must select maximal elements of Ass, not claim every associated prime is maximal. For the quotient step I checked B=Z, C=Z/4 and M=C: the annihilator of 2 is (2) in both rings under inverse image. The general proof uses no extra finiteness or flatness assumptions. No statement correction was necessary. All steps are below 2000 characters; the only non-elementary steps cite the precise statement nodes they use. No SGA source is used.

## Not duplicates

No new nodes. The four generic statement inputs are existing DAG nodes, reused without alteration.

## Unfinished work

None in the mathematical split. Required server dry run and push are performed through deliver.py after this report is written.
