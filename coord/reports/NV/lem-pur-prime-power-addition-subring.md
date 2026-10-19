## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-prime-power-addition-subring.json: split, statement unchanged.
- dag/nodes/sec-smooth-purity/lem-pur-prime-power-binomial-divisibility.json: statement, Mathlib leaf, WittVector.map_frobeniusPoly.key₁.
- dag/nodes/sec-smooth-purity/lem-pur-commutative-ring-binomial-expansion.json: statement, Mathlib leaf, add_pow.
- citations.json: verbatim statement citations for steps 2 and 3.

Attachments: none. Searches of WeilConjectures by the item ID, prime-power wording, and power/subring notions found no complete project theorem for the item. The upstream master is reference only. Neither arithmetic leaf is a project attachment; both are Mathlib declarations.

WANTED: none.

The imported item was correct but had no proof. Its existing Mathlib search records correctly rejected the uncontrolled error term in exists_add_pow_prime_pow_eq. I added actual searches through msearch.py, including a second semantic phrasing for the numerical bound. LeanSearch returned Internal Server Error, recorded as unavailable. No statement dispute was found, no new hypothesis was introduced, and no unfinished work remains. The unit has no proof steps, and this auxiliary item does not state the unit, so its realized fields are untouched.

## Not duplicates

lem-pur-prime-power-binomial-divisibility vs lem-pur-prime-power-addition-subring: the new leaf is integer divisibility for one binomial coefficient; the item proves two ring-element memberships from four membership hypotheses and still needs the remainder and monomial argument.
lem-pur-commutative-ring-binomial-expansion vs lem-pur-prime-power-addition-subring: the new leaf is the general finite binomial identity, with no subring and no membership assertion.
lem-pur-prime-power-binomial-divisibility vs lem-pc-homeo-pure-insep: the latter is a homeomorphism of spectra for a purely inseparable field extension, not a numerical divisibility statement.
lem-pur-commutative-ring-binomial-expansion vs lem-pc-homeo-pure-insep: the latter concerns spectra and field extensions, not the binomial expansion in an arbitrary ring.

The DAG was searched for Tag 0545, binomial coefficients, binomial expansion, multiplicity, and the exact Mathlib declarations. The blueprint searches for binomial, binomial theorem, prime power binomial, and multiplicity yielded no matching arithmetic statement. The characteristic-p Frobenius definition only states Frobenius and its iteration, not either general arithmetic leaf. The binomial shift/biproduct and exterior-power nodes concern ranks or derived objects rather than ring identities. The power-generated-spectrum node uses the item, so cannot supply its arithmetic tools.

## Review by NV

I read Algebra Tag 0545, label lemma-help-with-powers, including the entire coefficient argument and its explicit choice a=np^n+mp^m+n+m. The item faithfully evaluates the polynomial assertion in a general commutative ring and unital subring. Positivity of a follows from n,m>0 and prime p>=2. Requiring a>0 does not strengthen the source in a problematic way because its displayed witness is positive.

For the numerical leaf I read Mathlib/RingTheory/WittVector/Frobenius.lean, lines 116–119, where WittVector.map_frobeniusPoly.key₁ has only Fact p.Prime and natural-number arguments. The enclosing ring variable R is absent from its statement. Taking j=k-1 gives precisely the leaf for 0<k<=p^a. Its multiplicity is the largest exponent dividing positive k, not a valuation of a ring element. For the expansion leaf I read Mathlib/Data/Nat/Choose/Sum.lean, lines 75–78: add_pow holds for CommSemiring, so specializes to the underlying commutative semiring of every commutative ring, with the same natural coefficient mapped into the ring. Both nodes have self-contained statements, empty proofs, exact source places, blueprint ancestry, and recorded searches; neither is an elementary new claim invented instead of citing Mathlib, nor a clause of the item's membership conclusion.

Step 1 uses only the defining subring closure and the hypotheses. Its displayed sum proves the prime-multiple membership. I checked a>=n,m and the bounds a-n+1,a-m+1>=B=n(p^n-1)+m(p^m-1). All integer constants are in A because A contains 1 and is closed under finite addition and negatives.

Step 2 cites the expansion leaf's full equality, not a property of Frobenius or a characteristic-p assertion. Its remaining work is division with remainder in the natural numbers and the inequality nr+mr'<=B. The coefficient criterion is discharged, not assumed, in steps 3–4.

Step 3 cites exactly the numerical leaf's divisibility. When r>0, i is positive and p^n does not divide i, so v_p(i)<=n-1. When only r'>0, the same hypotheses hold for j and m. The inequalities then imply p^D divides the coefficient by multiplying p-powers; binomial symmetry follows immediately from the displayed factorial definition. I checked that endpoints i=0,P always have r=r'=0 since a>=n,m. Consequently the numerical leaf is never applied at k=0, and natural subtraction is ordinary subtraction in every nonzero-remainder case. This closes the source's informal 'pick a sufficiently large' instruction with its actual witness.

Step 4 cites no additional theorem: it multiplies out the displayed coefficient factorization to obtain a product of the four assumed subring elements, and adds finitely many such terms. This step is elementary from ring and subring definitions. It does not cancel p, divide in C, or assume C is a domain. I retained the statement-only algebra definition dependency for the structure map convention; no proof step takes an uncited theorem from that definition.

Small cases checked: the zero ring and characteristic-p rings cause no failure, since integer divisibility is established before evaluating in C; x=0 or y=0 is allowed; n=m=1,p=2 gives a=6 and B=2, with the endpoint coefficients needing no positive divisibility. For the numerical leaf a=0 forces k=1 and gives 1|1; k=p^a gives exponent zero; k=1 gives the full p^a divisibility. For the binomial leaf N=0 gives 1=1, including in the zero ring. No new unsplit statement or hidden existence object remains.

The review addressed B1–B10 (self-contained Mathlib leaves, actual searches and declaration lines), C1–C8 (all non-elementary tools cited by their statements, verbatim quotes, no off-unit unsplit tool and no cycle), D1–D5 (the item carries its membership argument rather than moving it to a child), and E1–E7 (all positivity, endpoint, characteristic, and ring hypotheses checked). I corrected no source assertion. I expanded the proof's remainder cases to prevent an implicit valuation at zero or cancellation in a ring with torsion.

Dry-run repairs: the preflight requires a definition citation even for these elementary algebraic notions, so both leaf statements now cite def-weil-pbc-algebra-hom-quotient for the commutative-ring convention (C for the expansion, Z for integer divisibility). I reread that definition: it explicitly introduces commutative rings and ring structure maps, and neither leaf takes a theorem from it. The numerical leaf spells out integer divisibility and its equivalence to natural divisibility for a positive divisor. The required integer mathlib_match.line fields are now 116 and 76, matching the source reads above. Verbatim citation quotes were refreshed. A Python arithmetic check also verified the remainder divisibility for every index with (p,n,m)=(2,1,1),(2,1,2),(3,1,1); these are checks of the numerical formulas, with no Lean run.

## Second reading by NV

- Item statement: read Algebra Tag 0545, `lemma-help-with-powers`, statement and complete proof; substitution into any commutative ring and unital subring gives exactly the imported memberships, and its displayed witness is positive. PASS, unchanged.
- Step 1: checked the witness against Tag 0545 and the inline subring definition; expanded the two lower bounds as positive differences. Integer coefficients need only repeated addition and negatives. PASS, elementary.
- Step 2: opened the expansion node and `add_pow` at Mathlib/Data/Nat/Choose/Sum.lean:75–78; its full equality applies to C without characteristic or domain hypotheses. Remainder division gives nonnegative q,q', the stated bounds, and D<=B. PASS.
- Step 3: opened the divisibility node and WittVector.map_frobeniusPoly.key₁ at Mathlib/RingTheory/WittVector/Frobenius.lean:116–119, with the enclosing Fact p.Prime and notation v=multiplicity at lines 55 and 77; j=k-1 meets j<p^a. Positive remainders imply positive indices and exclude p^n or p^m divisibility. The largest-exponent definition then bounds v; the lower bounds of step 1 give D<=a-v. Symmetry follows from the stated factorial expression; endpoints have zero remainders. PASS.
- Step 4: multiplied the displayed four powers to recover exactly c_i p^D x^i y^j, term by term, and checked each membership against the four hypotheses. The numerical coefficient is nonnegative, so integer divisibility yields a natural c_i. Finite sums and powers follow directly from subring closure. PASS, elementary, no cancellation in C.
- New node lem-pur-prime-power-binomial-divisibility: checked against the numerical coefficient argument of Tag 0545 and the exact Mathlib declaration above. Statement-only, self-contained (valuation, choose and divisibility spelled out), prime and positive-index hypotheses present, natural subtraction specified. Tested a=0,k=1; k=1; and k=p^a. PASS, Mathlib leaf retained.
- New node lem-pur-commutative-ring-binomial-expansion: checked against Tag 0545 expansion and add_pow above; CommSemiring specializes to CommRing, and natural coefficients equal their integer casts. Tested N=0,N=1 and the zero ring. PASS, Mathlib leaf retained.

Independent duplicate checks: searched all dag/nodes for 0545, binomial coefficients/expansion, multiplicity and the declaration names; read def-weil-ring-frobenius and lem-pc-homeo-pure-insep, neither of which states either arithmetic fact. The power-generated-spectrum node uses this item and cannot be used back. `blueprint_refs.py search binomial` returned no imported arithmetic node; `ancestor` returned lem-fin-generic-radicial-smoothing, matching both new records. Project-source searches by item ID and prime-power/addition/subring vocabulary found no finished theorem to attach. The upstream master remains reference material, and no sorry declaration was treated as proved.

I read def-weil-pbc-algebra-hom-quotient: it supplies the ring/algebra structure-map convention used in the statements; it supplies no theorem to a proof step. The elementary subring, integer divisibility, factorial coefficient and valuation meanings are inline. Both new nodes have empty proof and proof_deps and carry tag, label, exact Mathlib lines and the correct blueprint origin. Neither is a clause of the item or a duplicate: the item still needs the explicit exponent, remainder cases, monomial factorization and finite-sum argument.

Small cases for the item: zero ring, A=C, fields of characteristic p, x=0 or y=0 all satisfy the argument; n=m=1 is included. n=0 or m=0 is outside its explicit hypothesis; a=0 is allowed in the numerical leaf and handled above. No schemes occur in these nodes.

Changes: expanded step 1's two arithmetic inequalities; corrected the expansion node's zero-hit Loogle verdict to no match from that query; appended independent semantic and grep searches to both leaf records with their actual outcomes. No statement, citation quote or node count changed. The original worker and Review by NV sections remain intact. Existing created.item metadata was checked and retained: it records the parent split that originally created the item and is preserved by delivery.

Command correction: the brief's trailing dot is rejected by deliver.py's documented parser; use the same group/item and --no-push without that extra argument. No script was changed and no compiler was run.
