## Worker report

Files written (under dag/nodes/sec-proper-base-change/):
- lem-weil-pbc-weak-etale-field.json: item, seven-step split; statement unchanged.
- lem-weil-pbc-weakly-etale-field-separable.json: statement only, exact closed project attachment; not a Mathlib match.
- lem-weil-pbc-injective-minimal-prime-lift.json: statement only, Mathlib leaf Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective, Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean:109-114.

Attachments:
Algebra.WeaklyEtale.isAlgebraic belongs to lem-weil-pbc-weakly-etale-field-separable, WeilConjectures/RingTheory/ProEtale/WeaklyEtaleField.lean:94. Its result is Algebra.IsSeparable, which includes algebraicity; its source proof has no sorry and the 7d675a26 sorry-map record has s=false and ts=false. I seeded the exact declaration in the new node's lean_audit for maintainer verification.

No WANTED documents. All Stacks sources used are present.

The imported statement is correct. The imported proof omitted citations for the flat quotient equation, localization stability, minimal-prime lifting, finite-dimensionality, and finite reduced algebra decomposition. Its claim that each field factor embeds into a B_q needed a proof of lifting a prime and of the localization kernel; the new steps supply both. The field-extension paragraph compressed faithfully-flat descent and inseparability into uncited claims. I use the existing closed field-extension theorem in a properly separate statement-only node, rather than reproduce its unrecorded supporting facts. The final finite-subalgebra argument follows the actual Stacks 092Q minimal-prime route; this is a permitted change below the unit level, not a change in the proper-base-change unit route.

Source searches under WeilConjectures/ found no blueprint tag declaration of the whole item. Algebra.WeaklyEtale.etale_of_fg at WeaklyEtaleField.lean:176 states etaleness but does not itself state the item’s module-finiteness, reducedness and residue-field clauses. indEtale_field and isSeparable_residueField cover other clauses. These are useful evidence, not an exact full attachment under the brief’s rule. No upstream-master sorry is treated as a proof. No Lean file, compiler or Lake command was used.

No unfinished mathematical step remains in the item. The smaller field-extension node is delivered without proof because an exact project proof already exists. All new-node searches were run through msearch.py and recorded from searches.jsonl; LeanSearch returned Internal Server Error and is recorded unavailable. Mathlib's FormallyUnramified.isSeparable requires EssFiniteType and does not directly cover the arbitrary field-extension lemma. The minimal-prime lift is an exact one-line specialization from commutative semirings to commutative rings. The Artinian product searches led to existing DAG tools, so no product-decomposition node was created.

## Not duplicates

Neither new node shares a source tag with an existing nonmerged node: whole-DAG searches for 092P and 00FK and blueprint_refs searches returned no such statement. Keyword and declaration searches were also made across the DAG, blueprint and project source. lem-weil-pbc-injective-minimal-prime-lift differs from lem-pc-dense-range-comap-minimal-primes: the latter is an equivalence with dense range, not the implication from injectivity. The field-extension node is strictly smaller than the item: it only treats a field target and does not prove any finite-subalgebra, reducedness, or general-ring residue-field assertion. The remaining steps prove these assertions, so the split does not merely move the conclusion to a new node.

## Review by NC

I read the master blueprint statement and all three proof paragraphs, the proper-base-change chapter and unit records, and Stacks more-algebra.tex Tags 092Q (lemma-absolutely-flat-over-field), 092P (lemma-absolutely-flat-fields), 092F (lemma-absolutely-flat), and the flat-diagonal discussion including 092K and 092M. I read algebra.tex Tag 00FK (lemma-injective-minimal-primes-in-image), Tag 00KJ (proposition-dimension-zero-ring), and Tag 00U3 (lemma-etale-over-field). The item retains arbitrary commutative weakly etale k-algebras, with no finite type assumption on B. The new field-extension statement agrees with 092P specialized to weak etaleness and with the project declaration, including arbitrary extension degree. The new minimal-prime lift agrees exactly with 00FK and the Mathlib declaration read at lines 109-114. Both new statements introduce their objects and cite the definitions they need; neither has proof steps or a proof hidden in its statement.

Step 1 takes precisely the common-flat-resolution-bound conclusion from weak-etale-tor (not just the Tor formula), the weak etaleness of arbitrary localizations from localization-ring-weakly-etale, and weak-etale composition from ind-etale-stability. The zero bound over a field follows from a vector-space basis, with coordinatewise tensor injectivity. All the maps here are commutative k-algebra maps; the source of a localization need not be finite type.

Step 2 uses the full flat quotient element equation, with J=(b), and the actual local-ring/maximal-ideal assertion of localization-at-prime. Since b is a nonunit, e in (b) lies in the maximal ideal and 1-e is a unit. This proves the local ring is a field without assuming that its quotient is free or that b is regular. It also identifies the residue field because its maximal ideal is zero. This step is elementary once those two statements are supplied.

Step 3 uses the fraction equality from localization-at-prime to detect vanishing, and minimal-prime-over-proper-ideal only to obtain a prime containing a proper annihilator. This writes out why local vanishing implies global vanishing, rather than silently invoking a sheaf or support theorem. The new field-extension statement applies because steps 1-2 give exactly its field and weak-etale hypotheses. There is no invocation of the general-ring residue-field result being proved.

Step 4 applies minimal-prime-lift to the injective subalgebra inclusion. The localization kernel is checked in both directions using the zero maximal ideal and primeness, giving an embedding of A/p. Its field property is established by a polynomial inverse calculation for each nonzero element. The separability inference is justified by equality of the kernels of k[T] evaluation before and after the embedding; hence the monic minimal polynomials agree. No arbitrary prime of A is presumed to lift to B.

Step 5 uses finite-type-algebra-noetherian only after checking that a field is Noetherian and that A is finitely generated. The noetherian-minimal-prime node gives finiteness of minimal primes; prime-contains-minimal-prime and their proved maximality show these are all primes. Only then is the finite-spectrum hypothesis of pqf-lem-finite-type-algebra-finite-spectrum available. Its statement explicitly gives finite-dimensionality, which is what is used, not a proof detail of that node.

Step 6 uses the complete statement of reduced-noetherian-total-ring-fractions: it supplies the actual product isomorphism and the prime-localization fields. The avoidance statement of minimal-prime-avoids-nonzerodivisor and the existence statement of minimal-prime-over-proper-ideal prove every fraction denominator is already a unit. Thus Q(A)=A is justified with no unproved Artinian decomposition invoked. The quotient-to-localization identification is written out; step 4 gives separability of the quotient fields, and step 5 gives their finite dimension because they are quotients. The finite-etale-algebra-criterion node states exactly that a finite product of finite separable field extensions is finite etale. Its group-scheme clause is not used. The off-unit generic tools are declared in split_report.tool_uses, with their roles; none substitutes for a step of the unit route.

Step 7 uses exactly the filtered-colimit definition in ind-etale-algebra. The index is the set of finitely generated subalgebras of B, so smallness in a common universe is automatic. Directedness, the union, and the universal property are explicitly verified. Finite etale terms are in particular etale of finite presentation in the conventions already used by that definition. There is no need for an additional filtered-colimit existence or descent lemma.

I tested the zero algebra (empty spectrum, empty product, singleton subalgebra diagram), k itself, a finite separable field extension, a finite product of such fields, and an infinite separable algebraic field extension. The last case confirms no finite extension hypothesis can be added to B. The local argument excludes nonzero nilpotents; a nontrivial purely inseparable finite extension fails the flat-diagonal hypothesis, so the new field-extension statement does not overreach. In step 4 only minimal primes are lifted, which avoids the false assertion that every prime lifts along an injection. The source statement needs no correction and no STATEMENT-DISPUTED mark.

The B-to-E checks corrected the uncited inputs and the unjustified field-factor embedding described above. I kept both new nodes statement-only, avoided new elementary nodes, checked every cited statement in full, and put verbatim statements in citations.json for every step citation. Imported metadata and the unit/chapter records are unchanged. There is no circular use of the item or of a residue-field theorem depending on it.

## Second reading by NC

I reread Stacks Tag 092Q (lemma-absolutely-flat-over-field) in `more-algebra.tex`, including its hypotheses and the finite-subalgebra conclusion, and Tag 092P (lemma-absolutely-flat-fields); the item statement agrees clause by clause, including arbitrary (possibly zero) algebras and no finite-type hypothesis on `B`.

Step 1 was checked against the full common-bound conclusion of `lem-weil-pbc-weak-etale-tor`, localization weak etaleness, and composition stability; the zero flat-resolution bound over a field is elementary.

Step 2 was checked against the localization-at-prime definition and flat-quotient element equation; the nonunit argument correctly uses the local maximal ideal and is elementary from those statements.

Step 3 was checked against the localization fraction criterion, minimal-prime-over-proper-ideal, and the field-extension attachment; the annihilator argument and residue-field application have all required hypotheses.

Step 4 was checked against Stacks Tag 00FK and the new minimal-prime-lift Mathlib leaf; only minimal primes are lifted, and the localization kernel and separability arguments are explicitly supplied.

Step 5 was checked against the noetherian finite-type, finite-minimal-prime, prime-contains-minimal-prime, and finite-spectrum criteria; finite spectrum is established before invoking finite dimensionality.

Step 6 was checked against the reduced Noetherian total-ring-of-fractions decomposition, nonzerodivisor avoidance, proper-ideal prime existence, and finite-etale criterion; denominators, quotient-localization maps, and finite separable factors are all addressed.

Step 7 was checked against the definition of ind-etale algebra; directedness, union, filtered-colimit universal property, and the zero-algebra edge case are stated.

The field-extension node was checked against Tag 092P and the closed `Algebra.WeaklyEtale.isAlgebraic` declaration in `WeaklyEtaleField.lean:94`; the minimal-prime node was checked against Tag 00FK and `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` at lines 109–114. Both remain statement-only/Mathlib-leaf nodes with self-contained hypotheses and recorded searches. I found no statement, citation, duplication, cycle, source, or edge-case defect, so no further file changes were necessary in this second reading.
