# Stage 1 report: lem-trf-split-principal-quotient-normality

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-split-principal-quotient-normality.json`: statement; now split into five proof steps; no Mathlib match for the whole statement.
- `citations.json`: one verbatim statement quote for each of the three step/node citations.
- `report.md`: this report.

There are 0 new nodes and 0 new Mathlib leaves. The proof reuses the existing Mathlib leaf `lem-weil-pbc-fraction-field-lift` and the existing definition leaf `def-weil-pbc-normal-ring`.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact node id, split/normal and retraction/integral-closedness terminology. No project declaration states every clause. The parent log-regular normality theorem does not state this general split-subring theorem.

## Wanted sources

None for this item. The parent's unavailable Kato reference is not needed for this elementary auxiliary descent argument.

## Corrections and provenance

The statement is unchanged and is true without Noetherianity, flatness, a nonzerodivisor assumption on theta, or multiplicativity of rho. The imported node had no proof; its earlier searches and ancestry are retained. Tag 0309 defines normal domains; it does not assert the descent result. Read `literature/stacks-project/algebra.tex`, label `definition-domain-normal` (0309), and the full proof at `lemma-descent-normal` (033G). The latter proves faithfully flat normality descent by sending a fraction a/b to the normal overring and descending a in bS. Here the explicitly given linear retraction proves the necessary principal-ideal contraction. Consequently this is marked agent-origin, and does not cite the faithfully flat theorem as applicable to a merely module-split extension.

Read ILO Expose VI 1.6(i)-(ii), printed p.70 / PDF p.76, for the completed monoid and Cohen hypersurface models motivating the parent. Also read the parent's current split and the current main-20261015 `lem-trf-local-term-locality.md`; the item remains an auxiliary local-algebra ingredient along its recorded ancestry. It is not the key statement of unit sk-i-curve-zero, so no unit record changes.

## Searches and reuse

Before considering new nodes, searched the entire DAG by normal-domain, integrally-closed, retraction, direct-summand, fraction-embedding and fraction-field terminology; searched the imported blueprint with `tools/blueprint_refs.py search` for normal, fraction fields, direct summand, module-split and retraction normal; and ran `ancestor`. No blueprint node states the item. The whole-DAG search found `lem-weil-pbc-fraction-field-lift`, whose statement includes exactly existence, injectivity and the fraction formula required in step 3. Reusing it avoids creating a duplicate tool lemma. No new node was necessary for the polynomial calculation: applying a ring map to a finite sum of powers explicitly writes the entire argument in step 4.

Read all six new search results recorded in searches.jsonl, including the recovered interrupted LeanFinder result; no search was inferred from a failed transport. Reused the original node's prior searches without rerunning them. The second LeanFinder wording found `IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn`. Read its type and `IntegrallyClosed.lean` at that declaration: it assumes IsIntegrallyClosedIn R S. A module splitting does not give this relative condition: a proper algebraic field extension L/k has a k-linear retraction taking 1 to 1, but elements of L integral over k need not belong to k. Thus that declaration does not turn the item into a Mathlib leaf. Loogle's linear-map query yields trace maps assuming integral closedness, not proving the needed descent. Read `FractionRing.lean` lines 340-414 and `IntegrallyClosed.lean` lines 60-130 for the existing leaves and normality definition.

## Not duplicates

No new nodes were created. The sole substantive generic tool needed beyond the definition was already present and was cited instead of duplicated.

## Review by Q123

I checked this split against delivery-errors B-E with the item, the two cited node statements, Stacks 0309/033G and ILO VI 1.6 open. The new-node requirements B are vacuous: there are no new statements or definitions. The item's unchanged statement introduces all rings, maps and scalar-linearity hypotheses and explicitly defines what normal domain means. Its existing ancestry has a precise place and searched same_as=[], and all original fields and searches are retained.

Step 1 uses only the given equalities: from iota(r)=iota(theta)a, applying rho gives r=theta rho(a). The reverse inclusion is the ring-map formula. This verifies contraction even when theta is a zero divisor and makes no multiplicativity assertion about rho. Step 2 checks every representative change for both maps, then computes both linearity and the retraction identity. These are written elementary calculations, not deferred quotient lemmas.

Step 3 cites only `lem-weil-pbc-fraction-field-lift`. I read its entire statement, not its proof: the source must be a domain, the target a field, and the map injective. This step first proves that B is a nonzero domain using the unital injection into the assumed normal domain C. The composite into Frac(C) is then injective, and the cited statement supplies exactly h and h(a/b)=j(a)/j(b). Both denominators remain nonzero. The cited node is a Mathlib leaf, so this off-unit use is a permitted generic tool and does not replace the unit's route.

Step 4 cites `def-weil-pbc-normal-ring`. Its statement says verbatim that every fraction-field root of a monic polynomial lies in the normal domain. The displayed polynomial is obtained by applying h term by term, and remains monic because h preserves 1. Its coefficients j(b_i) are in C. Normality of C therefore applies to this actual element of Frac(C). The equality j(a)=j(b)c is first obtained in Frac(C) and then reflected to C by the canonical domain inclusion; there is no unjustified identification of fraction fields.

Step 5 cites the same definition, now for B. Applying p to j(a)=j(b)c gives a=b p(c) by precisely the previously proved B-linearity and retraction identity. Division by the nonzero b proves that the original arbitrary integral fraction belongs to B. Together with the domain verification this is exactly normality as defined by the cited node. No claim that p is a ring map occurs. The definition invocation and ring identities of steps 4-5 are elementary once the fraction-field embedding has been supplied; neither step hides a non-elementary lemma.

I tested theta=0, which gives the asserted unquotiented descent; unit theta, where C is zero and the normal-domain premise is false but the quotient identities still hold; theta a zero divisor, for example R=A=Z/6 and theta=2, giving the normal quotient F_2; and zero rings, where the normality premise is impossible. For a nonmultiplicative retraction take R=Z, A=Z[t] and rho equal to constant coefficient plus coefficient of t: rho(t)=1 but rho(t^2)=0. It is Z-linear and retracts constants. With theta=2 it descends to F_2[t] to F_2, so all the hypotheses and conclusions still work. The tempting overstrong relative-integral-closedness claim was rejected using the proper algebraic field-extension example above.

All three citations have verbatim full-statement quotes in citations.json. proof_deps equals the union of uses; no newly introduced cycle is possible because the only nondefinition dependency is an existing proof-free Mathlib leaf. The proof is an argument rather than a relabelling of clauses as new nodes; all steps are below 2000 characters. No SGA source is used, no target statement is changed, and nothing in the repository or launcher was written.

## Unfinished work

None in the mathematical split. Required server dry run and push follow this report.
