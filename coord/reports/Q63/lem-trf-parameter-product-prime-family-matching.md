# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-parameter-product-prime-family-matching.json: item statement retained, split into five proof steps; Mathlib verdict no match.
- citations.json: verbatim citation for the sole externally cited proof step.
- report.md: this report.

No new nodes; no Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, parameter-product and prime-family names and regular-parameter concepts. No project declaration states the item. Existing parameter-system and parameter-sequence declarations cover ingredients only.

## WANTED

None.

## Problems found

No statement dispute. The imported source supplies parameter primality, not the whole contracted-family matching theorem. I label the matching proof agent-written. The nearest blueprint ancestor now concerns contracting local terms; the inherited provenance describes an extracted argument down its specialization/alteration dependency chain, rather than a literal paragraph of the latest ancestor proof. I retain this provenance and identify the returned parent steps in split_report.

The main potential gap was identifying primes solely from equality of closed-set unions. Equality alone permits redundant larger primes. The proof instead uses the minimal and pairwise distinct contractions to eliminate every such redundancy, explicitly contracting a two-sided chain.

## Not duplicates

No new nodes. Clause (b) of the existing reviewed lem-sfb-transverse-prime-ideal-parameters supplies all coordinate-product facts, so I cite it without creating another parameter-primality node. Whole-DAG searches for Tag 0AG0, regular-local-UFD, parameter/prime and cotangent concepts found this reusable result. Blueprint searches for regular system of parameters, prime ideals, parameter, contracted and incomparable found no exact imported match. The local clause of lem-trf-parameter-product-reduced-cartier also overlaps, but its scheme conclusion is unnecessary here.

## Review by Q63

I read Stacks more-algebra.tex Tag 0AG0, lemma-regular-local-UFD, especially the opening proof that an element outside the square of the maximal ideal generates a prime ideal. I also read algebra.tex Tags 00NP (lemma-regular-domain) and 00NQ (lemma-regular-ring-CM), and etale.tex Tag 0BIA (lemma-strict-normal-crossings), including its coordinate-component argument. I read the full statement and reviewed proof of lem-sfb-transverse-prime-ideal-parameters and the definitions of regular local ring and regular system of parameters. No new node sources are needed.

Step 1 takes precisely clause (b) of that existing node: the initial parameter ideals are incomparable primes and exactly the minimal primes of the product. The given R, its full parameter system and 0 <= r <= d satisfy every hypothesis. Properness is part of being prime here; it also follows because the parameters lie in the maximal ideal. Its part (a) has extra transverse-quotient hypotheses, but I do not invoke part (a). This is the only non-elementary input and the only off-unit proof citation. I declare it as a generic tool use.

Step 2 checks the empty-product case by evaluating the union at each proper prime q_a itself; no theorem about existence of points is needed. Steps 3--5 use only definitions already written in the item's statement and the conclusions of step 1. In step 3, membership in V((T)) means T lies in q_a; repeated primality supplies a factor. Evaluating the same union at P_i supplies q_b contained in P_i. Contraction preserves containment by the definition of preimage. Minimality of p_a applies because p_b is prime and contains I, so equality of contractions and distinct labels force b=a. Step 4 proves uniqueness of the coordinate and injection using contraction, with no assertion that the ring homomorphism itself is injective. Step 5 proves surjection by applying the union equality at every P_i, followed by incomparability. Pointwise uniqueness proves uniqueness of the bijection. All these steps are short explicit ideal/set arguments; none hides an existence theorem about minimal primes or irreducible decompositions.

I checked d=0 and r=0 (F must be empty), F empty with r>0 (impossible since each P_i lies in the nonempty left union), d=r=1, and R=k[x,y]_(x,y), T=xy, A=R, I=(xy), with the two coordinate primes. I also checked why distinct minimal contractions matter: adding (x,y) to (x),(y) leaves the union unchanged but creates a redundant prime. Its contraction cannot join the required distinct minimal primes. Repeating a coordinate label likewise violates distinctness of the contractions. No flatness, locality or injectivity of phi is used or added.

I checked delivery-errors B--E: no new unsupported or duplicate node; no unrun search recorded; no citation of a proof instead of its statement; no cycle (the cited node's dependency list is independent of this item); no relabelling of the conclusion as a new node; all hypotheses used are present. Fresh searches used msearch.py, and searches.jsonl preserves their actual output summaries. LeanSearch was available in this run. No proof step exceeds 2000 characters. The statement, source and maintainer fields are retained unchanged.

## Unfinished work

None in this one-level split. Dependent nodes keep their existing status.
