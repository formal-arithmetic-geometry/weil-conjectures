# Q68 stage-1 delivery: lem-sfb-dvr-perfect-residue-algebraic-tower

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-perfect-residue-algebraic-tower.json: item, statement unchanged, seven-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-p-independent-root-quotient-field.json: statement-only field-theory input; searched, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-free-field-fibre-dvr.json: statement-only finite-algebra input; searched, no Mathlib match.
- citations.json: the thirteen actual step citations, with verbatim statements.

## Attachments

None. Searched the live WeilConjectures source for the item's blueprint tag and for perfect residue, p-basis, weak unramifiedness and DVR notions. The existing PBasis files cover p-basis existence, not this algebraic DVR extension. DVR root files concern uniformizer roots or tame roots and do not provide the perfect-residue construction. No project declaration states the full item or either new input. Existing p-basis, monic-quotient, PID-normality and finite-integrality nodes are reused.

## WANTED

None. The proof source is available locally.

## Corrections and scope

The imported statement is correct; no hypothesis or conclusion was changed. Stacks more-algebra.tex, Tag 09II (proposition-epp-essentially-finite-type), proof lines 35980–35993, supplies the route. Its infinite-variable notation is interpreted by finite subsets of the p-basis, with a separate finite root level. The written transition sentence appears to give the arrow backwards: the forward algebra homomorphism is t_(i,n) mapped to t_(i,n+1)^p. The split spells this out with compatible roots in one algebraic closure, so every union is literally a union of subrings of one field. This is an orientation clarification, not a disputed mathematical statement.

The current latest blueprint direct-image proof (3), in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, no longer states this supporting commutative-algebra result. I retain the item's historical blueprint provenance and creation chain. tools/blueprint_refs.py ancestor reports the existing null ancestor. Searches of the entire imported blueprint for p-basis, p-independent, p-power roots, perfection and closed fibre is a field found no duplicate. I read the chapter record and the sk-thm-sf-ctf-stability unit; this split expands only the inherited auxiliary algebra node and does not change their route or realization records.

The two new inputs are strictly smaller than the item. One is a field-theory calculation for a fixed finite independent family and fixed root exponent, with no DVR. The other is a finite-algebra criterion with no residue characteristic or perfection assumption and no infinite tower. Neither asserts the item's extension exists or packages its conclusion.

## Mathematical continuation of the new inputs

For the finite root field input, p-independence says the bounded monomials in b_i are independent over k^p. For the first roots, raising a prospective relation among root monomials to p gives such a relation, so evaluation in an algebraic closure is injective. Its finite-dimensional image is a domain and hence a field. At level n, the same argument uses independence of the b-monomials with exponents less than p^n over k^(p^n). This follows by induction, grouping exponents by their residue modulo p, applying p-independence and then injectivity of Frobenius. The spanning basis is monic division; raising the finite expansion to p^n puts it in k. This explains the smaller field calculation to be proved when that unsplit node is taken up; its node carries no proof.

For the finite-free DVR criterion, B is finite integral over A, so its maximal ideals contract to the unique maximal ideal of A; the field quotient makes pi B its unique maximal ideal. Finite freeness makes pi a nonzerodivisor and gives intersection_n pi^n B = 0 by coordinates in the DVR A. A nonzero b therefore has a largest divisibility exponent a and is u pi^a, with u outside pi B and hence a unit. Products of such nonzero elements are nonzero; thus B is a domain. The least-exponent argument makes every ideal principal and pi remains a nonzero nonunit, proving the DVR claim. This is more than a one-line specialization of the Mathlib DVR equivalences, which require local-domain hypotheses to start with. No domain assumption is smuggled into the new statement.

## Not duplicates

lem-sfb-p-independent-root-quotient-field vs lem-sfb-dvr-perfect-residue-algebraic-tower: fixed finite characteristic-p field quotient, without a DVR or a perfect-residue extension construction.
lem-sfb-p-independent-root-quotient-field vs lem-sfb-epp-essentially-finite-type-traits: no pair of traits, Epp solution, or normalized tensor branches; only the finite residue calculation used by its preparation.
lem-sfb-p-independent-root-quotient-field vs lem-sfb-dvr-normalized-finite-stage-descent: gives a specific root quotient field, whereas descent assumes algebraic normalizations and descends local properties.
lem-sfb-p-independent-root-quotient-field vs lem-sfb-epp-weak-perfect-residue: no weak Epp solution or perfect base residue hypothesis; gives a finite purely inseparable field quotient from independence.
lem-sfb-p-independent-root-quotient-field vs lem-sfb-raynaud-faltings-normalized-reduction: concerns only characteristic-p fields and no flat model, geometric normality, or reduced special fibre.
lem-sfb-finite-free-field-fibre-dvr vs lem-sfb-dvr-perfect-residue-algebraic-tower: a fixed finite free algebra criterion, with no perfectness, root selection, algebraic extension existence or directed union.
lem-sfb-finite-free-field-fibre-dvr vs lem-sfb-epp-essentially-finite-type-traits: no Epp solution or normalization of a pair of traits; derives the DVR property of a specified finite algebra.
lem-sfb-finite-free-field-fibre-dvr vs lem-sfb-dvr-normalized-finite-stage-descent: no descent over an algebraic tower and no assumed normalized DVR branches; derives local-domain properties from finite freeness and a field fibre.
lem-sfb-finite-free-field-fibre-dvr vs lem-sfb-epp-weak-perfect-residue: no residue perfection or Epp conclusion; the algebra B is given, and its field fibre is a hypothesis.
lem-sfb-finite-free-field-fibre-dvr vs lem-sfb-raynaud-faltings-normalized-reduction: no geometric normality, base extension, normalization or reduction theorem; just a finite free algebra criterion.
lem-sfb-finite-free-field-fibre-dvr vs lem-sfb-p-independent-root-quotient-field: arbitrary-characteristic DVR algebra criterion versus characteristic-p field polynomial quotient calculation.

The p-basis-existence and p-independent-extension nodes (07P2) select or extend independent families; they do not adjoin roots or state that the root quotient is a field. The existing monic-quotient-free node supplies the basis over a ring but not the field or DVR conclusions. The existing DVR unit-times-power node assumes a Noetherian local domain and does not prove those hypotheses from the finite algebra data. The parameter-root nodes concern roots of regular parameters, whereas these residue-basis lifts are units. lem-per-perfect-residue-coefficient-dvr requires an already perfect residue field and completeness, constructs a complete coefficient extension, and gives no algebraic fraction extension of an arbitrary DVR.

## Review by Q68

I read delivery-errors B–E in full and checked the node files against the actual Stacks paragraph, as well as the p-basis definition and lemma at Tags 07P1/07P2 and the DVR equivalences at Tag 00PD. For both new nodes I read the 09II sentence they make precise, searched the whole DAG and blueprint, searched the project Lean, and ran logged LeanFinder, Loogle, LeanSearch and Mathlib grep queries, with a second natural-language phrasing. The search hits were inspected: DVR TFAE requires a Noetherian local domain, the purely-inseparable finrank theorem merely gives an unspecified power of p for an existing field extension, and the Frobenius basis transport result assumes separability. None states either new input. The Loogle query with unqualified finrank was retried using Module.finrank; the logged unsuccessful query is preserved, not treated as an absence proof. No new Mathlib leaf is claimed.

Step 1 uses exactly p-basis existence and algebraic-closure existence, and the latter's definition supplies roots of every nonconstant polynomial. I checked that k is a field of prime characteristic and that the root polynomials have positive degree, regardless of the characteristic of K. Lifting residue elements only uses surjectivity of A to its residue field.

Step 2 uses the monic quotient node for each successive variable and its reduction clause, then the new finite p-independent root field statement. The finite subfamily is independent because its monomials are part of the p-basis; no finite p-basis assumption appears. The constant rank is positive, including empty J. Step 3 uses precisely the new finite-free field-fibre criterion, and the existing DVR factorization node to prove evaluation injective. All local-domain and Noetherian hypotheses of factorization follow from the newly proved DVR property; injectivity is not assumed to prove it. A unit cannot map to zero in the nonzero field Omega, and pi already lies in K nontrivially.

Step 4 uses DVR factorization to calculate contraction of the principal maximal ideal along the explicit inclusions. This ensures that a unit at one stage stays a unit and a nonunit never becomes a unit at a later stage. Step 5 is a direct elementary ideal argument, not a claim that arbitrary filtered unions of Noetherian rings remain Noetherian. It gives a finite-stage fraction-field spanning set explicitly and proves the directed union is a field. The principal-ideal conclusion and the nonunit pi are exactly what the cited DVR definition requires. No separate union-DVR node is created for this routine argument.

Step 6 uses the finite-algebra-is-integral node and the PID-normality node, each for the precise clause its statement supplies. An A-integral element is also B-integral because the same coefficients lie in B. The integral-closure equalities therefore do not assume integral closedness of an infinite union; they follow from the proven PID property. Step 7 cites no outside theorem: it computes quotient equality by a common finite stage, takes the p^n power using the explicit formula already established in Step 2, and writes out pth roots of coefficients using the p-basis expansion. The pth roots of the finitely many coefficients and the next root level all lie in a common finite stage. This proves perfection of every element of the residue field, not just of the selected generators.

I tested k perfect (empty p-basis, so P=K and A'=A); k=F_p(s) with A=k[[pi]] (residue roots of s and unchanged uniformizer); two independent residue variables; an infinite p-basis (every expression still uses finitely many indices); n=1; and mixed characteristic. For the finite-algebra criterion, B=A is the rank-one test. B=A[e]/(e^2) and a ramified uniformizer-root extension fail its field-fibre hypothesis, so the statement excludes the nilpotent and ramified counterexamples. For the p-independent input, b=0 or a pth power fails independence, preventing the repeated-factor counterexample. Neither new statement needs a completeness hypothesis. Every step is below 2000 characters, and each non-elementary input is a cited node rather than a bare source tag. New nodes carry statements only and their statement dependencies introduce the notions actually used.

The off-unit p-basis existence citation is explicitly declared as a generic tool use in split_report; the remaining off-unit inputs are definitions or existing Mathlib leaves. citations.json quotes the live statements verbatim, not their proofs. No SGA source, Lean writing, compiler, Lake or local preflight was used.

## Unfinished work

None for the one-level split. The two new statement-only inputs intentionally join the stage-1 queue; they are not split recursively in this delivery.
