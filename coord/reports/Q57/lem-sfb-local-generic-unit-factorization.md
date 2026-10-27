# Q57 — lem-sfb-local-generic-unit-factorization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-generic-unit-factorization.json`: statement, split into ten proof steps; no Mathlib match. The statement and its three statement dependencies are unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-symbolic-powers-flat-prime-extension.json`: statement-only general algebra lemma, Stacks 0BC0; unsplit, no Mathlib match. One new node, zero new Mathlib leaves.
- `citations.json`: one exact source-statement quotation for each use in each step. Whole statements are quoted so that the local-ring, domain and Noetherian restrictions remain visible.

## Attachments

None. I searched `lean/WeilConjectures/` for the item tag, generic-fibre units, symbolic powers and flat intersections. The generic-unit declarations found concern constant sheaves or orders of divisors, and do not state this ring factorization. The flat-intersection files do not state symbolic-power base change. No project declaration provides all clauses of the item without sorry.

## WANTED

None for this split. The sources for the item and new node are present in `literature/stacks-project/`. No SGA source is used.

## What needed correction or expansion

The imported item was a statement-only extraction of the affine paragraph of 0BD7, not a proof. I retained its statement and proved the existence, uniqueness modulo base units, and reflection clauses. The distinction between the fibre and B/pB matters: the latter is shown torsion-free over A/p, so it injects into the integral fibre. I did not silently assume that B itself is normal.

The source's local argument is made explicit in three places: the principal ideal is detected by existing associated-prime nodes; flat exact tensoring computes finite intersections; and the local version of the principal-product argument of 09ME is written out using a unit coefficient in a finite sum. Thus none of those few-line consequences becomes an unnecessary new node. Fractional unit reflection uses contraction of (c) and (d); ordinary reflection for an element already in A would not suffice.

Blueprint provenance: `python3 tools/blueprint_refs.py ancestor lem-sfb-local-generic-unit-factorization` returns None. The inherited created.item chain ends at the string `Sheaf.SixFunctors.CtfStabilityDirectImages`, not a DAG node. I retained the inherited null from.node and its via list, and prepended this item for the new node. The inherited from.place names det-thm-sf-ctf-stability-direct-images (3), and is retained with the exact lower-level source passage added for the new node. I read the chapter and unit records, and the latest blueprint's unit and direct-images proof: this is a lower-level commutative-algebra prerequisite in the previously recorded alteration/Picard route, with no change of unit or chapter route. The item is not the unit's key node, so no realization record is changed.

## Searches and reuse

The whole DAG was searched by tags 0BC0, 0BBY, 09ME, 031T, 00PD, 00KV, by symbolic powers, ideal intersections, principal products, associated-prime detection, and generic units. Blueprint searches for symbolic, symbolic power, flat intersection, product-ideals-principal, generic unit, 0BC0 and 0BD7 returned no matching blueprint nodes. Existing normal-domain valuation, faithful-flat contraction, exact tensoring, height bound, finite minimal primes, localization permanence and associated-prime detection nodes are reused, rather than recreated.

All delivered search records were actually run through the mandated msearch.py; raw output is retained in `search-results.json` and the command log in `searches.jsonl`. The item searches repeat both semantic phrasings from its live record because this sandbox initially contained no search log. The symbolic-power node was searched with two LeanFinder formulations (the first was exploratory), LeanSearch, Loogle and RingTheory grep. The delivered entries preserve the exact queries and complete outputs of the final formulation and the other tools. Loogle reports the identifier Ideal.symbolicPower unknown; this is a successful search reporting no such identifier, not a service outage. The two semantic searches return ordinary powers/flat localization/going down, not symbolic-power comparison. RingTheory grep gives only two Eisenstein docstring lines. Additional intersection searches were exploratory, recorded by the tool, and do not claim a new leaf: exact tensoring already has an existing DAG node.

## Not duplicates

lem-sfb-symbolic-powers-flat-prime-extension vs lem-per-vertical-symbolic-powers-completion: the existing statement assumes an excellent henselian local normal domain and its normal completion, supplies descent of primes minimal over a fixed element, and compares only those primes under completion. The new statement is 0BC0 for arbitrary flat maps of Noetherian rings with a specified prime whose extension is prime, and every exponent including zero. Neither the completion hypotheses nor minimal-prime descent are needed here; the existing node does not imply this general flat-extension assertion.

The new node is neither a clause of the item nor its disguised restatement: it has no generic-fibre unit, normal base, local-ring hypothesis, factorization or uniqueness assertion. It is the independent comparison of two ideal constructions used after the valuation exponents have already been constructed. It has no proof or hidden proof sketch in its statement.

## Review by Q57

I read all of Stacks divisors.tex, lemma-in-image-pullback (0BD7), especially the affine paragraph beginning s=a/r and ending s=ug/r, and the following uniqueness paragraph. I read algebra.tex, definition-symbolic-power and lemma-symbolic-power-flat-extension (0BC0), its statement and full proof, before stating the new node. Its Noetherian hypotheses are restrictions, not claims that the source assumed them; R,S need not be domains or local, and q=pS is explicitly required prime. Definitions of flatness, Noetherianity and localization are cited, and symbolic power is defined inline, including exponent zero. No new notation depends on reading a tag.

Step 1 uses the existing maximal-ideal faithful-flatness criterion and ideal-contraction statements, which I opened: the former explicitly covers a flat module over a local ring with nonzero residue quotient, and the latter gives both contraction and injectivity. Locality supplies the required nonzero quotient.

Step 2 uses the statement of flat-tensor-exact, including preservation of injections. I checked the induced quotient map explicitly, and wrote the localization-kernel argument. The fibre hypothesis is applied to the localization, not to the unlocalized quotient. This is precisely why q=pB really is prime and has the stated contraction.

Step 3 uses finite-minimal-primes, the principal ideal height bound, and only the height-one DVR/normalized valuation clauses of normal-domain-principal-divisor-kernel, not that node's proof. I opened all three. Their hypotheses hold for the Noetherian normal domain A and nonzero t=rr'. No regularity or factoriality of A is presumed. The height-zero possibility is ruled out by t nonzero in a domain.

Step 4 uses the definition of a DVR (which supplies a uniformizer), localization-at-prime's stated maximal ideal, localization-noetherian and the stated unit-times-uniformizer-power lemma. I checked that B_i is a local domain independently of normality, with nonzero principal maximal ideal generated by the image of pi_i. Thus the unit-times-power lemma applies directly to B_i and A_i. The image of each A_i unit is a unit in B_i. Cancellation of the nonzero uniformizer and its failure to be a unit prove equality of exponents; there is no unsupported ramification theorem.

Step 5 uses normal-domain-principal-quotient-associated-height exactly for A/tA, and module-injects-localizations-associated-primes exactly for its classes. I opened both statements: the first supplies height one, and the second gives the injective map to all associated-prime localizations. A prime annihilating a class modulo t contains t, and the chain argument makes it minimal over t. Therefore all relevant localizations are in the finite list; this proves the displayed ideal equality without borrowing an unstated intersection theorem from another proof.

Step 6 is elementary: multiplication adds ideal-power cutoffs in each localization, so step 5 detects the product in (t). Step 7 uses flat-tensor-exact for a finite direct sum of quotients; I wrote both image and kernel, with the canonical quotient formula. The only further theorem used is the new 0BC0 node, after step 2 has verified its crucial prime-extension hypothesis. All rings are Noetherian as required by the new statement. Exponents zero cause no exception.

Step 8 uses only the stated ideal-contraction theorem to descend equality of the two ideals. The remainder is the explicit local finite-sum proof of 09ME: one coefficient is a unit because the sum is 1, and cancellation of a nonzero factor makes both ideals principal. This is an elementary argument, not a new invertible-module theorem. Step 9 is elementary cancellation of t in B and defines h=g/r. Step 10 uses exactly the contraction of principal ideals from the same node; it proves both h and h inverse lie in A before asserting h is a base unit, and then applies this to h/h'. Every listed use has a verbatim statement in citations.json. Proof dependencies are exactly the union of step uses.

For the small cases I checked a field base (the list of primes is empty), the identity map, and a DVR base with a chosen uniformizer. In the symbolic-power lemma, n=0 gives S=S, n=1 gives pS=q, an identity map gives equality termwise, and p=0 in a flat domain extension gives zero in positive degree. A non-prime extension is excluded: A=k[t] to B=k[s] with t mapping to s^2 is flat but tB is not prime, so it cannot be used here. For the item, its local map at (t),(s) has nonintegral special fibre, which confirms why the fibre assumption cannot be discarded. The normal nonfactorial local surface k[x,y,z]_(x,y,z)/(xy-z^2), with B=A, also fits: the proof never makes the individual height-one primes principal in A, only in A_i.

I checked delivery-errors B through E against the written files: all notions are introduced, TeX has single semantic backslashes, the new node is statement-only, searches and no-match judgments are real, no duplicate or clause-restatement is created, and no source proof is used through a citation that states something weaker. No step exceeds 2000 characters. The three non-leaf tools from other units are explicitly declared in split_report.tool_uses as generic algebra inputs; this does not replace a step of the unit's route. No Lean file was written, no compiler or Lake command was run, and all writes were confined to this sandbox. Repository and launcher scripts were only read or invoked as required by the brief.

## Unfinished work

The general 0BC0 lemma remains an unsplit child for another stage-1 item, as required for a one-level split. All ten proof steps of this item are complete natural-language arguments. The required full server dry run passed at 7f0bd5654e5; its receipt printed OK (not pushed). The report wording was then clarified to distinguish read-only script invocation from writing files; a final dry run precedes push.
