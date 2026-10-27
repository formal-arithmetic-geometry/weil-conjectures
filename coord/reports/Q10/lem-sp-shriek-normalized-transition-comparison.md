# Worker report: lem-sp-shriek-normalized-transition-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-shriek-normalized-transition-comparison.json`: item, split into five explicit steps using existing nodes. No new nodes and no Mathlib leaves.
- `citations.json`: 14 step/node entries with verbatim extracts from the cited statements.
- `searches.jsonl`: five actual Mathlib searches recorded by msearch.py; the item retains its inherited searches and appends the five new records.

## Attachments

None. I searched the current read-only `lean/WeilConjectures/` for the exact blueprint tag and for tower, coefficient-transition and semilinear compact-support terminology. IntegralCoefficients.lean:409 states `exists_transition_of_isDerivedBaseChange`, an existence assertion for input reduction transitions, not the compact-support output formula. Its later normalized-tower construction does not give this item. No project declaration found states every clause.

## WANTED

None. The source documents used are present locally. No SGA source is used.

## Corrections and source audit

The item was unsplit with no earlier sandbox split/report. I read the current unit and chapter records, GOAL.md, the three-level route rules, the worker brief and delivery-errors B–E. This is the reduction-transition sentence in paragraph (1) of main-20261015 `sk-prop-sp-integral-adjunction-direct-image.proof.md`; its surrounding argument invokes the finite coefficient comparison, not a new trace construction. I read that paragraph and the tower-operations proof (paragraphs (1) and (2)) and the coefficient-comparison proof (Steps 1 and 4).

There was a malformed JSON string escape: the intended TeX `p\ne\ell` had become `p` followed by a newline and `e\ell`. I repaired that typography, without changing the characteristic hypothesis. I added the already bracket-cited `sk-def-sp-coefficient-towers` and `det-sp-coefficient-towers-abelian` to stmt_deps. There is no mathematical statement dispute or change of route.

The proof does not assume evaluations are faithful. It identifies the maps using the existing simultaneous system model, then explicitly pastes the input and coefficient cocycles. No claim is made that evaluated K-injectives remain K-injective, and no bounded flat model or finite resolution of a quotient ring is used.

## Searches and reuse

The five fresh searches use leanfinder (two phrasings), leansearch, loogle and grep, with the literal queries recorded in the item and in searches.jsonl. The hits are underived module/presheaf/sheaf pushforward composition, extension/restriction adjunctions, locally cartesian closed counits and unrelated continuous compact-support maps. I read the types printed by the services and the underived pushforward source in Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean. None states a derived semilinear tower compact-support transition formula or specializes to it in one line. Both leanfinder phrasings agree on that negative conclusion. All services answered successfully.

Whole-DAG keyword searches and `tools/blueprint_refs.py search` for transition, semilinear and reduction maps found existing foundational ingredients. In particular `lem-sp-tower-transition-compatibility` treats a specified constructible finite-Tor tower interface, finite direct-image coordinates and O/(ell)^(n+1) indexing. I read its statement and proof. This item treats arbitrary D+ systems with finite-Tor constructible levels and additionally asks for explicit naturality and the n-to-m-to-r identity. Rather than create an overlapping node or cite the narrower interface with extra data, I used the common system and finite-comparison ingredients directly. The current blueprint same_as search found no other blueprint node with this full statement; same_as remains [].

## Not duplicates

No new nodes were created. The overlapping transition-interface node was reused as search evidence, not copied. The system operations, open tensor normalization and scalar cocycle already exist and are cited in the proof.

## Review by Q10

I checked the statements of every cited node, not their proofs as substitutes for missing hypotheses. Step 1 cites `def-sp-reduction-direct-image-comparison`: it actually defines gamma by the scalar-extended proper counit and b as Rp(e) gamma on the ambient categories. That definition is why no invertibility or coefficient-flatness hypothesis is needed to form the maps.

For step 2 I read `lem-cbc-proetale-extension-zero`, which states exact termwise open extension and restriction-of-scalars compatibility, and `lem-sf-open-tensor-normalization`, which states the open-unit normalization, full faithfulness, arbitrary ring maps and the same assertions on ringed diagram sites. I also read its local sources: Stacks 0GL1 (sites-cohomology.tex, lemma-j-shriek-and-tensor) and 0E8I (sites-modules.tex, lemma-j-shriek-and-tensor). Those tags give the tensor equality; the stronger system and normalization assertions are supplied by the cited DAG lemma, not attributed to the tags alone. After identifying the source by e with an extended object in the image of j_!, restriction through the open unit is faithful. The displayed open-transition map restricts to rho, which is the adjoint of the original semilinear transition. The definition's comparison of composite left adjoints has these same units, so it is this e, rather than an unspecified tensor isomorphism. The semilinear-derived-sections statement supplies the actual ordinary derived system model and ordinary open level adjunctions.

For step 3 `lem-coef-semilinear-derived-sections` explicitly states the direct-image transition as G(t) followed by the scalar mate and says evaluations preserve units, counits and transition maps. Its exact displayed mate is the one defined in step 1. `det-sp-tower-shriek-levels` gives the canonical comparison for every bounded-below input; exact j_! preserves the lower bound, so C in D+ is sufficient. The formula follows by substituting the open transition and functoriality. I checked the background source cited by the system lemma, Stacks 079P (injectives.tex, theorem-K-injective-embedding-grothendieck): it gives functorial K-injective replacements only. The substantially stronger system realization is an existing cited node, not falsely asserted to be 079P itself. I also read Stacks 0D6E (sites-cohomology.tex, lemma-derived-pushforward-composition) for the normalized derived adjoint composition background.

Step 4 uses the actual naturality of input reduction in `det-sp-coefficient-towers-abelian` and the natural comparisons in the definition of b. The two naturality squares compose, including when rho is zero or noninvertible. This is an elementary manipulation of those stated maps, not a new lemma.

Step 5 uses the input cocycle from `det-sp-coefficient-towers-abelian`, the displayed b cocycle in `det-sp-reduction-direct-image`, and the canonical associator and its naturality in `det-sp-scalar-extension-functor`. I checked the order of every factor: naturality moves T(rho) past b, then the input rho cocycle contributes F_r(alpha_X), and the b cocycle changes the remaining three factors to b^(n,r) alpha_Y. Thus the final map has the required source `(F_n C_n tensor A_m) tensor A_r` and target `F_r C_r`. The quotient rings are finite commutative ell-primary rings; the schemes, proper map and open immersion satisfy the finite-comparison hypotheses. Finite Tor amplitude bounds cohomology by testing against the unit sheaf, so the constructible finite-Tor levels meet the bounded constructible input requirement. Scalar extension preserves finite Tor amplitude over the target ring; no quotient map is assumed to have finite projective dimension.

I tested the identity coefficient cases n=m and m=r, zero C, empty X, j the identity, p the identity, and O=Z_ell with Z/ell^2 to F_ell. For identities the unit comparisons recover the original transition; zero and empty inputs give zero maps. For the nonflat quotient, the construction still uses derived tensor throughout and the two associators have the correct target-ring actions. No normalization of C or uniform Tor bound across levels is assumed or used.

Against B–E: no new unsplit statement conceals a proof; every non-elementary ingredient is an existing cited statement; no new clause of the item has been relabelled as a node; the actual comparison and cocycle are displayed rather than replaced by “transports” or “compatibility is clear.” Each step is below 2000 characters, and none hides an uncited subclaim. Every use has a verbatim quotation in citations.json. Off-unit foundational tools are declared in split_report.tool_uses. The checks will run only on the server through the authorized delivery tool.

## Unfinished work

None in the mathematical split. Server dry run and push results are recorded below after they complete.
