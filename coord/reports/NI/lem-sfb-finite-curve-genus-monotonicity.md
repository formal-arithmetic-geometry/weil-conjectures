# Stage-1 report: lem-sfb-finite-curve-genus-monotonicity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-curve-genus-monotonicity.json: item, split into five proof steps; original statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-curve-frobenius-separable-factorization.json: statement-only unsplit geometric factorization lemma; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-curve-riemann-hurwitz-numerical.json: statement-only unsplit Riemann--Hurwitz formula, including wild ramification; no Mathlib match.
- citations.json: verbatim statement excerpts for every citation in every item step.

Two new nodes, zero Mathlib leaves. Research transcripts and the actual msearch log are retained in the sandbox.

## Attachments

None. Searched lean/WeilConjectures for the exact item blueprint tag and for genus inequalities, Riemann--Hurwitz, curve Frobenius factorization, and the proposed new facts. No declaration stating the item or either new fact was found. Existing genus/base-change declarations supply background only; an arithmetic-genus versus differential-genus agreement is not treated as an exact attachment.

## WANTED

None for this split. All mathematical sources used here are present in literature/stacks-project/ or in the current blueprint.

## What needed repair

The item had a correct statement and literature pointers, but no proof. Its source includes inseparable maps: applying Riemann--Hurwitz immediately to the original map would be invalid. The proof now first separates the Frobenius part. The sign of 2g(D)-2 must also be checked before comparing multiplication by the degree with the original value; the genus-zero case is handled separately.

The inherited item ends with unused normality and group-action conventions from its parent. These do not add hypotheses to its genus assertion and were retained with the original statement. No statement dispute or change to the unit route is necessary.

blueprint_refs.py ancestor reports no imported blueprint ancestor for this created.item chain: it eventually reaches the non-node Lean module Sheaf.SixFunctors.CtfStabilityDirectImages. Accordingly from.node remains null, as required by the computed ancestry, and the inherited via chain is preserved and extended in the new nodes. The place explicitly identifies det-thm-sf-ctf-stability-direct-images, proof (3), and the auxiliary high-genus-cover reduction. The current chapter and unit texts, including the direct-image proof, were read; this supplies a subordinate geometric input, without modifying the unit or chapter.

## Unfinished work

The two new input lemmas are intentionally statement-only, as a one-level stage-1 split requires. Their future splits must prove their complete statements. No part of the item's argument is left implicit behind the genus inequality itself.

## Sources and searches

For the item I read curves.tex section-riemann-hurewitz (Tag 0C1B), proposition-unwind-morphism-smooth (0CD2), lemma-purely-inseparable-smooth-genus (0CD0), and lemma-genus-base-change (0BY9). These give precisely the separable-factor and Frobenius-base-change route recorded in the item.

For lem-sfb-curve-frobenius-separable-factorization I read 0CD2 and its proof, theorem-curves-rational-maps (0BY1), and fields.tex lemma-separable-first (030K), including the characteristic-zero case. The node states a factorization of maps, not merely a decomposition of fields. It records the scalar Frobenius, the second projection as the scalar structure, and the affine ring map defining relative Frobenius. In characteristic zero the finite algebraic function-field extension is separable, so the identity first factor is available. In positive characteristic 0CD2 supplies the stated nonconstant separable second factor. The algebraically closed hypothesis ensures that the twists remain geometrically integral; the node explicitly retains this conclusion.

For lem-sfb-curve-riemann-hurwitz-numerical I read the displayed formula in 0C1B, its effective different divisor, the finite-separability criterion 0C1C, and varieties.tex lemma-dim-1-proper-projective (0A26). Proper smooth curves here are projective; their global functions are k by the existing lem-pc-h0-proper-variety clause (2), whose statement I also read. Thus the proper, geometrically integral formulation has exactly the hypotheses needed for the source's formula. This explanatory source check is not an additional proof step of the item: the new unsplit formula node bears the obligation to establish its full proper-curve formulation. The nonnegative integer r is the degree of the effective different, not the tame sum of e_x-1; degree divisible by the characteristic is permitted.

Before making these nodes I searched the whole DAG by tags and concepts, ran blueprint_refs.py searches for genus, Hurwitz, separable curves, Frobenius curves, Frobenius/nonconstant, and genus/nonconstant, and searched the project Lean source. In particular there is no imported blueprint node stating either new assertion. Related base-change, curve-model, and differential nodes have distinct statements, as recorded below.

Each new node has real msearch.py leanfinder, loogle, grep, leansearch, and a second differently worded leanfinder query, recorded verbatim with the returned output and verdict. I read all the hits. Frobenius results concern Weierstrass point maps, function-field definitions, formal smoothness, or the unrelated categorical Frobenius factorization. Hurwitz name results concern modular-form kernel bounds; semantic results concern Weierstrass maps and field/number-theoretic ramification. None states or specializes in one line to either arbitrary-curve assertion. The item's inherited searches are preserved, and its additional actual logged searches are recorded as well.

## Not duplicates

lem-sfb-curve-frobenius-separable-factorization vs lem-sfb-finite-curve-genus-monotonicity: the new lemma constructs a relative-Frobenius/separable factorization and says nothing about genus; the item proves an inequality using that construction, coherent base change, and a numerical formula.

lem-sfb-curve-riemann-hurwitz-numerical vs lem-sfb-finite-curve-genus-monotonicity: the new lemma gives an exact degree/different formula only for separable maps; the item covers every nonconstant map and carries the Frobenius reduction, the zero-genus case, and the arithmetic comparison in its own steps.

lem-sfb-curve-frobenius-separable-factorization vs lem-trf-algclosed-curve-model: the existing statement constructs a proper smooth model of one transcendence-degree-one field and extends valuation maps; it does not factor a given curve map through an iterated relative Frobenius.

lem-sfb-curve-frobenius-separable-factorization vs lem-dl-a1-normal-finite-aut-separable-subfield: the existing statement proves finiteness of the separable subfield under normality and finite automorphism hypotheses; it constructs no curve maps or Frobenius twist.

lem-sfb-curve-frobenius-separable-factorization vs lem-dl-a1-integral-normal-residue-etale-splitting: the existing statement splits an integral ring algebra after etale base change with purely inseparable residue extensions; it is not a curve-map Frobenius factorization.

lem-sfb-curve-frobenius-separable-factorization vs lem-weil-pbc-separable-first-purely-inseparable: the existing statement is the algebraic-field-extension decomposition; it supplies no geometric realization of its intermediate field as a relative Frobenius twist, which is the substance of the new node.

lem-sfb-curve-frobenius-separable-factorization vs lem-weil-pbc-separable-split-purely-inseparable-residue-fields: the existing statement chooses a finite separable scalar extension making tensor-product residue fields purely inseparable; it is not a factorization of a given morphism of smooth curves over the original field.

lem-sfb-curve-frobenius-separable-factorization vs lem-weil-pbc-separable-purely-inseparable-linear-disjoint: the existing statement is injectivity of a tensor-product map for two field extensions; it constructs neither a curve nor a relative Frobenius factor.

lem-sfb-curve-frobenius-separable-factorization vs lem-weil-pbc-sepclosed-finite-extension-unique-embedding: the existing statement concerns unique extensions of embeddings and separable closedness; it does not give the geometric factorization.

lem-sfb-curve-riemann-hurwitz-numerical vs sk-thm-picard-rr: the existing statement gives Riemann--Roch, duality, and the canonical degree of one curve, with base-change clauses; it does not compare canonical degrees along a separable curve map or provide its nonnegative different term.

lem-sfb-curve-riemann-hurwitz-numerical vs lem-a1-nonzero-differential-generically-etale: the existing statement characterizes a nonzero differential by an etale open locus; it gives no degree or genus formula.

lem-sfb-curve-riemann-hurwitz-numerical vs lem-sc-proper-dim-one-projective: the existing statement supplies a projective embedding for a proper scheme of dimension at most one; it has no ramification or genus comparison.

## Review by NI

I checked each step against the source route and opened the statement of every node it cites. Step 1 uses only the explicit definition and finite dimensionality in def-sc-genus; dimension is nonnegative and the genus-zero case closes without a map theorem. The later comparison is consequently made with 2g(D)-2 nonnegative. The current definition's equivalent H^1 form is the genus fixed explicitly by this item.

Step 2 uses the new factorization statement in full: the original C, D and u satisfy its algebraically closed, smooth, proper, geometrically integral, dimension-one and nonconstant hypotheses. The cited statement itself provides C' with all those properties, the actual factorization, and a nonconstant v with finite separable function-field extension. I do not infer these from a field-factorization statement that lacks maps.

Step 3 uses the final, explicit H^1 dimension clause of lem-sc-flat-base-change-coherent, not its proof or a Jacobian assertion. I checked that this clause allows any field-extension homomorphism, using def-pc-field-extension's definition as an injective ring map. The Frobenius self-embedding is such a homomorphism, both copies are algebraically closed, and C is proper. The base change has the second-projection scalar structure from step 2. Thus the formula's two vector-space dimensions are exactly the two arithmetic genera used here, including when the Frobenius automorphism of the algebraically closed field is nontrivial. This generic coherent-cohomology tool belongs to another unit and is declared in split_report.tool_uses; the alteration unit has no replacement for it.

Step 4 cites the new numerical Riemann--Hurwitz statement, which explicitly supplies positive integer d and nonnegative integer r and the equality used. Step 2 verifies its separability hypothesis for v, so the original inseparability is never silently ignored. Its statement allows wild ramification and does not assume invertibility of d. Step 5 writes out the full integer comparison and substitutes the genus equality already proved in step 3. It uses no new geometric fact. Every cited node has its exact relevant statement quoted in citations.json.

I checked delivery-errors B--E against the files: each new node introduces its own objects, cites its notions, has a Stacks tag and label, has genuine logged Mathlib searches, and has empty proof/proof_deps. Neither is a clause simply renaming the item. The formula carries stronger numerical information under separability; the factorization carries different geometric data. Existing general field and base-change statements were reused or distinguished, and no elementary arithmetic or genus-base-change specialization was made a new node. All proof uses occur in proof_deps and no new dependency points back to the item. No step exceeds 2000 characters.

For small cases I checked an identity map (degree 1 and r=0), a purely relative Frobenius map (separable factor degree 1 and unchanged genus), genus-zero target (handled before the sign argument), genus-one target (the formula forces source genus at least one), and an unramified positive-degree separable cover of target genus at least two. For the latter, g(source)-1=d(g(target)-1); a nonnegative different only increases the left side. Smooth proper integral zero-dimensional schemes and disconnected curves are excluded by the dimension-one/integrality assumptions. These checks found no false statement or missing hypothesis. The repairs were the explicit separable factor, scalar structure, genus-zero branch and wild different; the original statement remains unchanged.

The first server preflight found that grouped references such as [def-a, def-b] are not recognized as node citations. I changed those references in both new statements to separate [def-a], [def-b] references and refreshed the exact citation excerpts. No mathematical assertion or search changed.
