# Stage-1 report: lem-sfb-pointed-word-kernel-stabilization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-pointed-word-kernel-stabilization.json — statement, now split into seven proof steps. No exact Mathlib match.
- citations.json — a verbatim statement quotation for every node cited by every proof step.
- report.md — this report. searches.jsonl retains the actual search log; write_split.py is sandbox-only preparation material.

There are **0 new nodes and 0 new Mathlib leaves**. All supporting geometry and dimension statements already occur in the DAG. The original item's earlier search records, source, statement dependencies, creation record, and blueprint ancestry were retained. Only doubled TeX escapes in the statement were normalized; hypotheses, objects, and conclusions are unchanged.

## Attachments

None for this item. Searches in lean/WeilConjectures for its exact blueprint id, wordMap/word_map, pointedWord/pointed_word, and pointed word/kernel terminology found no declaration stating the whole item. Regular.lean has useful general smooth/regular geometry, not this theorem. The existing node lem-kun-dimension-finite-type already records the closed declaration AlgebraicGeometry.exists_topologicalKrullDim_le; it is cited rather than restated or reattached.

## WANTED

None. Milne's Algebraic Groups PDF and the relevant Stacks sources are locally available.

## Corrections and route

The imported node had no proof. Its mathematical statement is true as written, including non-homomorphic pointed maps and nonreduced targets. No STATEMENT-DISPUTED correction was needed. The only statement edit removes doubled TeX escapes.

I read Milne, Proposition 6.20(a), printed p.130 (PDF p.142), and Section 2h, printed pp.54–55 (PDF pp.66–67). Section 2h gives the arbitrary pointed-map product construction and identity-appending inclusions; 6.20(a) supplies the prime-kernel chain route. The proof here uses the finite dimension of the finite-type target J to make the chain argument explicit. It does not substitute the ascending-chain condition on ideals, and it does not infer stabilization merely from one adjacent equality. No inversion-stability assumption on the image, nor a subgroup structure on Z, is needed.

I read the chapter record, the inherited sk-thm-sf-ctf-stability unit record, and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its sk-thm-sf-ctf-stability-direct-images.proof.md. This long auxiliary ancestry serves the recorded alteration/moduli prerequisite of direct-images (3); this split changes no unit step or route. blueprint_refs.py ancestor returns None for this item's inherited ancestry, whose from.node is already null. I retained that ancestry and its precise from.place rather than inventing a blueprint node. Whole-blueprint searches for pointed product, kernel stabilization, descending prime, prime ideals, and stabilization found no equivalent imported statement; the latest blueprint text search likewise found no copy of this auxiliary.

## Not duplicates

No new nodes are created. Existing lem-trf-connected-point-geometrically-connected, lem-trf-smooth-connected-fibre-normal-integrality, lem-sc-geometrically-irreducible-product, sbc-lem-smooth-geometrically-reduced, lem-weil-pbc-fibre-product-affine-spectra, lem-pc-proper-base-change, lem-trf-smooth-composition, and lem-kun-dimension-finite-type are reused. Generic finite-dimensional chain reasoning and kernel/quotient calculations remain explicit elementary steps, rather than becoming new nodes repeating clauses of the item.

## Search results

The new sandbox's logged searches were all read, alongside the retained searches made when the item was created. LeanFinder with both a product-morphism phrasing and a prime-chain phrasing, LeanSearch with scheme-theoretic-image and finite-dimension phrasings, Loogle with PrimeSpectrum/WellFounded and Ideal.IsPrime/Antitone, and the recorded Mathlib greps found no exact theorem for the item. LinearMap.eventually_iSup_ker_pow_eq is about ascending kernels of powers of one linear endomorphism; its source in RingTheory/Noetherian/Defs.lean:181 was read. Module.End.ker_pow_constant is also a different linear statement. Scheme.Hom.image and specTargetImageFactorization merely construct images/factorizations; the latter's source in AlgebraicGeometry/AffineScheme.lean:1239–1255 was read. FiniteRingKrullDim and Ideal.finiteHeight_of_isNoetherianRing are supporting algebra notions/results, not this pointed-map theorem. No service outage was reclassified as absence, and no unrun search is recorded.

## Review by Q13

I checked the split against delivery-errors B–E with the node statements and source passages open. There are no unsplit new statements to audit. All seven steps have boolean elementary flags, specific source places, and proof_deps equal to the union of uses. The non-elementary geometry is cited by statement, never extracted from another node's proof. Every citation has its actual complete statement in citations.json, making the relevant hypotheses and conclusion reviewable verbatim.

Step 1 uses the exact connected-with-a-point criterion of lem-trf-connected-point-geometrically-connected (Stacks varieties.tex, Tag 04KV, label lemma-geometrically-connected-if-connected-and-point). I verified the residue field of the identity point is k using the retraction through the identity section; hence the algebraic-closure-in-residue-field hypothesis is satisfied. The base for lem-trf-smooth-connected-fibre-normal-integrality is Spec k, with its single fibre G, assumed smooth and now geometrically connected. That node expressly gives integral field-extended fibres. Its source geometry in varieties.tex Tag 056T and more-morphisms.tex Tag 057J was read. This proves integrality over every extension, not only over k. The definitions of geometric integrality and integral scheme give the claimed irreducibility.

Step 2 is an actual induction with base G and step G^m times G. I checked the affine tensor-product statement in lem-weil-pbc-fibre-product-affine-spectra and Stacks schemes.tex Tag 01JQ, label lemma-fibre-product-affines; it explicitly states affineness, which the fibre-product definition alone would not give. Only clause (2) of lem-pc-proper-base-change is used, for smoothness of the projection; lem-trf-smooth-composition gives the smooth structure map. Their source statements, morphisms.tex labels lemma-base-change-smooth and lemma-composition-smooth (01VB and 01VA), were read. lem-sc-geometrically-irreducible-product assumes precisely the two geometric irreducibility hypotheses available at each induction step. sbc-lem-smooth-geometrically-reduced concerns smooth fibres, applied to the structure morphism over the one-point base. Thus every field extension is both reduced and irreducible, and the integral-scheme definition makes its affine coordinate ring a nonzero domain. Nothing about products of arbitrary connected spaces is assumed.

Step 3 uses exactly the group operations/unit identity, fibre-product universal property, and contravariance of Spec recorded in the three definition nodes. It writes the identity-appending morphism equality before taking pullbacks, so the inclusion goes in the correct descending direction. Primality is checked directly in the domain B_n, including properness via 1 not in the kernel. This is ordinary kernel algebra, not an invocation of a hidden group-image theorem.

Step 4 cites the full finite-type dimension conclusion of lem-kun-dimension-finite-type for J over the given field and the chain definition def-kun-topological-krull-dimension. I read its current blueprint statement and its closed upstream declaration at WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean:212. The step writes why V(P) is the closure of its prime point, why that closure is irreducible, and why a strict prime inclusion gives a strict reverse inclusion of closed subsets. Thus the finite dimension bounds strict drops even when many consecutive I_n coincide. These are short direct consequences of the cited statements and the Zariski definition, so this is an elementary use of a cited dimension theorem.

Step 5 selects later strict drops under the negation of eventual constancy and derives d+1 strict inclusions. It carries the stabilization argument itself and introduces no restatement node. Step 6 proves the intersection equality, quotient-domain property, integral-spectrum property (generic zero prime plus reduced domain localizations), and the explicit injective quotient pullback. I opened def-pc-reduced-scheme, which defines reducedness by stalks, and def-pc-integral-scheme, whose equivalent reduced/irreducible formulation is exactly what is used. Step 7 takes the zero prime of the source coordinate domain to the zero prime of the quotient, and computes its closure as all of Z. This verifies density explicitly without confusing scheme-point image with rational-point image or needing Chevalley's theorem. The final pullback is the quotient map followed by its induced injection, as required.

I tested the trivial group G, constant identity map, r=1, J trivial, and zero-dimensional targets: the kernels are then already constant and prime where appropriate, with a nonzero source coordinate algebra. Positive characteristic and nonreduced J cause no problem: the proof only needs J finite type for dimension and allows its nilpotents to lie in all I_n. The argument never uses commutativity, a homomorphism property for phi, inversion closure, or a special characteristic. Empty G is excluded both by connectedness and by its identity section; all domain and generic-point arguments are consequently nonempty. Every non-elementary step is under 2000 characters, and the longest elementary steps spell out only the routine algebra/topology calculations described above. No source forbidden by the no-SGA route is used.

The off-unit statements are declared in split_report.tool_uses with their exact generic role. The affine fibre-product and smooth-composition results are already Mathlib leaves, and the finite-dimension node is Lean-closed. These are background tools for the inherited Milne argument, not a change to the unit route. No maintainer tool_uses field was written.

## Unfinished work

None in the stage-1 split. The required server dry run and direct delivery follow this report; their result is reported by the delivery command.
