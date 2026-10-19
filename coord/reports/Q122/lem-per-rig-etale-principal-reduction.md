# Worker report: lem-per-rig-etale-principal-reduction

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-etale-principal-reduction.json: item, split in seven steps; statement preserved; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-etale-compatible-model-tower.json: statement, unsplit; no Mathlib match. Replacement models have actual quotient isomorphisms and commute with their maps to E/a^mE.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-etale-principal-tower-limit.json: statement, unsplit; no Mathlib match. General finite-type principal quotient-tower reconstruction, without any E or etale hypothesis.
- dag/nodes/sec-deligne-laumon-a1/lem-per-rig-etale-principal-tower-conormal-transfer.json: statement, unsplit; no Mathlib match. General uniform completed conormal annihilation criterion, including a uniform closed-base-change formulation and detection on all adic truncations; no tower or F is presumed.
- dag/nodes/sec-deligne-laumon-a1/lem-per-etale-supported-cotangent-completion.json: statement, unsplit; no Mathlib match. Ordinary finite-presentation conormal cohomology is finite and killed by an ideal power when the algebra is etale outside its vanishing locus. The completed-homology comparison is reused from the current DAG.

The sandbox also contains citations.json, actual msearch logs and raw search outputs. The three earlier helper drafts are retained under prior-attempt/ for provenance; the delivered versions correct their statements. There was no earlier item copy, report, or searches.jsonl in this item's sandbox. Earlier searches in helper drafts were not used as evidence for the repaired statements: all delivered helper search entries were run with msearch.py for this item and their results read.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the item tag/id, all four helper ids, rig-etale variants, conormal-completion and compatible-algebra notions. No declaration states this theorem or any helper. Ordinary project limit and stalk declarations that matched compatibility words do not state any algebraization result. Upstream master is reference material, not a closed-proof attachment.

## Wanted literature

None. All mathematical sources used are in literature/stacks-project/restricted.tex and its referenced algebra.tex statements. No SGA source is used.

## Corrections and route

The item agrees with Stacks 0AKA (lemma-approximate), from the compatible-model paragraph through construction and rig-etaleness of B-prime, stopping before the final principal algebraization. Its statement was not changed. This is a supporting commutative-algebra argument for the blueprint ancestor lem-per-artin-gabber-affine-curve through the recorded local-duality/Elkik chain, not a change to the Fourier-perverse unit. I read its current main-20261015 blueprint text and the chapter/unit records. This item is not the unit's key statement; unit realization fields are untouched.

The earlier compatible-tower draft asserted only transition maps, while its limit draft inferred F/a^mF=C_m. Maps alone do not imply that: take A=k, a=0, K=I=(1), E=0, C_m=k x k and transitions (x,y) -> (x,x). Every C_m is finite etale, its K-completion is zero, and the inverse limit is k, not k x k. The new statements require actual quotient isomorphisms, exactly as equation-C and the compatible-model paragraph of 0AKA do. The compatibility helper is not an assertion about etaleness of transitions.

The former conormal-transfer draft began with another node's setting, and simply asserted the final torsion conclusion for F. It is now a self-contained general criterion (0AJU), with uniform closed base change (0AK2); the item carries the transfer argument through C_m and E_m. The prior limit draft also packaged the item's I-completion comparison. That comparison is now written out in Steps 3 and 4 using the actual maps modulo I^n. The fourth helper now isolates the ordinary finite-type conormal finiteness and ideal-power torsion argument. The completed-homology comparison is reused from lem-per-completed-jacobian-homology-comparison, which appeared in the refreshed DAG during the dry run.

A subtlety in 0AKA's last paragraph is the uniform exponent after quotienting by a^m. Merely citing the existing closed-base-change node would give one K_m-power bound for each m, with no uniform bound. The new criterion's condition (ii) is uniform in the quotient ideal L and uses the image of the original ideal power. This formulation follows from (3) -> (2) of 0AJU (one original ideal power acts as zero on the complex) and 0AK2 (that same multiplication remains zero after each base change). It does not claim the original exponent is unchanged. Detection on the principal truncations uses the converse of 0AJU (3) <-> (4). No flatness of A -> A/(a^m) is used.

## Review by Q122

I read restricted.tex at lemma-approximate (0AKA), including the full inductive replacement paragraph, the inverse-limit paragraph and the final cotangent argument. I also read lemma-topologically-finite-type (0AJP), its category equation-C and complete-algebra category equation-C-prime; lemma-topologically-finite-type-Noetherian (0AJQ); lemma-equivalent-with-artin (0AJU), especially conditions (3),(4) and their proof; lemma-zero-after-modding-out (0AK2) and the neighboring base-change statement; lemma-NL-up-to-homotopy (0GAE); lemma-NL-is-completion (0GAF) and lemma-NL-is-limit (0AJS). For the compatible-tower helper I read the cited full-faithfulness argument and lemma-lift-approximation, as well as their use in 0AKA. The four new statements introduce their own objects and hypotheses; each is statement-only with empty proof and proof dependencies.

Step 1 uses the actual statement of lem-weil-pbc-module-completion-complete, which provides completeness and projections for a module and any finitely generated ideal, not merely a definition of completion. Noetherianity provides finite generation of K. The repaired compatible-model statement then provides every transition isomorphism and every commuting map v_m needed later. Its hypothesis that E_m is complete is verified by the first citation, and all its other hypotheses are exactly the item's chosen models.

Step 2 uses only the new general principal-tower-limit statement. I checked the reduction-isomorphism hypothesis, the finite-type A/(a^m) hypotheses, and that its isomorphisms are induced by projections. This provides the completed polynomial presentation and finite-type special fibre used in Step 7. No completion comparison with E or conormal assertion is imported from this helper.

Step 3 applies the projection/kernel clause of module-completion-complete with T_n=IA_n, not accidentally with K_n when the quotients differ. The nilpotence exponent n gives the explicitly proved cofinality T_n^(j+n-1) contained in K_n^j. Equality of completions then follows directly from restriction of compatible residue classes. The quotient isomorphism is F/I^nF -> E/I^nE and is induced by the displayed maps. This elementary cofinal-filtration calculation is kept in the step, not made a node. Step 4 uses only those previously established quotient maps: the commuting squares, inverse sequence of inverse isomorphisms, definition of u, and identification of its induced completion map are all explicit. It is elementary and cites no additional lemma. This avoids assuming that E is a-adically complete without proving it.

Step 5 uses the same module-completion statement to identify P/IP; it then uses condition (i) -> (ii) of the new uniform conormal criterion. The special fibre E/IE is a polynomial quotient, and V(IA_m)=V(K_m) is checked prime by prime using a^m=0. This verifies all base-change hypotheses, including the topology on E_m. The bound is selected before m varies. The ordinary closed-base-change node does not state this uniformity, so it was not substituted for this citation.

Step 6 chooses finite polynomial presentations of C_m. I read the refreshed statement of lem-per-completed-jacobian-homology-comparison: it supplies isomorphisms from the completions of the kernels and cokernels of these presentations to the kernel and cokernel of ANY completed polynomial presentation of E_m. It does not claim that an uncompleted module maps isomorphically to its completion. The narrowed helper supplies the missing fact: these ordinary conormal cohomology modules are finite and K_m-power torsion, using etaleness outside V(K_m). Their completion maps are isomorphisms by the explicit eventually constant quotient-system argument in Step 6. This is where the individually varying torsion exponents b_m are used. I checked Noetherianity of A_m by reading finite-type-algebra-noetherian and applying it to A -> A/(a^m). Thus all hypotheses of both cotangent statements hold, and their A_m-linear isomorphisms transfer the SAME I^d from Step 5 to M_{i,m}. The inclusion a^d in I^d then finishes the step. There is no reflection through an arbitrary completion map.

Step 7 uses the other implication of the same uniform criterion, (iii) -> (i), for H=(a). Completeness, finite special fibre and the actual chosen presentation are from Step 2; the one bound for all m is from Step 6. It proves the last clause for the very presentation already constructed, not for an unspecified new algebra. Together with Steps 2 and 4 this proves every clause of the item.

I tested a=0: the repaired quotient transitions are isomorphisms, so F=C_1, and a positive a-power annihilates every module; no regular-element hypothesis is needed. For K=0, the given models already equal their completions and the argument still applies. For I=0, nilpotent ideals, I=A and the zero algebra, the completion and vanishing-locus assertions have their literal inverse-limit meanings; no excluded proper-ideal or nonzero-ring assumption is hidden. Rank zero polynomial presentations have the map J/J^2 -> 0, as required. The general conormal criterion permits zero or unit ideals; in those cases its annihilation conditions reduce respectively to zero-ideal annihilation or the zero complete algebra. For the narrowed ordinary-support helper, H=0 gives a zero ideal power annihilating every module; with H=A, etaleness everywhere makes both conormal cohomology modules zero. The inverse-limit lemma needs no flatness and allows torsion a; quotient transitions are its essential extra hypothesis.

For B1-B9, I checked statement-only helpers, complete introductions, inline descriptions of completed conormal differentials, definition dependencies, single TeX escaping, and exact Stacks tag/label attribution. For C1-C5, every non-elementary fact in the item's argument is the statement of a cited node and every cited statement was opened. citations.json copies their actual clauses verbatim. General completion and Noetherianity nodes are declared as generic tool uses; no unit step is replaced. For D1-D5, the argument is not “apply a new algebraization theorem”: the helpers are the independent compatibility, tower reconstruction, uniform conormal criterion, and ordinary conormal support/torsion fact, and the item constructs its completion map and proves the annihilator transfer. For E1-E7, I checked the quotient bases and ideals, used no regularity/excellence/flatness hypothesis, and repaired the false earlier tower inference with the explicit counterexample above. No non-elementary step exceeds 2000 characters.

I searched the whole DAG by the exact tags and by compatible tower, completed cotangent/conormal, uniform annihilation and topologically finite type notions. I ran blueprint_refs.py ancestor and searches for adic, rig-etale, topologically, cotangent, conormal, compatible finite type, tower and the relevant tags. No blueprint node states any new helper. Mathlib semantic searches were tried in two phrasings, together with Loogle and recorded grep searches. Hits included standard etale presentations, formally smooth lifting into complete rings, generic inverse-limit completion constructors, completion exactness/tensor product results and ordinary cotangent localization/support APIs. I read Smooth/AdicCompletion, AdicCompletion/Exactness and Noetherian, Etale/StandardEtale and Etale/Locus around the candidate declarations: these do not give the four asserted helpers as exact results or one-line specializations. In particular Algebra.etaleLocus_eq_compl_support (Etale/Locus.lean:58) supplies the cohomological vanishing locus, but not the finiteness and ideal-power annihilation assertion of the narrowed support helper. That assertion also requires finite-module support/annihilator and Noetherian finite-generation arguments; it is a genuine lemma, not the locus equality restated. Raw hits and unchanged query logs remain in the sandbox. There are zero Mathlib leaves.

## Not duplicates

lem-per-rig-etale-compatible-model-tower vs lem-per-rig-etale-principal-reduction: the helper constructs quotient-compatible finite-type models without conormal or rig-etale assumptions; it constructs neither the principal-complete algebra F nor its completion comparison or conormal bound.

lem-per-rig-etale-principal-tower-limit vs lem-per-completed-etale-jacobian-torsion: the helper reconstructs a ring from a quotient-compatible finite-type tower; the existing node starts with a finite module algebra over a complete base, etale away from the ideal, and proves a completed conormal bound.

lem-per-rig-etale-principal-tower-limit vs lem-per-jacobian-torsion-closed-base-change: the helper reconstructs an arbitrary principal quotient tower; the existing node transports one completed conormal torsion presentation along one closed base change.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-jacobian-torsion-etale-shrink: the helper gives a general uniform annihilation criterion and uniform bound across closed quotients; the existing node localizes a given finite type model to make its complement etale.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-rig-etale-principal-reduction: the helper concerns one general topologically finite type algebra and uniform cotangent tests under quotients; it constructs no compatible models, F, or map F -> E.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-principal-jacobian-algebraization: the helper gives uniform annihilation criteria without algebraizing any ring; the existing node produces a finite type model in the principal-ideal case.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-completed-etale-jacobian-torsion: the helper assumes no etale algebra or finite module algebra and includes detection from all truncations; the existing node starts with a finite algebra etale outside the ideal over a complete base and proves one conormal bound.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-jacobian-torsion-closed-base-change: the existing node has one quotient ideal and an exponent depending on that quotient and its topology. It gives neither one original-ideal power valid for all quotient ideals nor the converse uniform-truncation criterion; both are essential here.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-rig-etale-jacobian-algebraization: the helper is a cotangent annihilation criterion with no finite type model construction; the existing node algebraizes a completed rig-etale algebra.

lem-per-etale-supported-cotangent-completion vs lem-per-jacobian-torsion-etale-shrink: the helper assumes an etale complement and bounds ORDINARY finite-presentation conormal cohomology; the existing node deduces an etale complement after localization from a COMPLETED conormal bound.

lem-per-etale-supported-cotangent-completion vs lem-per-rig-etale-principal-reduction: the helper concerns ordinary finite-presentation conormal cohomology of one finite type algebra; it produces no principal-complete algebra, completion comparison, or compatible tower.

lem-per-etale-supported-cotangent-completion vs lem-per-completed-retraction-conormal-torsion: the helper bounds ordinary finite-presentation conormal cohomology of C/A; the existing node bounds the conormal module of the kernel of a retraction of completions, a different ring map and module.

lem-per-etale-supported-cotangent-completion vs lem-per-completed-etale-jacobian-torsion: the helper allows any finite type algebra and bounds its ordinary polynomial conormal cohomology without completing; the existing node assumes a finite module algebra over a complete base and concludes a completed torsion presentation.

lem-per-etale-supported-cotangent-completion vs lem-per-etale-away-completed-cotangent-torsion: the new helper bounds the uncompleted ordinary conormal modules of the finite type algebra C. The existing node bounds only the conormal cohomology of its completion. Completion is not faithfully flat globally, so the ordinary bound does not follow merely from the existing statement.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-etale-away-completed-cotangent-torsion: the new helper gives a uniform closed-base-change and truncation criterion for arbitrary complete topologically finite type algebras, without an etale finite type model. The existing node obtains one completed torsion bound from an etale-complement model, and has no uniform quotient/truncation criterion.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-completed-cotangent-transitivity: the new helper gives uniform annihilator criteria and transport of a common annihilator through all closed base changes. The existing node supplies the completed cotangent transitivity exact sequence and presentation independence, not those annihilator criteria.

lem-per-rig-etale-principal-tower-conormal-transfer vs lem-per-completed-jacobian-homology-comparison: the new helper detects uniform annihilation from ALL base-ring adic truncations and supplies a quotient-independent bound. The existing node compares completed modules from one ordinary presentation with a completed presentation of the same completed algebra, without these uniform truncation or base-change bounds.

lem-per-rig-etale-principal-tower-limit vs lem-per-completed-cotangent-transitivity: the new helper reconstructs a ring and polynomial presentation from a principal quotient-compatible tower; the existing node starts with complete algebras and gives a cotangent transitivity sequence, not quotient-tower reconstruction.

lem-per-rig-etale-principal-tower-limit vs lem-per-etale-away-completed-cotangent-torsion: the new helper starts with any quotient-compatible finite type tower and has no etale hypothesis or conormal conclusion. The existing node completes a single finite type algebra etale away from an ideal and bounds its conormal cohomology; it does not reconstruct an arbitrary tower.

The refreshed completed comparison node was reused, not duplicated. Its statement and that of lem-per-polynomial-conormal-completion were read in full. Neither was available at the earlier local snapshot; the second dry run exposed them. The final Step 6 names the former directly; the new support helper no longer asserts a completed-homology comparison.

lem-per-rig-etale-principal-tower-conormal-transfer vs def-per-completed-polynomial-conormal: the existing node defines the continuous differential and its domain/codomain; it gives neither a uniform annihilation criterion, a common annihilator over all closed quotients, nor detection on adic truncations. The definition is now explicitly reused as a statement dependency of the item and uniform criterion.

During the next server refresh, def-per-completed-polynomial-conormal appeared. I read its full statement: it defines the unique filtration-preserving continuous polynomial derivatives and their well-defined map on J/J^2. I added it as a statement dependency rather than defining a second construction. The item's formula already agrees with it. This changes no hypothesis or conclusion.

## Unfinished work

No part of this one-level split is left unfinished. The four new statement-only lemmas remain unsplit by the stage-1 contract, and will be separate queue items. Server dry-run and delivery results are reported by deliver.py.

The first server dry run returned only the four missing inline definition citations in the new helper statements. I added the definition-node references already listed in stmt_deps; no mathematical assertion changed.

## Resumed dry-run repair

The resumed dry run exited with two citation-shape failures: the compatible-model and tower-limit statements grouped every definition identifier inside a single bracket pair, so no individual identifier was recognized. I retained their mathematical statements and moved individual references beside the corresponding Noetherian, completion, finite-type, spectrum, etale and polynomial notions. No searches or earlier proof work were discarded.

The next resumed dry run exited without pushing and found two stale quotation strings in citations.json. I reopened the compatible-model and principal-tower-limit statements: their quotient-isomorphism and projection/presentation clauses still supply Steps 1 and 2 exactly. I copied their current statement text verbatim into the two citation entries; the only differences were the relocated inline definition references. No mathematical statement, proof, or recorded search changed.
