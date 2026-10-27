# Q24 stage-1 report

Item: lem-trf-excellent-blowup-projective-transforms

## Files written

- dag/nodes/sec-trace-formula/lem-trf-excellent-blowup-projective-transforms.json: statement, split into five steps; not a Mathlib leaf.
- citations.json: 16 exact statement excerpts, one for every step/node citation.
- report.md and searches.jsonl: review and actual searches. prepare.py is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the blowup, excellence, Rees and projectivity notions. No declaration states all clauses of this item. Existing affine blowup, relative-Proj and H-projective APIs cover only portions and do not justify ATTACH.

## WANTED

None. All sources used are in literature/stacks-project.

## Corrections and scope

The item's mathematical statement is unchanged. It was statement-only; its source gives the intended route. Added missing statement dependencies for the finite-type quasi-coherent ideal, sheaf Rees algebra and affine blowup chart ring. The projective-bundle convention for the blowup remains distinct from the finite-projective-space convention for X and Y. No globally free presentation of I is presumed.

Read the current chapter and unit records, the inherited blueprint ancestor and the flatification parent's split. These five steps supply the ordinary blowup input of the parent's step 2, at the recorded local-term-locality alteration/nearby-cycle ancestor. No chapter/unit route changes and no unit realized fields are needed: this item is not the key statement of the unit. Blueprint searches for blow, projective, excellent, 07QU, 02NS, excellent blowup, blowup projective, symmetric and chart cover, plus the full-DAG statement/source searches, found the existing tools used here and no blueprint statement of this whole conjunction. Retained all original fields and earlier Mathlib searches.

## Mathlib searches

The search command recorded LeanFinder twice with different phrasings, LeanSearch, Loogle, and two source greps. Read the returned types: IsIntegralHom concerns an integral morphism, not an integral blowup scheme; normalization is a different construction. The general Proj properness results do not give excellence or the specified blowup embeddings. Loogle found no excellence declarations. Source grep finds only incidental English mentions of excellence/blowup, and the Rees algebra definition at Mathlib/RingTheory/ReesAlgebra.lean:39. Thus the whole item is not a one-line Mathlib specialization. The earlier N5 searches remain intact; no new-node searches are claimed.

## Not duplicates

No new nodes. Reused lem-sfb-integral-blowup-chart-density, lem-sfb-sheaf-rees-symmetric-presentation and lem-sfb-rees-presentation-blowup-immersion instead of creating parallel nodes for their shared Tags 0804/02NS. Reused the already existing excellence and closed-immersion tools too. The existing lem-sfb-integral-blowup-projective-geometry and lem-per-integral-blowup-projective-geometry state only integrality and projective-bundle projectivity, not the whole item. Rather than duplicate them or package the item's clauses into new nodes, the proof carries the density/topology and Proj assembly explicitly.

## Review by Q24

I read Divisors Tag 0804 (lemma-blowing-up-affine), Tag 02ND (lemma-blow-up-integral-scheme) and Tag 02NS (lemma-blowing-up-projective), including its actual Sym-to-Rees proof, and Algebra Tag 052R (lemma-blowup-domain). I read More on Algebra Tag 07QU (lemma-finite-type-over-excellent), and Morphisms definition-excellent and Tag 0HAB (lemma-locally-excellent). For the final embedding I read Morphisms Tags 01QR and 01QS (base-change-closed-immersion and composition-closed-immersion) and the H-projective definition. No SGA route is used.

Step 1 uses the full statement of lem-sfb-integral-blowup-chart-density. It supplies the affine restriction identifications, finite generator chart cover, empty zero charts, domain/nonzero charts, nonempty integral centre complement, and density on each chart. The item's integral S and nonzero finite-type quasi-coherent I meet all its hypotheses: I cannot be zero because it is unit on nonempty U. The only further ring comparison is the explicit injective map from A localized at a nonzero a_j into its fraction field, whose kernel calculation is written. In particular I did not cite a definition of the chart for its cover/density theorem.

Step 2 reads thm-nagata-global-blowup-complement for the isomorphism on the actual centre complement W, not merely the originally supplied U. Together with step 1 this proves density, reducedness and irreducibility; the proof writes out why two nonempty opens intersect and uses the equivalence in def-pc-integral-scheme to conclude integrality. This is a short elementary topological assembly, not a new lemma. lemma-nagata-blowup-proper explicitly assumes only the finite type quasi-coherent ideal available here and states properness. def-weil-proper-morphism really includes finite type, so lem-weil-pbc-finite-type-over-noetherian applies with the global Noetherian S and yields global Noetherian T, not just local Noetherianity. Properness is not inferred from the finite-space projectivity lemma, which would use the wrong convention.

Step 3 uses lem-trf-excellent-scheme-affine-cover on the excellent affine cover of S to justify the ring hypothesis on affine opens and again on the constructed cover of T. It uses precisely the finite-type-algebra consequence in lem-exc-finite-type-localization-excellent with multiplicative set {1}. Its finite generation is written out with x=sum c_i a_i, so this does not silently assert that a general subalgebra of a finite type algebra is finite type. Excellence is being checked on affine neighbourhood rings, not only stalks, and zero-generator charts are discarded as empty. These hypotheses agree with the sources, including quasi-coherence for ideal restriction.

Step 4 reads the statements of lem-sfb-sheaf-rees-symmetric-presentation and lem-sfb-rees-presentation-blowup-immersion. The former supplies every affine identification, degree-zero identity, restriction compatibility and degreewise-surjective graded map required by the latter. The latter explicitly gives the ordinary-blowup/relative-Proj isomorphism and the induced closed immersion with structural composite v. This avoids using an isomorphism or map found only inside another node's proof. def-trf-projective-bundle-morphism then applies with the finite-type quasi-coherent module E=I. This is an assembly of the actual graded map and chart-compatible identification, not an appeal to a new restatement of projectivity.

Step 5 reads def-kun-projective, lem-weil-pbc-closed-immersion-base-change, lemma-nagata-projective-space-base-change-pullback and lem-weil-pbc-closed-immersion-comp. They state respectively the finite-space embedding, its stability under arbitrary base change, the projective-space cartesian square for every base morphism, and closure under composition. Thus the same finite N works for Y after base change. No excellence, integrality, flatness, or finite presentation is imposed on Y; its given closed immersion is sufficient. The argument constructs an embedding rather than confusing the two projectivity definitions.

The generic algebraic-geometry results from other units are declared individually in split_report.tool_uses where they are neither Mathlib leaves nor Lean-closed. They are tools below the unit's alteration route, not alternate trace-theorem routes. I opened each cited node's statement; citations.json contains a verbatim relevant substring for each of the original 15 uses (16 after the repair below), checked against those files.

I checked delivery-errors B--E: no new statement-only node is needed, none merely restates a clause, every non-elementary step has nodes with the exact required assertions, and none of the argument is hidden in a cited proof. The five steps are each under 900 characters; there is no long step concealing another lemma. Small cases: I=O_S gives the identity blowup, r=1 with nonzero generator also gives the expected identity chart A, repeated/zero generators add harmless repeated/empty charts, and the zero ideal is excluded by nonempty U on an integral scheme. The empty affine of S has empty inverse image, so no fraction field of the zero ring is used. Empty Y has an empty closed embedding in the same projective space. The proof never assumes affine intersections are affine, a global set of ideal generators exists, or a blowup is flat.

## Unfinished work

None for this one-level split. The reused unsplit tool nodes remain their own future items. Delivery checks and push follow this report.

## Validation

The first dry run required three citation excerpts to be expanded to at least 40 characters. I replaced those short excerpts with their full node statements and rechecked literal containment. The next deliver.py --no-push exited 0 and printed OK (not pushed) at 103bea1232d: server preflight, check_dag and review_split passed. No mathematical correction was required by these diagnostics.


## Repair of the 2026-10-22 return

The return names branch head f25dd006ee4 and says that the reader approved the mathematics but landing refused the side-project completion because the live DAG still had the item unsplit. I retained that returned split, report, citations, and all six logged searches. I compared its sandbox node field by field with the current repository node: the mathematical statement, source, creation stamp, chapter, unit, and blueprint ancestry agree; the live node still has status unsplit, empty proof/proof_deps and null proof_origin. The delivery changes are precisely the split fields (proof, proof dependencies/origin, the three added statement dependencies, recorded searches, status, and split_report). No released repair note exists locally. The prescribed deliver.py dry run fetched the current origin/sheaf-dag and rebuilt the overlay on that base; it exited 0 at 00ca5e33334 before I made the repairs below. The tool preserves current upstream metadata rather than restoring stale sandbox metadata.

This is a repaired split, not an unchanged re-push. Step 1 now explicitly records that W is dense in S, an assertion supplied by the current chart-density statement and used for birationality in step 2. Step 3 now cites def-nagata-blowup-chart-ring at the exact use of its generation-by-fractions definition, which previously appeared only among statement dependencies. I regenerated citations.json with the full current statement for each of the resulting 16 step/node uses, making the complete hypotheses and conclusions available in the delivery evidence. The item's mathematical statement and the five-step proof route remain unchanged.

### Review by Q24 of the repair

I reread all 15 previously cited node statements, not just excerpts, as well as the newly explicit definition citation. In step 1 the current lem-sfb-integral-blowup-chart-density states that the centre complement is nonempty, dense, and integral, that the local ideals are nonzero, and that the chart identifications respect affine restriction. Thus density in S is available, and the hypothesis that I is nonzero follows from its unit restriction on nonempty U. Zero generators give empty charts and do not require a fraction field of the zero ring. In step 2 thm-nagata-global-blowup-complement gives the actual centre-complement isomorphism; def-pc-integral-scheme gives the reduced-plus-irreducible characterization; lemma-nagata-blowup-proper needs exactly the finite-type quasi-coherent ideal at hand; def-weil-proper-morphism supplies finite type; and lem-weil-pbc-finite-type-over-noetherian gives global Noetherianity, including quasi-compactness. All of these current statements still support the retained argument.

In step 3 the current affine-cover excellence lemma gives excellence on every affine open from the specified cover; the finite-type-localization excellence lemma applies with multiplicative set {1}; and the newly explicit chart-ring definition says that the fractions x/a generate the algebra, exactly what the displayed finite-generator calculation needs. In step 4 I checked both current Rees-presentation statements: the first supplies degree-zero identity, coefficientwise restriction and degreewise surjectivity; the second assumes these same compatibilities and supplies the unique blowup/relative-Proj identification and the particular closed immersion induced by the given map. Its statement explicitly identifies the composite with the blowup structure map, so no construction hidden in its proof is borrowed. The projective-bundle definition allows E=I without a globally free presentation. In step 5 the current finite-space projectivity definition, closed-immersion base-change and composition lemmas, and projective-space cartesian-square statement provide precisely the same-N embedding over T. Their hypotheses do not require v flat or Y nonempty.

I reopened the source text for Divisors Tags 0804, 02ND, 02NS, Algebra 052R, More on Algebra 07QU, and Morphisms 0HAB, 01QR, 01QS and 01T6, together with definition-excellent. These confirm the retained chart, symmetric-to-Rees, excellence and embedding arguments. There are no new nodes or source requests. The earlier source and duplicate review above remains applicable. I reread delivery-errors B through E: new-node form, duplicate and Mathlib-leaf gates are vacuous for this repair; the one previously implicit definition citation is now explicit; every other non-elementary assertion is still in its cited statement; all five steps remain below 2000 characters. The unit/chapter route remains the flatification input under the recorded nearby-cycle ancestor. I rechecked I=O_S, a single nonzero generator, zero or repeated generators, and empty Y; none invalidates the argument. No hypothesis or conclusion changed and no statement dispute was found.
