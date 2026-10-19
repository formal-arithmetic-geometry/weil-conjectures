# Worker report

Group Q96; item lem-pur-etale-rho-monoidal-mate; stage 1; 2026-10-18.

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-rho-monoidal-mate.json: statement, split; no Mathlib match. The statement and original ancestry/created metadata are unchanged.
- No new nodes and no new Mathlib leaves.
- citations.json: a verbatim quotation for each of the 27 step/node citations.
- report.md; searches.jsonl is the search command's own log. Local preparation scripts are sandbox-only aids, not delivery files.

## Attachments

None. I searched the project Lean source under WeilConjectures for the exact blueprint tag/id and for normalized exceptional comparison, rho/monoidality, and projection-mate terms. There is no exact project declaration for this item. The upstream-master checkout was treated only as reference, not as evidence of proof.

## WANTED

None.

## Findings and changes

The item had an explicit, typed definition of kappa but no proof. The current main-20261015 sk-thm-regular proof, Step 4(ii), gives the etale-local smooth-purity comparison but does not supply this tensor-mate calculation. I expanded that missing calculation and marked the proof as agent-written. No statement correction or route change is made. The proof uses the normalized counit, not merely an unspecified natural isomorphism Re! ≅ Le*.

The inverse-twist formula is first reduced to the transpose (epsilon_K tensor 1) PF(GK,N)^(-1). This also proves its independence from inverse data. The Hom chain then identifies its closed-immersion inverse with the existing co-projection. The etale identity follows from the specified projection site comparison, the proper-support/sum projection comparison, the fold-counit tensor identity, and an explicit equality of transposes.

## Mathlib and duplicate searches

I read the item's inherited searches and ran two phrasings with each of LeanFinder, Loogle, LeanSearch and source grep through msearch.py. All services answered successfully. The first semantic query returned Over pullback coherence and scheme-module comparisons; the second returned mateEquiv_counit and monoidal-adjunction counit identities. The Loogle queries returned monoidal adjunction structure lemmas or zero hits. Source grep returned rigid dual mates and general tensor/monoidal definitions. I read the relevant generic rigid-functor and monoidal-functor source. These do not state this normalized etale compact-support comparison; in particular the sum-extension left adjoint is not a tensor-preserving monoidal functor. Exact queries/results are in the node and command log; I did not record a failed service as absence.

Whole-DAG keyword/id searches and blueprint_refs searches for rho monoidal mate, projection, and etale sum led to existing projection/sum/site-comparison nodes. I reused them, especially lem-asd-etale-sum-extension-tensor, whose statement already includes the derived fold-counit identity. Creating a new node for that identity would have duplicated it. The item's same_as remains empty: no blueprint node states the normalized rho/kappa identity. No new-node duplicate pairs arise.

## Review by Q96

I read the chapter and sk-thm-regular unit and the current blueprint proof in full, particularly Step 2's Hom/co-projection convention and Step 4(i)-(ii). I also read the current sk-lem-coprojection Hom proof. The Stacks sources opened were more-etale.tex, Tags 0GKF (lemma-f-shriek-projection, its pure-tensor map), 0F4Y (lemma-separated-etale-shriek), and 0GKM (lemma-Rf-shriek-for-quasi-finite). These justify the sum/proper-support route of the existing interfaces; none is claimed to state the entire item's mate identity. No SGA route is used. No new nodes need separate source or small-case audits.

I opened the statements of every cited node. Here is the mathematical check of the steps against those statements:

1. The exceptional definition explicitly supplies constructible and finite-Tor preservation and transported etale adjunctions. lem-sf-pullback-tor-amplitude supplies the pullback domain and lem-sf-tensor-ctf(ii) supplies the tensor domain. lem-sf-proetale-constructible-origin(ii) gives bounded constructible etale origins, and lem-sf-comparison-tor-amplitude(ii), not a mere comparison definition, reflects finite Tor amplitude. thm-weil-pbc-site-comparison is fully faithful on D+, which includes every bounded object used here. lem-weil-finite-compact-projection-formula then applies to M=GhK and H=N with exactly its bounded-constructible/finite-Tor hypotheses. The field-base hypotheses in the exceptional definition give Noetherian schemes for the later sum-support lemmas.

2. lem-pur-finite-projection-action-laws(3) explicitly states the compactification tensor-action law, rather than only the proper version. I apply it to N,N' and contract their evaluation. lem-weil-pbc-ringed-projection-mate-exact explicitly says the proper projection at the unit is the identity; the open factor is the tensor-unit instance of the formula in def-exchange-projection. Inserting the tensor-adjunction unit and using its triangle identity recovers exactly T PF(N)=1. The invertibility proved in Step 1 identifies T with PF(N)^(-1), so the formula is independent of the inverse data. The unit is the coherent adjunction unit specified by the item's conjugate description, not an independently chosen symmetric cup; this matters for odd shifts.

3. pur9-cs-def-invertible gives precisely the inverse object and evaluation; pur9-def-upper-shriek-composition specifies the actual exceptional adjunction bijection. For the Hom chain I take bounded constructible finite-Tor test objects, so all its projection and adjunction domains are valid. The displayed Hom chain spells out the tensor-adjunction and exceptional-adjunction transformations, including the direction of precomposition with PF(N'). The statement of lem-pur-coprojection explicitly defines the closed-immersion comparison through this inverse-twist projection; reversing that chain identifies its inverse with kappa. I did not use a hidden argument from that node's proof as a new fact.

4. lem-weil-pbc-comparison-pullback identifies the exact inverse images, and the ringed-topoi tensor-pullback theorem supplies the tensor comparisons. Crucially, lem-pur-projection-comparison-etale-origin states equality of the actual proper/open projection maps, with M bounded constructible and H finite Tor. Those hypotheses were checked in Step 1. The exceptional definition transports the adjunction and lem-pur-finite-etale-dualizing-normalization characterizes rho by the transported sum/evaluation counit. Substitution therefore compares the actual transposes, and full faithfulness transfers their equality. I do not use stalkwise testing to assert equality of derived morphisms.

5. lem-sfb-quasifinite-compact-support-exact explicitly covers separated etale finite-type maps and identifies the compact-support functor with the exact sum extension. lem-amb-etale-adjoint-locality gives S left adjoint to e*, on entire ordinary etale derived categories. lem-pur-etale-support-map-compatibility(2), not a definition of PF alone, gives the displayed projection compatibility with d. The normalization node explicitly supplies rho's counit-preserving characterization, which yields epsilon S(rho) d = varepsilon. The schemes are Noetherian, e is separated finite type, and the coefficient ring is finite, as required by all three interfaces.

6. lem-asd-etale-sum-extension-tensor states both its tensor comparison and its fold-counit identity on arbitrary unbounded complexes. I specialize B=N, C=K and use canonical symmetries to put N on the right. The inverse comparison r agrees with the inverse of the p in Step 5 by the same lift-indexed pure-tensor rule in lem-pur-etale-support-map-compatibility(2). This is just the two directions of that termwise tensor comparison. The equality is already a derived identity in the cited node, so there is no uncited passage from stalks or from cohomology to equality of morphisms.

7. The written three-line equation uses Step 6, naturality of r, and exactly the two equalities in Step 5. Its source is F(GK tensor PN) and its target is K tensor N throughout. The final cancellation uses the injective Hom bijection from lem-amb-etale-adjoint-locality and rho's counit normalization, both of which are stated by the cited nodes. This proves the specified rho/kappa equation, rather than just that kappa is an isomorphism.

8. Only inverse composition and multiplying the equation are used; it is elementary. rho and mu are the specified isomorphisms from the statement, so all factors and the equivalent coProj equation have the displayed domains.

I checked B–E of delivery-errors point by point: there are no new statement-only nodes or fabricated searches; no statement is relabelled as a child; all non-elementary inputs have the cited statements just described; no citation uses only a definition for a theorem; no circular dependency on the item was found in the existing dependency closures of the substantial tools. All steps are under 2000 characters, so none hides a separately stated comparison in a long paragraph. The off-unit citations are declared as generic tools in split_report.tool_uses; they do not replace the unit's smooth-purity/diagonal/DNC route.

Small cases checked were e=id, an open immersion, a finite disjoint union of copies of X, the empty source, N=A, and N=A[1] with inverse A[-1]. For the disjoint union, both transposes fold the same summands; for the empty source both maps are zero. For the identity and open maps the equation is the ordinary tensor comparison. Odd shifts use the same signed symmetry on both sides and the tensor-adjunction triangle identity, so no even-degree assumption on N is added. Inverse evaluation rescaling cancels in Step 2. I corrected the preliminary wording of inverse-twist cancellation to specify the coherent tensor-adjunction unit, avoiding an ambiguous symmetric-cup convention.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own statuses. No Lean was written or compiled, no Lake/build tool was run, and no shared project or launcher file was changed.
