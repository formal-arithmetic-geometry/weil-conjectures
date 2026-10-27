# Q10 stage-1 report: lem-sfb-relative-smooth-subgroup-normalizer

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-smooth-subgroup-normalizer.json: item, seven proof steps; statement retained, source page range corrected to include printed p.63.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-section-finite-jets.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-section-universal-jet-density.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-source-factorization-locus.json: statement-only, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-connected-subgroup-noetherian-model.json: statement-only, unsplit; no Mathlib match.
- citations.json: verbatim cited statements indexed by proof step.
- searches.jsonl: actual results of the prescribed msearch.py searches. No searches invented or copied from a different item's log.

## Attachments

None. Searching WeilConjectures/ by the blueprint id and normalizer/transporter notions finds the abstract GL vanishing-ideal normalizer lemma and its monodromy application, not the relative group-scheme assertion. They do not prove this item. Sheaf/ normalizer declarations concern groups over fields and are not upstream attachments.

## Literature

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed pp.57--63, for the item and all four supporting nodes; local archival path literature/conrad-reductive-group-schemes.pdf is absent. I read the primary PDF online, including Proposition 2.1.2, Lemma 2.1.3 and their proofs, Proposition 2.1.6 and its full proof, and Definition 2.1.7. Following the worker brief's rule for absent local documents, proof_origin.by is agent, with the precise online source recorded. No download or repository write was made. No SGA source is used.

Conrad gives no Stacks tag for this specialized relative normalizer statement. The noetherian model node isolates the reduction stated on printed p.62 (EGA IV 8.3.3, 9.7.9, 17.8.7), including the descent of group diagrams explained on p.57. The finite-jet node isolates pp.62--63. The density node isolates the assertion and proof on p.63, rather than treating pointwise or geometric-fiber density as universal schematic density. The finite-source node is the family pullback of the closed Hom-functor immersion in the proof on p.60, using the coefficient construction of Lemma 2.1.3, pp.58--59. These are four genuinely separate inputs, not a new transporter or normalizer theorem.

## What was wrong or changed

No mathematical error in the item was found, and no hypothesis or conclusion was changed. The original source range pp.61--62 did not cover the last and essential universal-density argument on p.63; the range is corrected. The original statement-only node had no proof. I used both conjugation directions, so I do not need to assume or cite the nontrivial assertion that a finitely presented scheme's monic endomorphism is an automorphism. Nor do I impose flatness on the normalizer: Conrad's Example 2.1.10 explains why that would be false in general.

The newest blueprint is literature/blueprint/latest (main-20261024). I read its sk-thm-sf-ctf-stability unit and the direct-images proof (3). The item remains a generic group-scheme prerequisite on its existing alteration/moduli/root-theoretic chain. tools/blueprint_refs.py ancestor reports None for this seeded chain; I preserve that existing null ancestor and its full provenance rather than inventing an imported ancestor. Keyword searches of the whole blueprint for normalizer, smooth section, infinitesimal neighbourhood, factorization locus, finite locally free, and Noetherian approximation found definitions or unrelated applications, not an existing statement of these four inputs.

## Not duplicates

lem-sfb-smooth-section-finite-jets vs lem-weil-pbc-etale-infinitesimal-neighbourhoods: the existing lemma detects etaleness near a closed subscheme from infinitesimal restrictions; it does not prove that neighborhoods of a smooth section are finite locally free.

lem-sfb-smooth-section-universal-jet-density vs lem-sfb-constant-source-closed-factorization-locus: the existing lemma uses a constant source over a field, whereas the new density assertion is for a varying smooth family over a Noetherian ring and arbitrary nonflat test schemes.

lem-sfb-finite-locally-free-source-factorization-locus vs lem-sfb-constant-source-closed-factorization-locus: the existing statement assumes a field, a constant source and finite-type parameter; the new statement allows a relative finite locally free source and arbitrary parameters over a scheme and asserts finite presentation of the closed immersion.

lem-sfb-finite-locally-free-source-factorization-locus vs lem-sfb-multiplicative-type-transporter-smooth: that result concerns conjugation between multiplicative-type subgroups and its smoothness, not arbitrary families of morphisms from a finite locally free scheme to a closed target.

lem-sfb-smooth-connected-subgroup-noetherian-model vs lem-sbc-pointed-smooth-family-stage: descent of a pointed smooth family over its prescribed approximation does not supply simultaneous affine group and closed subgroup models with descended multiplication, inverse, inclusion, and all geometrically connected subgroup fibers.

lem-sfb-smooth-connected-subgroup-noetherian-model vs lem-sbc-affine-section-noetherian-descent: descent with a section does not descend a closed subgroup inclusion together with the group operations and geometric connectedness of every subgroup fiber.

No new node has a Stacks tag colliding with an existing node. The overlapping Conrad Proposition number is a source location, not an assertion that any new node states that whole proposition. None of the four states a normalizer representability conclusion or one of its clauses.

## Review by Q10

I checked the files against delivery-errors B--E with the actual source PDF and cited node statements open. Every new statement introduces its base, schemes, morphisms and test category. The jet definitions use explicit affine quotient rings; geometric connectedness and Noetherianity are spelled out or defined by cited nodes. The supporting nodes are statement-only with empty proof and proof_deps. Searches include semantic searches, Loogle and logged Mathlib grep; the second semantic formulations are retained. Mathlib's Algebra.Smooth.exists_subalgebra_fg at Mathlib/RingTheory/Smooth/NoetherianDescent.lean:214 was read in source. It descends one smooth algebra only: no Hopf operations, compatible closed subgroup, or connected-fiber assertion, so the model node is not a one-line specialization of it. Other hits concern abstract group normalizers, scheme normalization, formal unramification or general finite presentation and do not state our nodes.

Step 1 uses exactly the new simultaneous-model statement; its isomorphisms preserve group operations and the subgroup inclusion, and its model is Noetherian. This is not an unjustified reduction on the representability functor: the actual transfer back to the original base is proved on all tests in Step 7.

Step 2 uses the finite-jet statement for finite local freeness and base-change identification, and the universal-density statement for the closed-subscheme test. Their smoothness, affine finite presentation, section, Noetherian-base and geometric connectedness hypotheses all hold for H_0 from Step 1. Infinitesimal neighborhoods need not be subgroup schemes; no step treats them as such.

Step 3 uses the multiplication and inverse already specified in the item, writing each conjugation map as their composition, and the exact universal property of the new finite-source factorization-locus node. I checked def-sc-group-scheme: its literal statement is over a field. It serves only as the diagram template in the item's explicit base-relative definition; I removed it as a proof citation so no field-based theorem is applied over A_0. D_n is finite locally free by Step 2, G_0 is affine and finitely presented by Step 1, and H_0 is a finitely presented closed target. Both positive and negative conjugation families are tested. There is no assumed smoothness of their parameter loci.

Step 4 uses def-weil-closed-immersion for the affine quotient descriptions; lem-weil-pbc-closed-immersion-base-change for the inverse images of H_0 under the two conjugation morphisms; and lem-weil-pbc-scheme-morphism-gluing for unique local quotient lifts on arbitrary tests. The ideal-sum calculation is written out: a ring map annihilates the sum if and only if it annihilates every summand. The universal density result already established in Step 2 upgrades both jet containments to full scheme containments. Applying c_g to the inverse containment supplies equality. This is an elementary assembly of established statements, not a replacement density lemma.

Step 5 uses pqf-lem-affine-open-locnoeth exactly for Noetherianity of C_0, not merely Noetherianity of its spectrum; the model has a locally Noetherian total scheme. def-weil-pbc-noetherian-ring gives finite generation of I, lem-weil-pbc-lfp-affine-opens-finite-presentation gives the affine algebra presentation of C_0 over A_0, and lem-weil-pbc-finite-presentation-quotient-fg-ideal gives that of C_0/I. It also displays the finite presentation of the closed immersion itself. No unsupported inference from a topological finite intersection is used.

Step 6 uses the full Yoneda evaluation statement lem-pc-yoneda, not merely full faithfulness of a particular representable embedding. Products and inverses preserve the equality condition by the displayed conjugation identities. The closed immersion is monic by the equivalence in lem-pc-proper-monomorphism-closed; that statement does give monicity for a closed immersion. Group laws can therefore be checked after inclusion into G_0. For the canonical H_0 inclusion, quotient-ring surjectivity proves closedness using def-weil-closed-immersion. There is no need to prove the normalizer flat.

Step 7 uses lem-weil-pbc-closed-immersion-base-change for closedness and the ring-level clause (1) of lem-weil-pbc-finite-presentation-base-change-composition for the two affine finite presentations. I checked this is a ring-level statement and applied it on affine coordinates, rather than pretending it directly states a general scheme theorem. The model's conjugation formula is unchanged on every S-scheme, so its base-changed scheme really represents the original functor. The same all-test identification gives arbitrary further base change. Yoneda yields the canonical isomorphism, with inverse constructed by evaluating the inverse natural transformation. No cofinality or small-index assumption is hidden here.

The generic off-unit affine algebra, gluing and Yoneda tools are declared in split_report.tool_uses with their purposes. They do not replace a step of the unit route. All proof citations have their actual verbatim statements in citations.json; I checked that their scope supplies the facts used as described above.

Small cases: if H=1 then every jet is S and the constraints vanish, so N=G; if H=G they vanish as well. A zero base ring gives the empty scheme and all functor assertions are still valid. Relative dimension zero with connected smooth nonempty fibers is compatible with the identity-section construction. Nonreduced and nonflat tests are retained both in the density node and in the factorization universal property. The density hypothesis is essential: for a disconnected smooth source, the jets at one section need not meet another component. None of the new statements drops connectedness where density uses it. I reviewed all step lengths: each is below 2000 characters, and no standard comparison or auxiliary lemma is concealed in a long step.

## Unfinished work

No unfinished part of the item's split. The four supporting statements are intentionally unsplit stage-1 queue items. No Lean was written and no compiler, Lake or build command was run. Required dry run and direct delivery follow this report.

The first server dry run passed (79f9f850f6b). A final citation-scope audit then removed the unnecessary field-based definition citation from Step 3 as explained above; the final dry run is rerun on that correction before push.
