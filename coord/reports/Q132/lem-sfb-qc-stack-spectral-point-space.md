# Q132: lem-sfb-qc-stack-spectral-point-space

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qc-stack-spectral-point-space.json: item, split; statement unchanged. Four fresh logged Mathlib searches supplement the inherited records. No matching stack declaration.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-qc-inertia-dense-open-gerbe.json: new statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-gerbe-qc-diagonal-descent.json: new statement-only lemma, unsplit; no Mathlib match.
- citations.json: every proof-step citation, with a verbatim statement quote.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag, spectral-stack phrases, gerbe and algebraic-stack terminology. No declaration states this result. Scheme spectral-map and prespectral-space instances do not concern stacks. No Lean was written or compiled.

## WANTED

None. All needed Stacks sources are in literature/stacks-project/.

## Findings and route

The original item is correctly restricted to an affine base and requires only a quasi-compact relative diagonal, without the stronger quasi-separated-diagonal assumption. Its statement, statement dependencies and inherited provenance remain unchanged. There is no statement dispute.

I followed stacks-morphisms.tex Tag 0DQN, lemma-spectral-qc-diagonal-qc, reading its full proof. The compact-open argument uses affine smooth charts and the affine product over S. For sobriety I expanded construction of reduced closed support rather than citing lem-sfb-smooth-presentation-closed-subsets, whose statement is only over a field. I used the same source's gerbe reduction, but use the existing sobriety theorem for the quotient space (06NJ) instead of spectrality (0A4G). This avoids assuming that the dense open gerbe is quasi-compact. No result of the item is moved into a new node.

The two new lemmas are respectively 06RC (proposition-open-stratum) and 0DQL (lemma-gerbe-diagonal-quasi-compact). I read both statements and their proofs in stacks-morphisms.tex, and the gerbe universal-homeomorphism statement 06R9. The 0DQL argument is relative to the common scheme S: its cartesian square and fppf-local descent use products over S. The first new lemma defines the inertia as the pullback of the relative diagonal and defines gerbe explicitly. The second defines gerbe again and only asserts descent of the relative diagonal. Neither lemma asserts spectrality or generic points.

## Searches

Read every msearch.py result, including both semantic phrasings for each new lemma, Loogle and grep. All succeeded. Loogle found no Gerbe or AlgebraicStack declarations; Mathlib grep found no gerbe/open-stratum or gerbe-diagonal declarations. Semantic hits concern schemes: QuasiCompact, QuasiSeparated, spreading out, dominant maps, flatness and open maps. I opened Morphisms/QuasiCompact.lean and Morphisms/QuasiSeparated.lean to check the types: their source and target are Scheme, not algebraic stacks. The spectral search returned the abstract SpectralSpace constructor, scheme prespectrality and scheme spectral-map statements, not the item. All new-node searches are recorded verbatim from the sandbox searches.jsonl; none was invented or copied from another group's log.

Searched the whole DAG's statements, titles, tags 06RC and 0DQL, generic-point/gerbe/reduced-support and affine-atlas concepts, and the project Lean sources. Ran blueprint_refs.py searches for spectral, gerbe, 06RC, 0DQL, algebraic space and reduced. None of the imported blueprint statements gives the new lemmas. The broad spectral/reduced hits concern schemes, topological spaces or cohomological spectral sequences. Existing gerbe and singleton lemmas have different hypotheses/conclusions as explained below. blueprint_refs.py ancestor reports that the inherited blueprint.from.node is None. This is the existing creation-chain situation, also documented in the reviewed topology dependency; I preserve it and extend the explicit place and via chain for the new nodes. I read the current latest blueprint proof sk-thm-sf-ctf-stability-direct-images.proof.md paragraph (3), and the chapter/unit records. This is a foundational prerequisite below its alteration/moduli route, not a change of route.

## Not duplicates

lem-sfb-reduced-qc-inertia-dense-open-gerbe vs lem-sfb-reduced-singleton-qc-diagonal-gerbe: the existing lemma assumes a reduced singleton stack over a field with quasi-compact diagonal and gives a gerbe over a field spectrum; the new lemma treats arbitrary reduced stacks with quasi-compact inertia, over any scheme, and only gives a dense open gerbe over an algebraic space. Neither assertion is a one-line specialization giving the other.

lem-sfb-gerbe-qc-diagonal-descent vs lem-sfb-reduced-singleton-qc-diagonal-gerbe: the existing singleton result produces a field gerbe and does not assert descent of quasi-compactness of a diagonal along an arbitrary given gerbe; the new lemma assumes a gerbe to an algebraic space and proves that its base has quasi-compact relative diagonal.

The item and lem-sfb-qc-diagonal-stack-spectral share Tag 0DQN, but that existing node is over a field, and uses the field-only smooth-presentation topology node. It cannot establish this item's affine-ring-base statement. I do not create a second stack spectrality lemma. The existing lem-sfb-gerbe-smooth-universal-homeomorphism has no diagonal-descent clause and is reused only for its explicit homeomorphism. The existing lem-sfb-flat-inertia-algebraic-space-quotient assumes everywhere flat locally finitely presented inertia and has no dense-open existence conclusion; the new dense-open lemma supplies the missing generic-flatness input.

lem-sfb-reduced-qc-inertia-dense-open-gerbe vs lem-sfb-universally-closed-stack-rational-point: the existing theorem assumes a nonempty universally closed stack over an algebraically closed field, with quasi-compact separated diagonal, and concludes existence of a rational object. It does not assert a dense open gerbe for a reduced stack with quasi-compact inertia.

lem-sfb-gerbe-qc-diagonal-descent vs lem-sfb-universally-closed-stack-rational-point: rational-point existence over an algebraically closed field does not assert diagonal descent for an arbitrary given gerbe over a space. The new lemma has neither universal closedness nor a field-base assumption.

## Review by Q132

I checked delivery-errors B–E against the node files and the source paragraphs, including the second copy of B–E in the historical new-target section. Both new nodes are self-contained statements, with explicit gerbe, reducedness/inertia or relative-diagonal hypotheses, no proof sketches, correct Stacks labels and single TeX escapes. Their dependencies define the notions actually used. No elementary topological implication became a node. Both lemmas are genuinely smaller source inputs and neither restates a spectrality clause.

Step 1 uses the affine-atlas equivalence in lem-sfb-algebraic-stack-quasicompact-surjection, the continuity and surjectivity clauses in lem-sfb-stack-point-topology, smooth-implies-flat-and-lfp in the chart calculus node, the open-map clause of lem-sfb-stack-point-topology-flat-lfp-open, and quasi-compactness of affine schemes. Each statement explicitly supplies that claim. No finite type or separatedness is inferred.

Step 2 applies the affine open covering theorem to arbitrary open subschemes, giving a basis, and the existing affine-scheme compactness theorem to their images. Openness and continuity were proved in step 1. The smooth-open-image theorem supplies algebraic open substacks when needed. Finite subcovers use only quasi-compactness. This is the elementary cover-and-image argument written in the step, not a hidden lemma.

Step 3 uses the affine tensor-product description and affine compactness for B times_S C. The base S is affine exactly here. The scheme-as-space definition and space-source representability theorem give the algebraic space B times_X C. The stack quasi-compactness definition applies to this pullback of the diagonal. Its quasi-compact atlas has a continuous surjective point map by the topology theorem. I wrote out point-surjectivity onto the intersection using the defining common field extension and isomorphism; no uncited cartesian-points theorem is assumed. Arbitrary compact opens are finite unions of those chart images, so finite distribution finishes the intersection argument.

Step 4 checks C4 carefully: the existing smooth-presentation closed-support statement has only a field base, so I did not use it. The space reduced-closed-support lemma gives the actual reduced closed subscheme D in A and uniqueness on the relation H; the chart calculus supplies smooth projections H to A. Both inverse images of D are reduced by the smooth-reduced-locality lemma and have equal support because the two maps to the stack are isomorphic. Thus their equality as closed subspaces is justified, and the invariant-closed-substack descent theorem gives Z with precisely atlas D. The closed-immersion calculus theorem identifies its point space homeomorphically with the closed subset T. Every fact is in the cited statements, rather than inside their proofs.

Step 5 writes the diagonal base-change equivalence on objects and isomorphisms. It applies to closed and open full substacks. Stability of quasi-compactness follows by composing the test fibre products in its definition. The inertia is explicitly that diagonal's self-base-change, so the reduced stack Z satisfies exactly the hypotheses of 06RC. The new dense-open gerbe lemma is used only for the open gerbe, without inferring quasi-compactness of that open.

Step 6 uses the arbitrary-base gerbe universal-homeomorphism statement with identity base change, the new 0DQL lemma for the relative diagonal, and lem-sfb-quasiseparated-space-sober, whose statement explicitly accepts this scheme-test diagonal hypothesis over a scheme. Since the dense open subset of T is nonempty and irreducible, its quotient is nonempty and irreducible; sobriety then gives its unique generic point. There is no appeal to Noetherianity or to spectrality of a non-quasi-compact open.

Step 7 expands the closure and uniqueness arguments: all generic points of T must belong to the same nonempty open, where uniqueness holds, and the dense open's generic point has closure T. The spectral definition supplies exactly the four assembled conditions.

I tested the empty stack (no nonempty T, empty atlas/cover allowed), schemes as stacks, a field spectrum, a reduced gerbe over a non-quasi-compact space, and non-Noetherian affine bases. The gerbe descent lemma has no quasi-compactness assumption on source or target; it is diagonal descent, not a conclusion about the space itself being quasi-compact. The dense-open lemma allows empty source and needs reducedness, retained explicitly. I checked the two new nodes' dependencies do not lead back to the item, and the existing reused topology/space nodes are not its descendants. Each proof step is under 2000 characters. I generated citations.json from the exact statements read; each quote covers the assertion used.

## Unfinished work

None for this one-level split. The two new unsplit nodes are future work by design. No Lean or compiler actions are authorized in this stage.
