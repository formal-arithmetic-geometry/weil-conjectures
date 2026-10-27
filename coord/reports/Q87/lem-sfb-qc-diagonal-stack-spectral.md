## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qc-diagonal-stack-spectral.json: split statement; specializes the already existing affine-base spectrality node and derives the Kolmogorov consequence. Mathlib searches found no stack theorem.
- citations.json: seven verbatim statement excerpts for the seven step/node pairs.
- searches.jsonl: five searches actually run for this item, including two different semantic phrasings. Read every returned hit.

No new nodes; zero new Mathlib leaves. No Lean files written and no compilation performed.

## Attachments

None. Searched WeilConjectures for the exact blueprint id, AlgebraicStack, algebraic stack, and spectral-space notions. There is no project declaration covering algebraic-stack spectrality. Scheme and abstract spectral-space declarations do not attach this item.

## WANTED

None. All sources used are in literature/stacks-project/.

## Corrections and reuse

The statement is unchanged and is correct. The imported node had no proof. The whole-DAG tag/keyword search found lem-sfb-qc-stack-spectral-point-space, an existing strictly more general theorem over an affine scheme. Reused that node rather than create a duplicate or a node repeating a clause. Its statement supplies every spectrality clause under the exact relative-diagonal hypothesis. Its unsplit status does not prevent citing its theorem statement in this one-level DAG split.

The topology cited in that existing node is lem-sfb-stack-point-topology, whereas this item cites lem-sfb-smooth-presentation-closed-subsets. Their statements explicitly use the same field-point equivalence and atlas quotient topology; step 2 gives the closed-inverse-image comparison, without reading an unstated construction from either proof. The two nodes do not impose a different topology or stack class.

No statement dependency was removed. No original search record was deleted. Five new searches were recorded exactly as run by msearch.py; all services answered. Loogle returned SpectralSpace.mk, SpectralSpace.toCompactSpace and Topology.IsOpenEmbedding.spectralSpace. LeanSearch and LeanFinder returned those or scheme-only facts. Read Mathlib/Topology/Spectral/Basic.lean, Prespectral.lean and AlgebraicGeometry/Morphisms/QuasiCompact.lean: these facts assume the topology properties we need to establish, or have scheme source/target, and do not prove the stack theorem. In particular there is no one-line Mathlib specialization with stack input.

The nearest blueprint ancestor command reports None, consistent with the inherited from.node = null. Retained that provenance and its existing exact place, with same_as = []. Blueprint searches for spectral and quasi-compact diagonal found no blueprint theorem for this stack assertion. Read the latest chapter and unit text and the latest sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). The legacy unit record has a different chapter path; this foundational topology result remains below the already specified alteration/moduli prerequisite chain and does not replace a unit step.

## Not duplicates

No new nodes were created. In particular, the existing lem-sfb-qc-stack-spectral-point-space already covers the spectrality assertion over an arbitrary affine base; this delivery uses it directly. lem-sfb-quasiseparated-space-sober concerns algebraic spaces and sobriety only and is not needed. No duplication is introduced.

## Review by Q87

I read the complete proof of Stacks Tag 0DQN, lemma-spectral-qc-diagonal-qc, and its 0DQQ corollary in stacks-morphisms.tex, including the reduced-closed-substack reduction, dense gerbe stratum, and quasi-separated-space argument. The source does not require finite type, Noetherianity or separated diagonal. The general affine-base node already packages precisely this theorem, so the correct split here is a specialization, not a fresh collection of its own clauses. I read its entire statement and traversed its statement/proof dependency closure (9894 nodes); our item is not in that closure, so the new citation creates no cycle.

Step 1 uses the actual statements of def-weil-field, def-weil-affine-spectrum and def-sfb-stack-qcqs-morphism. A field is a commutative ring, its spectrum is affine by the spectrum definition, and the given atlas is exactly the definition of stack quasi-compactness. I checked that the diagonal is relative to Spec k on both sides: no absolute-diagonal conversion, quasi-separatedness inference, finite-type inference or separatedness assumption is used.

Step 2 uses the full spectrality conclusion of lem-sfb-qc-stack-spectral-point-space and the topology statements of lem-sfb-smooth-presentation-closed-subsets and lem-sfb-stack-point-topology. The former assumes an affine base, which Spec k is; the atlas and diagonal hypotheses match literally. Both topology statements use field maps modulo common-extension isomorphism, and both declare the atlas quotient topology. Equality follows by testing closed sets on one and the same atlas. Each of the three statements says exactly the part taken from it; their verbatim excerpts are in citations.json. The target's uniqueness of generic points, compact-open basis, intersection property and compactness all follow directly, with no hidden gerbe lemma used in this specialization.

Step 3 uses the sobriety clause in def-weil-spectral-space as instantiated in step 2. I wrote out why topologically indistinguishable points have the same singleton closure, why this closure is irreducible and nonempty, and why uniqueness then equates the points. This is an elementary consequence, not a new theorem about stacks.

I checked the B--E return checklist against the node and sources: no new self-containment or definition issue; no unrun searches; no tag used as a substitute for a cited node; no citation to a proof-only construction; no cycle; no unsupported hypotheses; no new node restating the item. The pre-existing general result is reused as required by the duplicate rule. Every step is under 2000 characters and the assembly proof is under 3000 characters. Tested the empty stack (vacuous sobriety and T0, compact empty space), a one-point scheme, a nonreduced affine scheme, and a classifying stack over a field with quasi-compact affine group: none requires a new hypothesis. This specialization never uses a finite-type atlas. No SGA source, disputed statement or route change is involved.

## Unfinished

Nothing remains for this one-level split. Proof of the already-existing general affine-base theorem remains its own DAG item; it was not duplicated here.
