# Q160: lem-sfb-adequate-moduli-universal-closed-topology

## Files written

dag/nodes/sec-six-functors-basics/lem-sfb-adequate-moduli-universal-closed-topology.json — item, statement, split. Its mathematical statement and existing provenance are unchanged. The repaired proof has three steps and no dependency on lem-sfb-adequate-moduli-topological-images.

dag/nodes/sec-six-functors-basics/lem-sfb-adequate-base-change-affinization.json — new statement-only input, unsplit, no Mathlib match: the canonical affinization factorization after arbitrary base change (Alper Proposition 5.2.9(3)).

dag/nodes/sec-six-functors-basics/lem-sfb-adequate-closed-substack-affinization.json — new statement-only input, unsplit, no Mathlib match: closed-substack affinization and its universal homeomorphism onto the scheme-theoretic image (Alper Lemma 5.2.11).

There are two new nodes and zero Mathlib leaves. citations.json has one exact statement quotation for every step/node pair. searches.jsonl retains the old receipts and appends the actual new searches. The old proof, report and citations are retained in work/retained-* in the sandbox as superseded review material; only the current files above are delivered.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for adequateModuli, adequate_moduli, adequate moduli, adequatelyAffine and adequately affine. No project declaration states the item or either supporting factorization. Scheme relative-spectrum constructions are not the stack theorem.

## Wanted literature

WANTED: Alper, Adequate moduli spaces and geometrically reductive group schemes, published Proposition 5.2.9(3), p.509; Lemma 5.2.11, p.510; Theorem 5.3.1(1),(2), p.511; Definition 3.3.1, for this item and its two new nodes. The local source path literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf is absent. I read the published primary PDF online at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf, including the proof of Theorem 5.3.1 and Example 5.2.10. Nothing was downloaded or written outside the sandbox. Accordingly proof_origin remains agent, with the source and the expanded argument recorded.

## What changed and what was wrong

The current return says the landing refused a two-node cycle. The required initial dry run reproduced exactly this finding. On the current DAG, lem-sfb-adequate-moduli-topological-images now has a three-step split whose first step depends on this item; its statement is unchanged, but its proof is no longer an independent black box. Retaining the old specialization proof would be circular even though every statement quote remains valid. I removed that citation completely and reconstructed the proof from the two genuinely algebraic inputs used by Alper. No other worker's file is changed.

The proof first establishes surjectivity for EVERY adequate map, rather than invoking the item recursively. It uses the field-base-change factorization and condition (1): the fibre cannot be empty because its global ring is the nonzero ring of an affine space homeomorphic to the spectrum of a field. It next establishes closedness for EVERY adequate map by applying this already-proved surjectivity to a closed substack's adequate affinization, whose image is a closed subspace. Finally it applies these two general conclusions to the adequate factor of the arbitrary base change. The final homeomorphism preserves both properties. Thus the two new nodes concern algebraic factorizations; neither says that an adequate map is surjective or closed. The actual topology theorem is proved in the item, not moved to either new node.

I also re-read the changed/current statements and proofs of lem-sfb-smooth-presentation-closed-subsets and def-sfb-adequate-moduli-space. The smooth-presentation node supplies reduced closed substacks and point conventions; its image/base-change clause was the subject of an earlier repair but is no longer needed for surjectivity here. The adequate definition includes BOTH the structure-sheaf isomorphism and the full power-lifting condition on all affine etale charts; the proof uses its structure-sheaf clause explicitly and the new lemmas assume this exact adequate-moduli notion. No flatness or diagonal-separation condition was introduced.

The latest blueprint is literature/blueprint/latest at 7284bb09daf97437d544c51882b325f9c52cd345. I read its chapter section and direct-images proof (3), plus the DAG chapter and unit records. The current high-level proof uses the proper and open cases, whereas the inherited provenance follows the older auxiliary projective-moduli route. I retain that provenance and the existing split_report.blueprint explanation; this repair establishes its generic topology input without changing any unit step. blueprint_refs ancestor prints None for this item, so both new nodes have from.node=null and via consisting of this item followed by its inherited via. Searches over the whole imported blueprint for adequate, adequate homeomorphism, closed substack and relative spectrum found no node stating either factorization.

## Not duplicates

lem-sfb-adequate-base-change-affinization vs lem-sfb-adequate-flat-base-change: the existing node assumes flatness and quasi-compact separated diagonals and concludes that the projection itself is adequate; the new node allows arbitrary base change and constructs a different adequate target with a universal homeomorphism to the new base. Example 5.2.10 shows why these are different statements.

lem-sfb-adequate-base-change-affinization vs lem-sfb-adequate-moduli-etale-locality: etale locality does not supply the arbitrary nonflat-base-change affinization or its universal-homeomorphism comparison.

lem-sfb-adequate-base-change-affinization vs lem-sfb-adequate-moduli-universal-closed-topology: the item concludes surjectivity and closedness of point maps; the new node only constructs and identifies the algebraic factorization. It does not assert either topology conclusion for its adequate factor.

lem-sfb-adequate-base-change-affinization vs lem-sfb-adequate-geometric-fibres-submersion: a quotient topology and orbit-closure equivalence do not give the relative spectrum, quasi-coherence of its algebra, or the adequate factorization.

lem-sfb-adequate-closed-substack-affinization vs lem-sfb-stack-schematic-image-qc: the existing node constructs a closed scheme-theoretic image with dense point image; it does not construct an adequate map from the closed substack to its relative spectrum or a universal homeomorphism onto that image. Density alone does not give surjectivity.

lem-sfb-adequate-closed-substack-affinization vs lem-sfb-adequate-moduli-topological-images: the existing statement gives closedness and an intersection identity; it gives no quasi-coherent algebra, relative spectrum, or adequate factorization. In addition its current proof depends on this item, so using it would recreate the returned cycle.

lem-sfb-adequate-closed-substack-affinization vs lem-sfb-adequate-moduli-universal-closed-topology: the new statement supplies the algebraic construction preceding the topology proof, and does not state surjectivity or closedness of an adequate point map.

lem-sfb-adequate-closed-substack-affinization vs lem-sfb-space-relative-spec-correspondence: relative spectra alone do not imply adequacy or that the spectrum is universally homeomorphic to the closed image. The correspondence is cited for the meaning of the construction.

lem-sfb-adequate-base-change-affinization vs lem-sfb-adequate-closed-substack-affinization: the first changes the BASE by an arbitrary morphism; the second changes the SOURCE to a closed substack. Each supplies a different non-elementary input of Alper's proof.

Whole-DAG searches by the literature places 5.2.9, 5.2.11, adequate homeomorphism and by factorization/relative-spectrum concepts found the comparisons above and generic scheme results, with no node stating either new theorem. The nodes have the same chapter and unit as the item; no off-route tool is needed.

## Review by Q160

I checked delivery-errors B–E against the actual files and sources. Both new nodes have complete self-contained statements, empty proof/proof_deps and null proof_origin; they introduce their field, stacks, spaces, morphisms and algebras and cite the definitions of each. The universal-homeomorphism property is written out for arbitrary algebraic-space base change instead of leaving an undefined reference to adequate homeomorphism. Relative spectra are specified by the existing space-relative-spec node. They are not elementary two-line consequences: Proposition 5.2.9(3) depends on the algebraic power-lifting comparison, and Lemma 5.2.11 depends on the closed-substack quotient-algebra comparison. Neither just restates a clause of the item.

For the first new node I read Proposition 5.2.9(3), printed p.509: its target is Spec_T(f_*O), its first map is adequate and its second is an adequate homeomorphism. The latter is in particular a universal homeomorphism, the only aspect retained here. There is no flatness hypothesis on part (3); part (1), which concerns preservation of adequacy of the projection itself, DOES have one and is not used. For the second I read Lemma 5.2.11, p.510: specialize its quasi-coherent algebra to the algebra of a closed substack. It states exactly that Z maps adequately to Spec_Y(j_*O_Z) and that this space maps by an adequate homeomorphism to the scheme-theoretic image. Its kernel describes the closed image; no topological surjectivity has been assumed.

Step 1 uses the first new statement for the factorization and the homeomorphism, def-weil-affine-spectrum for the affine ring and one-point field spectrum, def-sfb-adequate-moduli-space for O_H = a_*O, and def-sfb-stack-quasi-coherent-algebra for evaluation on H and the compatible-family description of sections. I opened every statement: they give these precise assertions. Over a field the relative spectrum is affine, as stated in the relative-spectrum convention of the new input. If a stack has no field-valued points, its smooth scheme atlas has no points and hence is empty. Every object scheme mapping to the stack is then empty (a nonempty scheme has a residue-field point). A section family over only such objects has a single element, so its ring is zero. This supplies the nonemptiness argument hidden in Alper's short proof. The algebraic-stack fibre-product node guarantees that the fibres and the base-changed stacks are algebraic. I did not use a topology theorem about adequate maps to prove their surjectivity.

Step 2 uses the smooth-presentation statement's exact clause that every closed subset is the support of a reduced closed substack, then the second new statement's adequate map and universal homeomorphism onto W. Step 1 is already quantified over ALL adequate maps, including this one. The closed-immersion-calculus statement explicitly gives the homeomorphism onto a closed subset for W into V, including when these are algebraic spaces regarded as stacks. Thus the image equals all of |W|, rather than merely being dense. This is the exact distinction needed for C4.

Step 3 uses the first new factorization for the original arbitrary T. Its H is an algebraic space over k, so the preceding two general arguments apply to its adequate factor. The map H to T induces a homeomorphism; surjectivity and preservation of closed sets under composition are elementary. No assertion that X_T to T is adequate occurs, and no Noetherian, finite-type, reducedness, characteristic or inertia restriction is used. Every step is under 2000 characters. The proof has no induction, recursive use of the item or hidden comparison identification.

I tested the empty stack/empty target case, the empty base change, the identity adequate map, empty and full closed substacks, and a nonreduced base. An adequate map to a nonempty field cannot have empty source, precisely by step 1's nonzero-ring argument. For the identity map the first comparison is the identity; for an empty closed substack the second uses the zero algebra and empty closed image. In positive characteristic the comparison may be a nontrivial universal homeomorphism, which is allowed; Example 5.2.10 verifies that it must not be promoted to an isomorphism. None of these cases changes the theorem or requires a rational point over a residue field.

For each new node I ran and read LeanFinder twice with different phrasings, Loogle, grep and LeanSearch via the prescribed msearch.py. I retained the receipts exactly in searches.jsonl and recorded those exact query texts in the corresponding mathlib_searches fields. The hits concern affine scheme spectra, integrality, scheme base-change stability or scheme universal closedness. I re-read Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean:35–50: UniversallyClosed quantifies over schemes and presupposes the closed-map property. Neither it nor the returned general scheme spectra facts proves the adequate-moduli stack constructions. No unavailable service was called a no-match, and no search was invented. The item's earlier two-phrasings searches are retained because its statement and search question did not change.

## Repair of the refused landing

Return: NOT MERGED; check_dag reports the cycle between lem-sfb-adequate-moduli-topological-images and this item. The initial no-push invocation exited with that same failure. The repair changes all three proof steps, the proof dependency union, proof_origin, split_report.summary, the report and citations, and adds the two searched statement-only algebraic inputs. It removes the reverse edge completely. I re-read the current cited statements and the now-dependent topological-images proof rather than relying on the older report. This is a mathematical reconstruction of the split, not an unchanged rebase or re-push. The delivery tool rebases it onto the current DAG in its own worktree; no git command was run in the shared repository.

## Unfinished work

The two supporting statements are deliberately unsplit and join the stage-1 queue. Nothing is claimed proved in Lean. No Lean was written and no compiler, Lake or build tool was run. The shared repository and launcher were read only. The mandatory server dry run and delivery are the final checks for this repaired item.
