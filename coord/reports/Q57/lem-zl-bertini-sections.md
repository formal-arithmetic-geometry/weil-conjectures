# Q57: lem-zl-bertini-sections

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-bertini-sections.json`: statement, split into ten proof steps; no Mathlib match for the whole assertion.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-immersion-cancellation.json`: statement-only Mathlib leaf, `AlgebraicGeometry.IsImmersion.of_comp`, `Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:218–220`.
- `dag/nodes/sec-deligne-laumon-general/lem-zl-immersion-near-image-locality.json`: statement-only Mathlib leaf, `AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`, `Mathlib/AlgebraicGeometry/Morphisms/Basic.lean:169–185`, specialized to immersions using the local-at-target and composition instances in `Immersion.lean:111,138–146`.
- `citations.json`: one verbatim statement quotation for each of the 30 step/node citations. Some quotations include several clauses because the step needs more than one clause.
- `searches.jsonl`: the search command's existing log, retained. The UTC search date is 2026-10-17; this machine's calendar date is 2026-10-18.

## Attachments

None. Searched the item tag and its mathematical notions in the project source under `WeilConjectures/`, and inspected the existing Bertini and section-avoidance material. `Bertini.lean` states the parent curve-section input with sorry; the closed point-avoidance statements are only partial inputs. No project declaration proves every clause of this item. The project uses Mathlib's cancellation and generic locality declarations elsewhere; those uses do not themselves state either new lemma generally. Upstream master is reference material, not evidence of a finished proof.

## WANTED

None. All sources used are available locally.

## Corrections and interpretation

The item's mathematical statement is unchanged. The imported node had no proof. I follow the current blueprint's parent proof, its first invocation of Stacks 0FD5, rather than any purity or SGA route.

## Source error

There is a minor source typo in the proof of Stacks 0FD5: after choosing the generation bound n_1, its later chosen s_1 is written as belonging to V_1, but the displayed degree n=n_1+n' requires V_{n_1}. My proof avoids that typo. Fix one very ample power L^r, and for each n choose the vanishing section in V_{n-r}. The uniform generation bound gives it for all n at least a+r. This is the same product-of-sections proof and does not change the theorem or its hypotheses. The current `def-sc-ample.blueprint_update` allows any embedding with pulled-back O(1); the older complete-system definition also supplies such an embedding in this proper setting.

Instead of introducing a node for the source's final abstract ring-image lemma, I construct the chart map q explicitly from polynomial coordinates and apply immersion cancellation. This uses the same products (s_1 t_i)/(s_1 t_j) as the source. The new nodes are the general cancellation and target-locality facts, not the generation or immersion clauses of the item. No node is introduced for elementary restriction, rank-one tensor calculations, or subspace finite dimensionality.

## Unfinished work

None in this one-level split. Stage 2/3 and the proofs of reused DAG tools remain outside this assignment. No Lean file, live project file, launcher file, or unit record was changed; no compiler, Lake, build tool, or git command in the shared repository was run.

## Not duplicates

lem-zl-immersion-cancellation vs lem-cbc-qc-immersion-cancellation: the existing statement assumes the second map separated and the composite a quasi-compact immersion, and concludes quasi-compactness as well; the new statement has neither hypothesis and concludes immersion only. The existing lemma therefore does not supply the unrestricted cancellation used here.

lem-zl-immersion-cancellation vs lem-weil-pbc-closed-immersion-cancellation: the existing statement is Tag 07RK(3), closed-immersion cancellation with separated second map; this is Tag 07RK(1), unrestricted immersion cancellation.

lem-zl-immersion-cancellation vs lem-weil-pbc-closed-immersion-from-composite: likewise the existing node concerns closed immersions and a separated second map, not general immersion cancellation.

lem-zl-immersion-cancellation vs lem-pc-complete-linear-system-closed: the latter constructs the closed immersion from the complete system when a finite subsystem embeds; its proof cites 07RK(3), but its statement is not the cancellation theorem.

lem-zl-immersion-cancellation vs lem-weil-pbc-closed-subset-proper-over-base-universally-closed-image: the latter is about the image of a closed subset in a proper-family argument; 07RK occurs in its proof, not as its statement.

lem-zl-immersion-cancellation vs lem-weil-pbc-finite-separable-base-refinement: the latter is about base refinement of finite separable data, with 07RK used only in its proof; it states no general immersion cancellation theorem.

lem-zl-immersion-near-image-locality vs lem-sc-ample-proj-open: the existing statement concerns an open immersion into the section-ring Proj of an ample bundle; its proof's use of target-locality is not a statement of target-locality for an arbitrary morphism.

I searched the whole DAG for 07RK, 0FCZ, the declaration names, cancellation and immersion locality, and used `tools/blueprint_refs.py search` for both source labels and equivalent notions. Neither new statement is already a blueprint node; `same_as` is empty. Both new nodes point through this item to the blueprint ancestor `lem-zl-bertini-finite-cover-curve`, specifically its first geometric-input paragraph invoking 0FD5.

## Review by Q57

I read the item directly in `literature/stacks-project/varieties.tex`, label `lemma-generate-over-complement` (0FD5), including its last ring-image argument. I also read the current blueprint parent's proof under `main-20261015`: the input is precisely generation and an immersion off the prescribed finite subscheme, before its separate smoothness and irreducibility arguments. For the cancellation leaf I read `morphisms.tex`, `lemma-immersion-permanence` (07RK), part (1), and Mathlib `Immersion.lean:218–220`. No separatedness is required. For locality I read `morphisms.tex`, `lemma-check-immersion` (0FCZ), and `Basic.lean:169–185`; Mathlib's local-at-target instance is at `Immersion.lean:111`. The generic theorem's extra RespectsRight hypothesis follows immediately by composing an immersion with an open immersion, using the Mathlib composition instance at 138–146 and open-immersion-to-immersion at 132. The project also has this exact auxiliary instance in `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:53–59`; the match does not assume a new geometric theorem absent from Mathlib.

For each proof step I opened the statements of every cited node. My check of what each actually supplies is as follows.

1. `def-sc-ample` supplies a positive very ample power, and its current update supplies the embedding interpretation. `lem-weil-pbc-projective-ample-invertible` explicitly asserts absolute ampleness of the pulled-back O(1), not just relative ampleness. `def-weil-pbc-ample-invertible-module` has exactly quasi-compactness and affine nonvanishing neighborhoods of positive-power sections; replacing a degree d by rd therefore verifies the required absolute ampleness without invoking an unrecorded power-invariance theorem.
2. `def-weil-proper-morphism` includes finite type. `lem-weil-pbc-finite-type-over-noetherian` applies over Spec k, which is Noetherian, giving the locally Noetherian hypothesis. `def-sbc-closed-immersion-ideal-sheaf` explicitly says I is quasi-coherent. Rank-one local freeness gives finite type for the structure sheaf and powers of L. `pqf-lem-coherent-ft-locnoeth` then supplies coherence, and part (2) of `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` says precisely that a quasi-coherent submodule of a coherent module is coherent. This is not an inference that the definition of an ideal alone implies coherence on every scheme.
3. The ideal definition gives the restriction kernel sectionwise. With an invertible sheaf locally generated by e, the restriction kernel consists of ae with a in that ideal; this proves the tensor identification and injectivity, including on a nonreduced Z. On U the ideal is O. Thus this elementary step does not silently use a general tensor-exactness theorem.
4. The twist-generation node needs an absolutely ample bundle and a finite type quasi-coherent module, both established above; its statement gives a uniform bound for every degree beyond it. Restricting a generating family works stalkwise. The proper coherent-cohomology node states finite H^0 over a Noetherian affine base, and L^d has been shown coherent. Finite dimensionality of its kernel is ordinary linear algebra; no vanishing H^1 or surjectivity of the restriction map is needed.
5. The projective-map definition accepts any finite generating family and gives the coordinate map over the base. A basis of V_n generates because its constant span contains the finite generating family from step 4. The chart-preimage node gives both the full inverse image and coordinate ratios. I also cite the projective-space functor-of-points theorem for existence and uniqueness: the new linear forms generate O(1) because the inverse matrix recovers the original coordinates; its coordinate maps are inverse by uniqueness. Choosing a basis containing a particular nonzero s therefore changes only coordinates, with the required maps actually constructed. I made the empty-source case explicit using the definition of a closed immersion, instead of assuming a nonempty basis for V_n in that case.
6. The standard-chart node asserts coverage and identifies coordinate pullbacks. The generation-in-fibres node applies to a finite basis of V_{n-r}, so some s_1 is nonzero at x. The tensor/pullback node explicitly gives compatibility of sections with restriction and the product formula in fibres. A product with a section vanishing on Z again vanishes on Z. Over each residue field the two fibres are lines, giving exactly Y_s=Y_{s_1} intersection Y_{t_j}. This uses no rational-point, smoothness, or reducedness assumption.
7. Part (c) of the standard-chart statement is the polynomial coordinate-ring isomorphism needed for D(T_j). On D(s), each product v_i is an element of the finite-dimensional V_n, so its ratio is a linear polynomial in chart coordinates. The universal property of a polynomial algebra and the bijection in `lem-weil-pbc-morphism-into-affine-scheme` construct q. I do not assume every map to affine space is a closed immersion, or that an arbitrary image-subring argument gives a surjection.
8. The chart-preimage node gives the pulled-back ratios. After trivializing the two line bundles the cancellation of s_1 is literally cancellation of the chosen basis 1, not cancellation of an arbitrary zero divisor. The standard-chart statement identifies j's ratios, and the affine-morphism bijection identifies the two morphisms from equality on the polynomial generators and on k. Thus qh really is the required restricted j.
9. Part (b) of the permanence node explicitly includes base change of closed immersions; part (e) explicitly includes composition of immersions. The definition of immersion includes open and closed immersions by using identity factors. These show the composite qh is an immersion before cancellation is applied. The new cancellation node then concludes exactly that h is an immersion, with no extra hypothesis on q.
10. The chosen target opens cover the image, rather than merely forming a cover on the source. Their full inverse images are Y_s. The locality leaf therefore applies to those precise restrictions and concludes immersion of the original morphism. The bound n>=a+r gives both inequalities used in the proof, with no assertion about degrees below it.

I checked B–E of `coord/delivery-errors.md`: both new statements introduce all objects and cite their definitions, have only statements and no hidden proof dependencies, and have explicit source tags and read Mathlib file/line matches. Their searches were run with the mandated search command, including both semantic services, Loogle and grep; the whole item was searched under two distinct phrasings before concluding absence. I retained all prior searches on the item. I did not record an unavailable service as a failed mathematical search. Existing same-tag nodes were compared by statements, as listed above. All off-unit theorem tools are declared in `split_report.tool_uses`; they supply generic coherence, generation, proper finiteness and coordinates, without replacing the parent unit's geometric route. The item itself carries the products argument, so neither new node repackages one of its clauses. No proof step exceeds 2000 characters, and I inspected each step for concealed comparisons: the only two general immersion lemmas are the new cited leaves, while the local rank-one and polynomial-coordinate calculations are written explicitly.

Small cases checked: Y empty; Z=Y (including a nonempty proper scheme, when V_n=0 and the source complement is empty); Z empty (I=O and the products recover the usual ample-power immersion); a nonreduced closed subscheme, where membership in the full ideal rather than set-theoretic vanishing is essential; finite and nonperfect fields; and dimension-zero schemes. Neither leaf needs quasi-compactness or a separated ambient scheme. In the locality leaf an empty indexing family forces X empty, and the conclusion still holds. In the cancellation leaf identity maps give the expected special cases. The product proof is scheme-theoretic throughout and imposes no smoothness, geometric irreducibility or infinite-field hypothesis.
