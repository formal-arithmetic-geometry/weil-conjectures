# Q27 stage-1 delivery: lem-sfb-kodaira-vanishing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kodaira-vanishing.json: item split into five proof steps; statement and statement dependencies retained. Not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-kollar-smooth-divisor-injectivity.json: one new statement-only lemma; no Mathlib match, no proof or proof dependencies.
- citations.json: verbatim statement quotations for every step/cited-node pair.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, Kodaira, and the injectivity terminology. No project declaration states this item, nor the new injectivity input. Ordinary cotangent and canonical-map injectivity hits are unrelated. No Lean was written, compiled or built.

## Wanted literature

WANTED: Mihnea Popa, Kodaira dimension of algebraic varieties, section 1.6 opening paragraph (printed p.22), Theorem 1.6.6 with its proof (pp.26--27), and the proof of Theorem 1.6.1 using it (pp.27--28), for lem-sfb-kodaira-vanishing and lem-sfb-kollar-smooth-divisor-injectivity; suggested local filename literature/popa-kodaira-dimension.pdf. Author PDF read online at https://people.math.harvard.edu/~mpopa/271/Kodaira-posted.pdf. No copy is present in the named local literature tree, and workers may not download there or change LIST.md. The split is therefore explicitly agent-written. The existing local Milne iAG2017, Theorem 22.51, printed p.480, was read; it invokes Kodaira but does not prove it. No SGA source is used.

## Findings and corrections

The original item is mathematically correct and is not weakened. It had no proof. Its use for flag varieties needs the theorem over arbitrary algebraically closed characteristic-zero fields, not just the complex numbers. Popa's section 1.6 opening explicitly extends its results to these fields. The new injectivity node therefore states that field generality; any future split of that node must expose the field-of-definition/base-change reduction if it uses the complex proof. There is no assumption that F embeds in C.

I followed Popa's injectivity-to-vanishing argument, not a replacement of Kodaira by an equivalent vanishing leaf. The new node concerns a multiplication map, permits arbitrary invertible L without ampleness, and has no vanishing conclusion. Its hypothesis is a chosen smooth zero divisor of a power. The actual item proof makes that section using Bertini, chooses the power large enough for Serre, and then uses injectivity into zero. Thus its argument is not delegated in full to a restatement of the item.

The online proof of 1.6.1 has a minor typographical omission: it says that L is very ample for m sufficiently large. It is the power L^m which must be very ample; the next sentence uses |mL|. Our split uses the existing stronger sections/immersion lemma for A^m, so neither the item nor a new node asserts ampleness implies very ampleness without taking a power. Also I imposed m>=2 on the injectivity input, sufficient for this proof and consistent with the nontrivial eigensummand in the cyclic-cover proof. Dimension zero and empty smooth zero schemes are explicitly included.

The inherited blueprint.from.node is null. tools/blueprint_refs.py ancestor lem-sfb-kodaira-vanishing prints None. I preserved the inherited item ancestry and used the same null ancestor for the supporting node, prepending the item to its via list. The inherited place already records the full direct-image/alteration/moduli/reductivity/flag chain. I read the current latest blueprint direct-image statement/proof and its unit. The node-level Kodaira proof adds no unit or chapter route change.

## Searches and nonduplication

I searched the full DAG and blueprint for Kodaira, canonical bundle, injectivity, cyclic cover, and Bertini, and searched the project Lean by the item tag and notions. The canonical-bundle blueprint hit is a degree formula for curves, not this injectivity statement. Existing Serre and Bertini nodes are reused. Searches of the whole DAG for Kollár/Esnault–Viehweg injectivity and the proposed id found no matching statement. Generic multiplication, torsion, germ and localization injectivity nodes do not say this. Blueprint searches found no injectivity theorem for canonical-bundle cohomology.

All new-node Mathlib queries were actually run through msearch.py and are in searches.jsonl, including two distinct LeanFinder phrasings, Loogle, LeanSearch, and source grep. I read every returned hit. Cotangent H1 injection, germ injectivity, scalar multiplication on torsion-free modules, and Ext via injective resolutions do not give this geometric injectivity theorem. The item searches likewise found no Kodaira vanishing. Existing mathlib_searches on the item were retained. No Mathlib leaf is claimed.

## Not duplicates

No existing node has the statement of the new node. The new node's source has no Stacks tag, so there are no new/existing same-tag pairs. In particular, lem-sfb-kollar-smooth-divisor-injectivity vs lem-sfb-kodaira-vanishing: the former states injectivity for a specified smooth divisor and an arbitrary line bundle, whereas the latter states vanishing for an ample line bundle with no specified section. The proof still needs Serre and Bertini. Neither is a clause copied from the other.

## Review by Q27

I checked B--E of delivery-errors.md against the node files and the actual source statements. I read local Milne 22.51 p.480 and online Popa section 1.6 p.22, Theorems 1.6.1 and 1.6.6 and their proofs, especially the final injectivity-to-vanishing assembly. I also read the local Stacks source for the smooth differential lemma (02G1, morphisms-lemma-smooth-omega-finite-locally-free), coherent closure (01Y0, coherent-lemma-coherent-abelian-Noetherian), Serre (02O1, coherent-lemma-kill-by-twisting), and Bertini (0FD5, varieties-lemma-generate-over-complement; 0FD6, varieties-lemma-bertini). The new node is exactly the supporting smooth-divisor injectivity theorem, restricted to m>=2 and with its objects and tensor/cohomology maps specified; it does not carry an inline proof.

For step 1 I opened lem-pc-projective-proper: it supplies properness from the actual projectivity assumption. I opened lem-trf-proper-field-invertible-coherent: with N=O_Y it supplies Noetherianity and coherence of O_Y, not coherence of an arbitrary sheaf. I opened lem-ag-smooth-relative-differentials-finite-locally-free: it supplies finite local frames, without requiring a constant-rank assertion. Wedges of those frames give finite local frames of omega in every exterior degree. The finite-sum clause of lem-weil-pbc-coherent-kernel-cokernel-locnoeth gives coherence on these open restrictions. pqf-def-coherent supplies the local definition to glue this conclusion. This avoids taking an unjustified canonical-bundle coherence theorem from a definition node, and avoids silently identifying pure dimension with differential rank. Exterior basis bookkeeping is elementary and written explicitly, not made into another node.

For step 2 I opened lem-weil-pbc-coherent-serre-vanishing: its coefficient really may be any coherent module, so it applies to omega by step 1, over the Noetherian ring F with the proper structural morphism and ample A. I opened lem-zl-bertini-sections: it gives generation and immersion for every sufficiently large power after putting Z=empty. The same power is chosen >=2 and with m+1 above the Serre threshold. I opened lem-pc-projective-coherent-finiteness: it gives finite-dimensional H0, after lem-trf-proper-field-invertible-coherent supplies coherence of A^m. The cited ample definition explicitly supplies invertibility of nonnegative tensor powers. These results are used only for what their statements give; no construction from their proofs is used.

For step 3 I opened lem-zl-bertini-smooth-member: the finite-dimensional space, generation and immersion needed by its statement were obtained in step 2. Smoothness of Y is a given hypothesis. Its precise meaning of general gives a nonempty affine coefficient open. I removed the zero vector; r>=1 because the system generates a line bundle on the nonempty integral Y. The polynomial induction written in the step supplies an F-valued coefficient tuple over the infinite field, so there is no unmentioned closed-point theorem. The chosen section has smooth zero scheme, including the empty case; those are exactly the new injectivity node's assumptions.

For step 4 I opened the new node and checked the multiplication map's source and target: the power is m+1, not m, and its degree j is unrestricted. The same algebraically closed characteristic-zero F, smooth projective geometrically integral Y, A, m>=2 and the section from step 3 satisfy all hypotheses. Ampleness is not silently required by the supporting node. Step 5 is elementary: injectivity into the zero group forces every class to vanish. Each cited statement was copied verbatim to citations.json, not paraphrased to make it appear to say more.

Small cases checked: Y=Spec F (n=0, empty smooth divisor, multiplication by a nonzero scalar is invertible); Y=P1 with A=O(d), d>0 (the target powers and canonical twist agree with H1(O(d-2))=0); arbitrary i>n (the proof does not need a separate cohomological-dimension assertion); trivial L and nowhere-vanishing s in the new node (multiplication is already an isomorphism). I checked that no positivity or finite-coefficient assumption from the surrounding étale project is introduced into this Zariski coherent-cohomology argument. Every off-unit input is a generic algebraic-geometric tool and is declared in split_report.tool_uses. The DAG citation check and dry run will check cycles as well. No step exceeds 2000 characters, and there is no hidden field-extension comparison performed inside a step.

## Unfinished work

The new injectivity theorem is intentionally statement-only for the next stage-1 split. Its cyclic-cover/Hodge-theoretic proof and field-of-definition reduction remain that node's work, not unacknowledged premises of the present assembly. No other work on the item remains except the required dry run and push.
