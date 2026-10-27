# Q52: lem-sfb-orbit-automorphism-cauchy-realizers

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-orbit-automorphism-cauchy-realizers.json`: existing statement, now split into five explicit elementary steps. Statement and statement dependencies unchanged. No exact Mathlib match.
- `citations.json`: verbatim statement excerpts for the orbit-category definition used in steps 1 and 2.
- `searches.jsonl`: six actual msearch invocations, including a second semantic phrasing and a second source grep. The original item's four search records are retained; the six searches run by Q52 are appended to its Mathlib search field.

New nodes: 0. New Mathlib leaves: 0. No Lean files, repository files, launcher files, unit records or chapter records were written. `write_split.py` is a sandbox-only JSON preparation script.

## Attachments

None. Searched all of `lean/WeilConjectures/` and `lean/Sheaf/` for the item tag, open-orbit language, forgetful automorphisms and two-sided Cauchy arguments. The existing `TopologicalGroup.completeGroup_forgetful_automorphisms` at `lean/Sheaf/GroupTheory/CompleteGroupForgetfulAutomorphisms.lean:65` ends in `sorry` and assumes compactness or completeness; it is neither an attachment nor a proof of this item under its hypotheses. The actual open-orbit definitions already belong to `def-sfb-open-orbit-functor`.

## WANTED

None. Read the local Bhatt–Scholze PDF, Proposition 7.1.5, printed p. 64, directly using pdftotext. The neighboring Example 7.1.6 is about completeness and is not needed here. No SGA source is used. No Stacks claim is invoked: the source of this group-theoretic argument is Bhatt–Scholze, not an algebraic-geometric lemma from Stacks.

## What was wrong or incomplete

The item was statement-only. Its parent already uses it for finite simultaneous realizability, closed coordinate cosets, and two-sided Cauchyness. The missing argument was how naturality on a common conjugate stabilizer simultaneously prescribes every coordinate, and how a coordinate for the inverse automorphism controls the second ordered difference. All of that argument is now in the item itself.

There is no statement dispute. Neither completeness nor compactness is needed to construct this net. Those are hypotheses of the parent's subsequent limit argument. The present Hausdorff hypothesis is harmless and retained even though this construction does not use it. No normality or finite-index assumption on the open subgroups has been introduced.

## Unfinished work

None for this stage-1 split. This is a natural-language proof only, as authorized; no compilation was attempted.

## Searches and blueprint route

Read the chapter `sec-six-functors-basics` and the recorded unit `sk-thm-sf-ctf-stability`, including its three-level route constraints. This is the previously extracted reconstruction subargument below the continuous-monodromy obligation. Its parent and existing ancestry identify the finite-coordinate/Cauchy argument of Proposition 7.1.5. Nothing in the unit or chapter is changed. `tools/blueprint_refs.py ancestor lem-sfb-orbit-automorphism-cauchy-realizers` returns None; retained the inherited null ancestor and the precise existing place/via chain, and filled the split report's blueprint explanation.

Whole-blueprint searches for `orbit`, `Cauchy` and `natural automorphism` returned respectively three unrelated orbit statements, no Cauchy statement, and five finite-Galois/representation/generating-class statements. No blueprint node states this lemma, so `same_as` remains empty. Whole-DAG searches for finite coordinate realization, simultaneous orbit/coset realization, intersections of stabilizers and open-subgroup closedness found the item, its reconstruction parent and unrelated statements, rather than a smaller result needed here. No new-node duplicate question arises.

All six Q52 Mathlib searches were made with the required msearch.py and their outputs were read. LeanFinder returned finite-fibre Galois reconstruction/quotient realization and unrelated density statements. LeanSearch returned finite-fibre fundamental-group, naturality, compactness and unrelated forgetful-functor facts. Loogle's `"Cauchy", "Aut"` had no hits. The first grep had none; the second had unrelated `TwoSidedIdeal` assertions and a finite Galois orbit relation. Checked `Mathlib/CategoryTheory/Galois/Basic.lean:190-205`, `Galois/EssSurj.lean:15-55`, `Galois/Topology.lean:39`, and `Galois/IsFundamentalgroup.lean:61-83,120-145`: the functors there have finite fibres. Naturality itself is a defining equation, not a theorem requiring the finite-Galois setup. In particular no finite-fibre or compact-group theorem is used for the arbitrary (possibly infinite) coset sets of this item.

## Not duplicates

No new nodes. Extracting a node asserting simultaneous finite-coordinate realization would merely restate the main clause of this item (D1), while extracting common stabilizers, open-subgroup closedness or the two displayed group calculations would create elementary nodes (B/C). The proof spells them out instead.

## Review by Q52

I read delivery-errors B through E in full and checked the split against them with both definition statements and the source open. For the item, the source actually uses projection compatibility for finite intersections and the conjugate-orbit map T_h for the inverse-coordinate Cauchy condition. Our five-step net proof makes those same operations explicit. Its proof origin is marked agent because it rewrites the source filter argument as the particular finite-coordinate net in this statement; it does not claim that the PDF contains this net verbatim. There are no new nodes requiring separate sources or searches.

Step 1 uses exactly the statement of `def-sfb-open-orbit-functor`: objects are quotients by open subgroups and arrows are all equivariant maps between them. I verified that H_x=a_x U_x a_x^{-1} really is the stabilizer of the left coset a_x U_x, that conjugation is a homeomorphism by multiplication/inversion continuity, that the finite intersection V is open, and that q_x is well-defined and equivariant by the displayed equations. Thus the cited definition supplies the actual arrow we need, rather than merely a related category.

Step 2 uses the same definition to regard those arrows under the underlying-set functor. Applying the defining naturality equation at the identity coset V yields the complete formula for g x. Choice is only of representatives and of one element in each already nonempty realizer set; no theorem with undetermined data is postponed. I set the empty-index choice to 1 explicitly. The statement excerpts for both citations are copied verbatim in citations.json; no proof of a cited node is being used. I also read `def-sfb-set-functor-aut-pointwise-topology`: it really allows arbitrary fibres and independent universes, as the statement requires, but no assertion about that topology is used in this proof.

Step 3 uses the previous two steps and the elementary partition into left cosets: the complement of an open subgroup is the union of the other open cosets. This proves closedness rather than citing an unrecorded closed-subgroup theorem. The equality C_x=rH_x fixes the side of the coset, and each finite intersection contains the chosen g_F. The empty intersection contains 1. These checks use no compactness theorem or topological completeness.

Step 4 uses only prescribed values from step 2 and cancellation of the left action. I checked the two orders separately: aU=bU gives a^{-1}b in U, whereas ay=by=U gives y=b^{-1}U and then ab^{-1} in U. The second equality would not follow by treating a natural-automorphism component as G-equivariant; the proof never does so. It uses both coordinates exactly as the statement says, with no normality assumption.

Step 5 uses the hypothesis that identity neighborhoods contain open subgroups, the union upper bound for finite subsets, and the displayed definition of two-sided Cauchyness in the item's statement. Its threshold contains the two correctly tagged coordinates, so it controls every pair of later indices. It invokes no general convergence or uniform-space lemma. No step cites any off-unit statement; the only proof dependency is the existing definition node. The union of step uses equals proof_deps.

I checked the small and degenerate cases: the trivial group, F empty, U=G, coinciding threshold coordinates, distinct subgroup tags with otherwise similar underlying representatives, and a nonnormal order-two subgroup of the discrete group S_3. The stabilizers are conjugates and not assumed equal to U_x; this is what makes the nonnormal case work. For an infinite discrete group such as Z, V may be the trivial subgroup and G/V infinite; the same formulas work, confirming that no finiteness-of-fibres argument has slipped in. For alpha the identity one may choose every g_F=1. The general choices need not be compatible across F, and the estimates still follow from their prescribed coordinates. Every proof step is under 550 characters, so there is no long step hiding an auxiliary lemma. The unchanged statement has every object introduced and both necessary definition references already in stmt_deps.

No mathematical correction was necessary. The repair consists entirely of supplying the missing proof with all conventions and edge cases checked. Server dry run and delivery are performed by the prescribed deliver.py commands after this report is written.
