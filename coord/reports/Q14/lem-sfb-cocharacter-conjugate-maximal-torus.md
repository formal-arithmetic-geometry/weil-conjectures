## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-cocharacter-conjugate-maximal-torus.json: statement, split; no Mathlib match, five proof steps, no new nodes.
- citations.json: ten verbatim statement extracts, one for every step/node pair.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, cocharacter, maximal torus, torus and Theorem 17.10 found no declaration of this result. The only torus hit concerned a topological compactness argument in FrobeniusModule/TraceBound.lean, and the 17.10 hits were unrelated Stacks section references. No Lean was written or compiled.

## WANTED

None. The item's cited Milne book is available and was read locally.

## Corrections and scope

The statement is true and is preserved, including the quantification over all commutative k-algebras, the absence of reductivity, the trivial cocharacter, and rank zero. There is no statement dispute. The imported empty proof is replaced by an assembly using existing nodes. In particular, torus-image alone would not supply the factorization it assumes: the affine homomorphism theorem is cited separately. Neither Borel containment nor maximal-torus conjugacy alone asserts that a prescribed smaller torus is contained in a maximal torus; that missing inference is proved explicitly by a maximum-dimension argument.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, especially _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3). The latter retains the compactification and proper/open direct-image route of the inherited dependency chain. This supporting algebraic-group input changes no unit or chapter route. The copied item's blueprint.from.node is null, and tools/blueprint_refs.py ancestor returns None; its existing from.place and via chain are preserved. Whole-blueprint searches for maximal tor, torus, cocharacter and cocharacter conjugate returned no matching imported node. Whole-DAG keyword and Milne-place searches found the reused image and conjugacy nodes.

## Not duplicates

No new node is proposed. Existing lem-sfb-affine-homomorphism-flat-image, lem-sfb-torus-homomorphism-image and lem-sfb-borel-maximal-torus-conjugacy are reused; a maximal-torus-containment node would merely package the short strict-chain argument and is unnecessary. The existing conjugacy node applies to maximal tori and does not by itself state this item's factorization for a cocharacter.

## Review by Q14

I read Milne, Algebraic Groups (2017), Theorem 3.34 on printed p.75, Definition 12.14 and its following paragraph on p.236, and the statement and proof of Theorem 17.10 on pp.354–355. These give respectively the faithfully flat image factorization, that a quotient of a split torus is a split torus, and conjugacy of maximal tori for a smooth connected affine group over an algebraically closed field. No reductivity assumption is hidden in the latter: the ambient hypothesis at the beginning of Section 17b is a connected group variety. I also read the supporting statement of lem-kun-dimension-finite-type in the latest blueprint and the chain definition in Stacks topology.tex, Definition 0055 (definition-Krull), and the affine closed-immersion description in morphisms.tex, Lemma 01QO (lemma-closed-immersion), together with schemes.tex, lemma-closed-immersion-affine-case and lemma-closed-subspace-scheme. There are no new-node sources to audit.

Step 1 uses the complete statements of lem-sfb-affine-homomorphism-flat-image and lem-sfb-torus-homomorphism-image. The first actually supplies I, u and j and says that u is faithfully flat in the module sense required by the second. Both source and target are affine of finite type; Gm is a torus and k is algebraically closed. I checked that the torus-image statement does not assume a smooth kernel, so characteristic-p power cocharacters are covered. This repairs the potential gap between an informal image and the required scheme-theoretic factorization.

Step 2 uses exactly the finite-type dimension bound in lem-kun-dimension-finite-type and the global strict-chain meaning in def-kun-dimension. It uses only the unconditional first assertion of lem-trf-lattice-torus-coordinates-action, which identifies the coordinate torus with Spec k[Z^r], and the integral-domain assertion of lem-trf-split-lattice-torus-projection, specialized to K=k. The unrelated monoscheme assumptions of the coordinate node apply only to its later action clause. A domain has zero prime, dense in its spectrum, so these tori are reduced and irreducible. Chains in a closed subspace remain closed chains in G, giving the bounded nonnegative integer dimensions directly. I read the full statements of these four nodes and verified each extract in citations.json against the corresponding statement.

Step 3 uses def-weil-closed-immersion for the actual quotient ideal J, and def-kun-dimension for the chain argument. The family of containing tori is nonempty because step 1 produced I, and its dimensions lie in the finite interval from step 2. If a larger torus R had the same support as S, J would lie in every prime of the domain k[R], including zero, so the supposed strict inclusion would be an isomorphism. Otherwise appending the irreducible R to a longest chain in S increases the dimension. This is a few-line consequence of the cited definitions and step 2, not an uncited theorem about algebraic groups. It justifies maximality among all tori, not only among those of a preassigned rank. No new elementary node was created.

Step 4 reads and applies only the maximal-torus clause of lem-sfb-borel-maximal-torus-conjugacy, with T1=S and T2=T. Its statement gives an element of G(k), not merely of G over a further field, and gives equality of subgroup schemes after every algebra extension. Its algebraically closed, smooth, connected, affine and finite-type hypotheses are precisely available here. The Borel clause of that node is not used. I checked the orientation so the resulting conjugate is g mu g^{-1}, not its inverse conjugation.

Step 5 uses def-sc-group-scheme for multiplication, inverse, identity and homomorphisms. Restricting the explicitly constructed inner automorphism to S and composing it with Gm -> I -> S gives an actual scheme morphism into T. The formula on A-points is the composite formula, not a claim that u is surjective on arbitrary A-points. Group identities give its inverse and its homomorphism identity. This verifies the strongest, functorial clause of the item without invoking agreement on k-points only.

I tested the trivial group, a trivial cocharacter into any G, the rank-zero prescribed torus, and the inseparable power map t -> t^p in characteristic p. Rank zero gives k[Z^0]=k and the same dimension argument; if T has rank zero, conjugacy forces S and then I to have rank zero, so mu is trivial. The map t -> t^p has image Gm despite nonreduced kernel, as required. Disconnected or nonsmooth ambient groups are not introduced. Every non-elementary input is named, and every cited statement was opened. Proof dependencies are exactly the union of step uses, and none reaches the item. Step lengths are 528, 706, 902, 455 and 793 characters, so none contains an unexamined long step.

The two semantic Mathlib phrasings were the cocharacter-conjugation theorem and containment of a torus in a maximal torus. LeanFinder returned Lie-algebra Cartan and abstract subgroup results; LeanSearch returned abstract conjugation, Frattini and topological torus results. Loogle returned no hits for the torus/conjugacy patterns, and grep found only an unrelated complex-embedding conjugation line or no hits in AlgebraicGeometry. I read those returned results: none is this algebraic-group theorem or a one-line specialization. All seven searches are recorded exactly by tool and query in searches.jsonl and the item's mathlib_searches; no unavailable service was treated as absence.

The finite-type dimension bound and the two lattice-torus facts are declared generic tool uses in split_report.tool_uses, since their units differ. They supply dimension and coordinate facts only and do not replace the unit's geometric route. No maintainer-owned field, library source, launcher script or shared-repository file was changed. No prohibited source was used. The source proof is an agent assembly from the cited document and existing nodes, so proof_origin.by is agent.

## Unfinished work

None within the stage-1 item. The reused unsplit torus-image and maximal-torus-conjugacy nodes remain existing separate queue items.

## Dry-run repair

The first citation gate required extracts of at least 40 characters. I replaced the short conclusions quoted for the torus-image and dimension-finiteness nodes by their complete statements, preserving the same proof and cited hypotheses. The statement excerpts remain verbatim.
