# Stage-1 delivery: lem-sfb-unitriangular-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-unitriangular-extension.json`: statement item, now split into six proof steps; no Mathlib match.
- `citations.json`: ten entries, one for every step/node citation, checked as verbatim substrings of the current cited statements.
- `report.md`: this report.
- `searches.jsonl`: five actual msearch queries for the item. Existing inherited search records are retained unchanged in the node. Local reference extraction `milne.txt` is scratch material only.

New nodes: 0. New Mathlib leaves: 0. No Lean, unit records, repository files or launcher files were written. No compiler or git command was run by the worker.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint id and for unipotent/unitriangular. Hits concern a biproduct automorphism and a matrix calculation, not affine group-scheme extensions. There is no finished project declaration to attach.

## WANTED

None. All proof sources used here are present in Milne, Algebraic Groups (2017), and were read from the local PDF.

## Problems found and changes made

The imported statement is correct, including arbitrary fields and nonsmooth, nonreduced groups. Its proof was empty. I retained its statement, statement dependencies, source and inherited blueprint provenance and search records, and supplied the proof rather than citing another extension statement. The inherited `blueprint.from.node` is null (the ancestor script reports None); its detailed `from.place` and `via` list were preserved, not invented. The latest blueprint has no standalone node for this extension assertion. I read the current chapter and unit, the direct-images proof and the inherited DAG chapter/unit records. The supporting algebraic-group argument stays below the existing unit route; no unit or chapter was changed. The current blueprint direct-image proof has a different presentation from the historical long alteration provenance in `from.place`; this split does not claim the latest file explicitly contains Milne's group-theoretic argument.

A pre-existing duplicate was found: `lem-sfb-unipotent-extension-arbitrary` states precisely the same arbitrary-field unitriangular extension theorem. It is unsplit. I did not edit it or make the item's proof 'apply that node', which would be a relabelling, not a split. The maintainer can reconcile the existing duplicate after reviewing this real split. No new duplicate was created.

The proof uses the existing cyclic-representation descent theorem instead of introducing another normal-invariant quotient lemma. Its statement explicitly permits a noncentral, nonreduced kernel. Thus an N-fixed vector generates a nonzero E-module on which the action descends to Q, and Q's fixed-vector theorem yields an E-fixed vector. This is a submodule of the normal-invariant space in Milne 6.45 and realizes exactly its argument. I then spell out the flag construction and the coordinate-surjectivity argument, so no equivalence between rational unipotence and unitriangular embeddability is assumed without proof.

## Search results

The whole DAG was searched by statement text for unitriangular groups, rational fixed vectors, faithful representations, normal-invariant spaces and representation descent; every cited node was opened. `tools/blueprint_refs.py search` was run for unipotent, fixed vector, faithful representation and invariant. The fixed-vector and faithful linear representation inputs already exist, and all statement inputs here belong to the same unit or are definitions. `same_as: []` is retained: the blueprint searches found no equivalent blueprint statement.

Five new searches were run using the required msearch.py command (two different LeanFinder phrasings, LeanSearch, Loogle, and source grep). All services returned successfully. I read all returned signatures: they concern topological matrix embeddings, general abstract group extensions, abstract solvability/nilpotence, affine limits, and unramified or smooth-ring morphisms. None asserts this theorem or specializes to it in one line. Loogle and grep returned no hits for the requested group-scheme/unitriangular notions. Exact tool/query records and results appear in the node and searches.jsonl. No unavailable service was represented as a negative mathematical result.

## Not duplicates

No new nodes. Existing pair noted for maintainer action: lem-sfb-unitriangular-extension vs lem-sfb-unipotent-extension-arbitrary: these are equivalent statements; this delivery provides the six-step proof on the assigned item and leaves the other node untouched.

## Review by Q02

I read Milne Section 6.45 (printed p.135) for the item, Lemma 5.15 (p.102) and Theorem 5.13 (p.101) for the normal-invariant factorization, Proposition 14.3 (p.280) and Theorem 14.5 (pp.281–282) for the conversion to a closed unitriangular embedding, and Theorem 4.9/Corollary 4.10 (p.87) for faithful representability. Corollary 14.7 (p.282) explicitly points back to 6.45 for extensions. There are no new node statements to review. None of these inputs assumes smoothness, connectedness, reducedness or a perfect field; I did not replace rational invariance by invariance of k-points.

Step 1 uses `lem-sfb-unitriangular-subgroup-rational-fixed-vector`, whose statement gives a nonzero vector fixed after EVERY algebra extension for any representation of a finite-type affine group with a closed unitriangular immersion. It applies to N by the item's hypotheses and to W after choosing a basis. The representation-comodule dictionary explicitly gives the coaction and evaluation formula, so this vector is also a comodule-fixed vector, as required in the next citation. This is a theorem application, marked non-elementary.

Step 2 uses the quotient clause of `def-sfb-solvable-group-structure`: the represented quotient is flat, surjective and locally finitely presented, with the given scheme-theoretic kernel. All schemes are affine, so this is faithfully flat on coordinate algebras as required by `lem-sfb-central-kernel-cyclic-representation-descent`. I checked its complete statement: it gives the smallest cyclic subcomodule, finite dimension, nonzeroness, trivial kernel action and an actual descended rational quotient action. It explicitly removes centrality/reducedness assumptions despite its historical name. The step takes those conclusions from its statement, not from its proof. This step is non-elementary.

Step 3 again uses the dictionary's finite-dimensional representation clause and the same unitriangular fixed-vector theorem, now for Q on the nonzero descended space. The last inference is explicit: E(A) acts through q_A into Q(A), hence fixes the resulting vector. No assertion that q_A is onto for arbitrary A is used. Its nonzero image in W follows from the inclusion of a vector subspace. This step is non-elementary because it applies the fixed-vector theorem.

Step 4 uses `lem-sfb-affine-group-faithful-linear-representation`, whose statement supplies a CLOSED immersion into GL_m with m at least one for every affine finite-type group scheme over an arbitrary field. This exactly meets E's hypotheses; a representation injective only on geometric points would not suffice. It is marked non-elementary.

Step 5 is elementary assembly of the fixed-vector property already established for arbitrary finite-dimensional E-representations: dimension zero is the base; a fixed line is removed, the quotient action is written on representatives, and its rationality follows from the cited dictionary's exact finite-dimensional clause. Choosing a complement identifies the scalar quotient for every test algebra. The dimension strictly drops; lifting the quotient flag gives the flag upstairs with trivial one-dimensional quotients. Thus there is no hidden appeal to composition-series existence, Lie–Kolchin, smoothness, or a separate unipotence criterion. The induction uses the SAME group E and the property proved in steps 1–3, so it is not circular. The step has no independent unproved subclaim requiring a new node.

Step 6 is elementary matrix and ring assembly. I opened `def-sc-general-linear-group`: its statement gives the represented invertible-matrix functor and matrix coordinate algebra. With an adapted basis, the flag makes each column equal to its standard vector modulo preceding columns, over every A. Evaluating at the universal affine point forces the defining unitriangular equations in k[E] itself. I opened `def-weil-closed-immersion`: its statement explicitly includes the affine criterion by surjective coordinate maps (Stacks Tag 01QO, morphisms.tex, lemma-closed-immersion). After basis conjugation the original coordinate map is still surjective; factoring it through the unitriangular quotient preserves surjectivity. This verifies a closed immersion into U_m, not just a set-theoretic inclusion. No uncited theorem about factorization of immersions is used.

Small cases checked: N=1, Q=1, and E=1 give the same fixed-vector argument, with the trivial group embedding in U_1. In a one-dimensional faithful representation the fixed flag forces the action to be trivial, consistent with U_1=1. The dimension-zero quotient occurs at the last induction stage and has the empty flag; no fixed vector in a zero space is requested. In characteristic p, alpha_p and the constant group Z/pZ are allowed by the cited nonsmooth fixed-vector theorem and the all-algebra calculations; mu_p is not incorrectly treated as unipotent (its nontrivial character fails the fixed-vector property). Imperfect fields cause no scalar-extension or descent issue because the construction stays over k. In particular no argument relies on geometric points detecting nilpotents.

I checked delivery-errors B through E: no new self-contained statements or proof sketches masquerading as statements, no invented Mathlib searches, no clause-restating nodes, no use of a citation's proof-only content, no unstated smoothness or characteristic assumption, and no induction dependency on a later conclusion. Each of the ten citations has a verified verbatim quote in citations.json. All six proof steps are shorter than 2000 characters (533, 585, 692, 293, 1063, 1177); none hides a literature lemma behind a long step. The non-elementary steps cite their exact inputs, and the elementary steps give the actual quotient-action, flag and coordinate arguments. No SGA source is used.

## Unfinished work

None in the one-level split. The existing unsplit duplicate needs maintainer reconciliation, outside the worker's allowed files. The required dry run and push are recorded by the delivery tool.
