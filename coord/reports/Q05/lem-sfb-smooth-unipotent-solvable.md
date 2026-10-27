# Q05 stage-1 delivery: lem-sfb-smooth-unipotent-solvable

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-unipotent-solvable.json`: split statement, unchanged statement and statement dependencies; three proof steps, 2201 characters in total.
- `dag/nodes/sec-six-functors-basics/lem-sfb-geometric-unipotence-unitriangular-embedding.json`: one new statement-only node, unsplit; Mathlib searches found no matching group-scheme theorem.
- `citations.json`: verbatim statements for every citation of each item proof step.
- `report.md`: this report. The sandbox also retains the actual `searches.jsonl`, an extracted `milne.txt` for reading, and the sandbox-only writing script.

## Attachments

None. Searches by the item tag and by unipotent/solvable/unitriangular in `lean/WeilConjectures/` found no declaration stating the item. The hits on biproduct unipotent morphisms and block unitriangular matrices do not concern algebraic-group solvability. No Lean was edited, compiled or built.

## WANTED

None. Every source used is available in `literature/milne-algebraic-groups_iAG2017.pdf`.

## Findings and corrections

The imported statement is correct and was retained verbatim. In particular the hypothesis is smoothness, not geometric connectedness, and the ground field can be imperfect and of positive characteristic. Its statement dependencies are unchanged, including the introductory connectedness convention even though no connectedness hypothesis is imposed.

Milne Proposition 14.21 is a proof, not a permissible new node repeating the desired conclusion. Its proof first embeds in a unitriangular group, then intersects the standard series. I isolated only the embedding theorem (14.12 and 14.5(b)). I replaced the fine one-coordinate ordering of Example 6.49 by its coarser superdiagonal-distance filtration, and wrote the elementary matrix multiplication, inverse and commutator calculation in the item itself. This is the same embedding-and-intersection route. No new theorem saying that unipotent groups are solvable, nilpotent, or have the required solvable series was created.

Quotient representability, exactness and local lifting are taken from the existing `lem-sfb-affine-normal-quotient-geometry`, not inferred from normality alone. I do not assume its smoothness conclusions apply to the intersections: those intersections need not be smooth. Its first assertions apply to arbitrary affine finite-type group schemes and normal closed subgroups, precisely what is needed here.

The inherited `created.item` chain stops at `lem-sfb-admissible-direct-image` without an imported blueprint ancestor. `python3 tools/blueprint_refs.py ancestor lem-sfb-smooth-unipotent-solvable` explicitly returned `None`. The item retains that null ancestor and its exact explanatory place; the new node has the same null ancestor and the extra item at the front of `via`. I did not invent an ancestor or edit the upstream chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, as well as the recorded unit and chapter. This is a generic algebraic-group input already required by the item's parent; the unit and chapter route are untouched.

## Search record and Mathlib verdict

The original item's search results from its creator are preserved. I also ran the specified msearch command for the item and the new embedding question: LeanFinder, LeanSearch, Loogle, and Mathlib grep. For the new node I used both “smooth affine algebraic group with unipotent geometric points ... upper unitriangular matrices over the base field” and “faithful unipotent representation ... triangularizable over its ground field.” Queries in the JSON are exactly the queries in the actual sandbox log. All these services answered successfully.

The semantic results include `IsNilpotent.to_isSolvable` (read at `Mathlib/GroupTheory/Nilpotent.lean:1161`), `IsSolvable`, Lie algebra solvability, `LieModule.instIsTriangularizableOfIsAlgClosed` (read at `Mathlib/Algebra/Lie/Weights/Basic.lean:757`), and properties of closed immersions. These do not prove either group-scheme statement. The Lie-module instance gives generalized weight-space decompositions for one operator at a time; it is not a unitriangular embedding of a group scheme over an arbitrary field. The broader LinearAlgebra grep found `Matrix.SpecialLinearGroup.lineStab` (`Mathlib/LinearAlgebra/Projectivization/PSL/Stabilizer.lean:34`) and simultaneous generalized-eigenspace results for a commuting family (`Mathlib/LinearAlgebra/Eigenspace/Pi.lean:194`); I read those source passages. The group here is not assumed commutative, and an abstract subgroup of SL over a field is not the required all-algebra group scheme. No exact match or one-line specialization was found. There are zero Mathlib leaves.

## Not duplicates

lem-sfb-geometric-unipotence-unitriangular-embedding vs lem-sfb-unipotent-rational-representation-fixed-vector: the existing node gives a nonzero fixed vector for any rational representation over an algebraically closed field; the new node gives a closed unitriangular embedding over the original arbitrary field, including imperfect fields. The former does not state the latter or its descent.

lem-sfb-geometric-unipotence-unitriangular-embedding vs lem-sfb-smooth-unipotent-solvable: the new statement is a matrix realization theorem, not solvability or any clause of the item's conclusion; the matrix filtration and quotient commutativity argument remain in the item.

lem-sfb-geometric-unipotence-unitriangular-embedding vs lem-wf-engel-matrix: the existing statement is about a Lie algebra of nilpotent endomorphisms over the algebraic closure of an l-adic coefficient field, not a smooth affine group scheme over an arbitrary field.

lem-sfb-geometric-unipotence-unitriangular-embedding vs sk-lem-curve-sylow-trace: the latter is a prime-to-rank finite étale cover and a filtration of a finite local system on a connected scheme. It is not an algebraic-group embedding theorem.

Before writing the new file I searched the whole DAG for unitriangular, triangularization, unipotent algebraic/group-scheme statements, and Milne 14.12, 14.5 and 14.21; blueprint_refs searches for unipotent, unitriangular, triangular, solvable and central series found no duplicate. I also searched the current blueprint text and project Lean source. The same-word Lie results and local-system statements are unrelated. The source is Milne; there are no shared Stacks tags requiring additional same-tag pairs.

## Review by Q05

I read the whole of delivery-errors B through E (both copies in the file), and checked the actual files against those failure modes. For the item I read Milne Proposition 14.21 and its complete proof on printed pp.284–285, Example 6.49 on pp.136–137, and Proposition 6.2 on pp.124–125. For the new node I read Theorem 14.5 on pp.281–282, Corollary 14.12 on p.283, and Corollary 3.35 on p.75. The last identifies all-algebra injectivity with the faithful closed-subgroup interpretation used by the smooth geometric-point criterion. Smoothness is present, so the criterion cannot confuse an infinitesimal multiplicative group such as mu_p with a unipotent group. The resulting embedding is over k itself: Theorem 14.5 states that over its given field, with no perfectness restriction.

Step 1 cites the new embedding statement, whose full hypotheses match the faithful geometric unipotence assumed by the item and whose conclusion expressly supplies the closed embedding into the unitriangular group over k. It does not cite the algebraically-closed-only fixed-vector theorem for a descent assertion. Step 2 cites `def-weil-closed-immersion` for the affine quotient-ring meaning of vanishing equations and `def-sc-group-scheme-subgroup` for all-algebra subgroup and normality tests. I opened both statements, and they explicitly say these things. The remaining argument is elementary finite matrix algebra, written out: each nonzero summand has two distance inequalities; products add distances; the inverse is a finite geometric sum; the quotient ring kills both products AB and BA. Pulling the same equations back to U gives its closed subgroup schemes and, for all R, puts the commutators in the next one. This step does not conceal a triangularization theorem, a group-scheme isomorphism theorem, or a descent theorem.

Step 3 cites `lem-sfb-affine-normal-quotient-geometry` for representability of every normal quotient, its kernel, and fppf local surjectivity. I opened its whole statement and read Milne 5.20–5.29, pp.104–105, and 5.65–5.74, pp.116–119, to verify the quotient/sheaf interpretation. Its unrestricted first clauses apply even if H_r is nonsmooth or disconnected. The closed coordinate quotients are finite type: images of finitely many algebra generators still generate the quotient algebra. Local lifts of both sections exist on a common refinement by the covering axioms; their commutator has trivial image by Step 2, and equality descends by the sheaf separation axiom. The cited `def-sc-group-scheme` explicitly defines commutativity by equality of multiplication and swapped multiplication; equality on all algebra points is exactly equality of those affine-scheme morphisms. This avoids mistaking commutativity of geometric points for group-scheme commutativity.

I tested the formulas for n=1 (the trivial group, with a length-zero series), n=2 (the single additive coordinate and an immediately trivial commutator), and n=3 (the only mixed product is the distance-two coordinate). The inequalities 2r >= r+1 require r >= 1, which is exactly the chosen index range. The proof uses neither division by a characteristic-dependent integer nor reducedness of an arbitrary test algebra. It therefore includes positive characteristic, imperfect fields, and disconnected smooth unipotent groups, including finite constant p-groups; no connectedness assumption entered. No new statement claims the nonsmooth mu_p geometric criterion. Repeated filtration terms are allowed by the definition of a finite descending series, so an intersection that is already trivial causes no problem.

For B, the new node is self-contained, has definitions inline or cited, carries no proof or proof dependencies, uses normal single TeX escaping, and records actual searches. For C, every cited statement is quoted verbatim in citations.json and the non-elementary embedding and quotient facts each have a node. For D, the substantial distance filtration and quotient argument remains in the item, so this is not a relabelling. For E, every field, smoothness, index and finite-type hypothesis has been checked as described. All proof steps are shorter than 2000 characters. There is no source error or statement dispute, no SGA citation, no off-unit tool use, and no Lean work.

## Unfinished work

The new embedding node is intentionally statement-only, to be split at the next level. Nothing in the present item's proof is left unstated. Delivery is subject to the server dry run and independent maintainer review.
