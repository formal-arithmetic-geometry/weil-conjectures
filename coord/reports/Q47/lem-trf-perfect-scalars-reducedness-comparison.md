1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-perfect-scalars-reducedness-comparison.json`: statement, split; unchanged statement; no exact or one-line Mathlib match.
- `citations.json`: one verbatim statement excerpt for each use in each of the five proof steps.
- No new nodes and no new Mathlib leaves.

2. Attachments

None for this item. The completed project declaration `isReduced_tensorProduct_of_perfectField` belongs to the already existing `lem-weil-pbc-perfect-reduced-tensor`; it proves the ascent ingredient only. `Field.exists_common_extension` belongs to the already existing `lem-weil-common-extension-fields`. Neither states the item. Searched the live project under `lean/WeilConjectures/` by the blueprint tag and reducedness/perfect-field concepts; read both project files, including their hypotheses and proofs. No completed project declaration supplies the comparison for arbitrary E and F.

3. WANTED

None. All sources used are available locally.

4. Problems and changes

The initial item is an unsplit, correct auxiliary statement. No statement dispute or correction was needed. Its earlier Mathlib searches are preserved, including the failed Loogle pattern and its successful replacement. Additional searches were run through msearch.py and the actual log records are included. A second semantic phrasing was also run. The pinned Mathlib's geometric-reducedness interface gives an algebraic-closure test and an algebraic-extension reducedness instance; it does not compare arbitrary perfect extensions in one line. The project, rather than Mathlib alone, supplies the general perfect-field ascent theorem, and its existing DAG node is reused.

Read the chapter and unit records, SETUP's three-level route, and the latest blueprint ancestor `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.{md,proof.md}`. The inherited blueprint.from place locates this algebraic comparison in the approximation subargument underneath the contracting-local-term route. Whole-blueprint searches for `perfect reduced`, `reducedness` and `perfect field` found no blueprint statement equivalent to this comparison. The finite-type scheme assertion `lem-kun-geometric-reduced-perfect` is only an ascent result and imposes finite type, so it is not the item. The existing arbitrary-algebra ascent node is the appropriate tool.

Generic off-unit tool: `lem-weil-common-extension-fields` supplies amalgamation of arbitrary field extensions; this does not replace the trace-formula unit's geometric route. It is declared in split_report.tool_uses. The other off-unit tools are Mathlib leaves or the Lean-closed perfect-reduced-tensor node.

5. Unfinished work

None in this one-level split. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. The argument reuses the existing common-extension, cancellation, algebra tensor universal property, module tensor definition, scalar-extension injectivity, and perfect-field tensor reducedness nodes.

## Review by Q47

I read Stacks `fields.tex`, Tag 0H7K (`lemma-common-extension-field`), and `algebra.tex`, Tag 00I4 (`lemma-perfect-reduced`), including their proofs. The former explicitly allows arbitrary E/k and F/k, while the latter explicitly allows arbitrary reduced algebras over a perfect field. I also read the tensor reassociation statement at Tag 00D2 (`lemma-tensor-with-bimodule`), the existing algebra cancellation node, and its Mathlib source at `RingTheory/TensorProduct/Maps.lean:476–489`. I checked scalar-extension injectivity in `RingTheory/Flat/Basic.lean:410–415`, as recorded by the existing field-extension tensor injectivity leaf. I read the statement of every cited node, not just its source metadata. There are no new nodes needing additional sources.

Step 1 cites `lem-weil-common-extension-fields` for exactly a common field and compatible k-embeddings. It neither assumes an embedding E to F nor requires their extensions to be algebraic. The two embeddings define the separate E- and F-algebra structures on M with the same underlying k-structure.

Step 2 cites `lem-weil-pbc-tensor-cancel-base-change` for its stated algebra isomorphism, specialized with its R=k, S=D, A=M and B=the item's A. The module tensor definition provides the bilinear universal property for factor flips; the algebra tensor pushout node supplies precisely multiplication of pure tensors and the ring structure. I checked the flip on products and its inverse on generators. The resulting displayed maps are mutual inverses: balancing moves d across the D-tensor, and multiplying i_D(d)m agrees with the common k-structure. These are direct generator calculations after the cited cancellation, so this step is elementary rather than a hidden comparison lemma. It does not infer a ring isomorphism merely from a module isomorphism.

Step 3 cites `lem-sfb-field-extension-tensor-injective` with its base field k replaced by D, its K by M, and its B by A tensor_k D. Its statement gives exactly b to b tensor 1 injective for every commutative D-algebra. Composition with step 2 is therefore the explicitly displayed scalar-extension map j_D. Neither reducedness nor finite generation nor a nonzero algebra is a hypothesis of this leaf.

Step 4 cites `lem-weil-pbc-perfect-reduced-tensor` over E, with reduced factors B_E and M. Perfectness is used for E, not for the possibly imperfect k and not for M. The field M is reduced because a nonzero field element is a unit. Preservation of reducedness under theta_E is checked by applying its inverse to a nilpotent, rather than invoking an uncited descent theorem.

Step 5 writes descent to B_F as the equation j_F(x)^n=j_F(x^n)=0 followed by reducedness of T and injectivity. For the reverse implication it cites the same perfect-reduced-tensor statement over F, then uses theta_F and j_E. Both uses have their exact hypotheses in force. No faithful-flat descent theorem is tacitly needed: the nilpotent calculation is the whole descent argument.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against the delivery. No new statement-only node, duplicate clause, relabelled proof, or cycle is introduced. All non-elementary inputs are existing cited statements. Every citation quote was checked as a literal substring of its node's statement. Every proof step is under 2000 characters. The statement is unchanged and all inherited import/blueprint metadata is retained. The only newly specified blueprint data is the searched same_as list, still empty.

Small cases: A=0 makes both tensor rings zero and reduced; the injectivity and comparison arguments remain valid. A with a nonzero nilpotent, for example k[epsilon]/(epsilon^2), retains its nilpotent in both scalar extensions, consistently with the equivalence. E=F and E=k (when k is perfect) specialize correctly. With imperfect k=F_p(t), E and F perfect closures with additional transcendental variables still embed in a common field; no finite-type or algebraicity assumption enters. The proof never asserts that a reduced A over imperfect k remains reduced. Thus it includes arbitrary, possibly non-finitely-generated and initially nonreduced A as required.
