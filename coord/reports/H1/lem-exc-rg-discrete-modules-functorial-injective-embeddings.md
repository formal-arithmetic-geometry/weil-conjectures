1. Files written

- `dag/nodes/sec-curve-estimates/lem-exc-rg-discrete-modules-functorial-injective-embeddings.json`: item, statement, split proof, and metadata.
- `dag/nodes/sec-curve-estimates/lem-exc-rg-group-algebra-functorial-injective-embeddings.json`: statement node, Mathlib searches found no match.
- `dag/nodes/sec-curve-estimates/lem-exc-rg-open-stabilizer-adjoint.json`: statement node, Mathlib searches found no match.
- `dag/nodes/sec-curve-estimates/lem-exc-rg-adjoint-transfer-functorial-injectives.json`: statement node, Mathlib searches found no match.

2. Attachments

None.

3. WANTED

WANTED: `literature/stacks-project/injectives.tex`, Tag 04JF and the paragraph on modules over an algebra, for `lem-exc-rg-discrete-modules-functorial-injective-embeddings` and `lem-exc-rg-group-algebra-functorial-injective-embeddings`.
WANTED: `literature/stacks-project/homology.tex`, Tag 0161, for `lem-exc-rg-adjoint-transfer-functorial-injectives`.

4. Problems found

The repository node had been created by an earlier item but remained `unsplit`, and its `created.item` names that earlier item. I left that history field unchanged and supplied the missing split. No statement error was found. The project checkout does not contain the cited Stacks TeX files, so the report records them as wanted rather than pretending they are local project sources.

5. Unfinished work

The three dependency nodes are intentionally statement-only unsplit nodes, as required for one-level stage-1 splitting. No Lean declaration states the item in either source checkout.

## Review by H1

I read the exact proof of Stacks Tag 04JF in `/home/ubuntu/c1-stacks-review/injectives.tex` (the project literature directory lacks this file) and checked the nearby group-ring paragraph and its final invocation of Homology Tag 0161 in `/home/ubuntu/c1-stacks-review/homology.tex`. The item statement matches Tag 04JF: the group is topological, the coefficient object is an arbitrary ring, objects are $R$-modules with an $R$-linear action and open stabilizers, and the conclusion is a functorial monomorphism into injectives. The first new node records the preceding group-ring module assertion. The second records exactly the proof's forgetful functor, preservation of monomorphisms, and right adjoint $u(M)=\{x: \operatorname{Stab}(x)$ is open$\}$. The third records the generic adjoint-functorial-injectives transfer used in the final sentence.

Step 1 uses only the statement of the group-ring node. Step 2 uses only the statement of the open-stabilizer adjunction node. Step 3 uses the statements of all three nodes: the group-ring functorial embeddings, the adjunction data, and the transfer lemma; no step relies on a hidden proof. Each step is marked non-elementary because it invokes a cited Stacks result. The item and all new nodes have complete statements, TeX escaping, source places, blueprint ancestry, and three recorded Mathlib search kinds (LeanSearch, Loogle, and source grep), all with no specialized match.

I tested the construction on the trivial group, where the open-stabilizer category is the ordinary module category, and on a finite discrete group, where every stabilizer is open and the category is the group-ring module category. I also checked the zero module: its stabilizer condition is vacuous and the natural component is the zero-to-injective monomorphism. These cases support the hypotheses and reveal no mismatch in the specialization.
