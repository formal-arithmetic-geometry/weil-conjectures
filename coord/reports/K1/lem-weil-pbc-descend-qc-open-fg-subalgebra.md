1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-qc-open-fg-subalgebra.json`: statement node, split into four elementary proof steps; no new nodes and no Mathlib leaves.

2. Attachments

None. I searched `WeilConjectures/` for the item id, its key notions, and blueprint tags; no declaration states this item.

3. WANTED

None. The cited source is present as the Stacks Project source identified by Tag 0388; I read the current `varieties.tex` proof at the cited lines.

4. Problems found and corrections

The imported item had the exact Tag 0388 statement but no proof and `status: unsplit`. I filled `blueprint.same_as` with `[]`, added the source proof, set `status: split`, and added the required `split_report`. I found no statement error. The proof deliberately does not assume that `V ∩ U_{i,A}` is quasi-compact: the finite principal opens are selected from the basis of the whole quasi-compact open `V`, exactly as in the source. I searched the whole DAG for an existing finite-principal-open descent node and checked the existing finite-affine-cover node; neither duplicates this item or is needed as a proof dependency.

## Review by K1

I read Varieties, Lemma Tag 0388 (`lemma-descend-open`), proof lines 811--848, and checked the imported statement against its hypotheses: `k` is a field, `X` is a `k`-scheme, `A` is a `k`-algebra, and `V` is a quasi-compact open of `X_A`; no separatedness or quasi-separatedness occurs. Step 1 follows the source's finite affine-neighborhood choice (lines 819--821): affine opens form a basis, and quasi-compactness supplies a finite subcover. Step 2 follows lines 821--829: principal opens on each affine base-change chart form a basis, and compactness of `V` gives a finite list; the wording explicitly avoids assuming quasi-compact intersections. Step 3 follows lines 829--838: the finitely many tensors have finitely many coefficients, so the generated `k`-subalgebra `A'` is finitely generated, and the finite union of descended principal opens is quasi-compact. Step 4 follows lines 838--848: pullback sends each descended principal open to the original one, giving both inclusions and equality. All four steps are elementary once the definitions of affine basis, quasi-compactness, tensor products, and principal opens are unpacked, so `proof_deps` is correctly empty. I searched the Lean source for an exact declaration and the DAG/blueprint for duplicate statements; none was found. I also checked the small edge cases in the source argument: an empty `V` is handled by the empty finite list, and no coefficient choice depends on separatedness or quasi-separatedness.

5. Incomplete work

None.
