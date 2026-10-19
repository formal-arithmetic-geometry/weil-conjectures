## Worker report

Files written under `dag/nodes/sec-purity-real-sheaves/`:

- `lem-a1-affine-groupoid-polynomial-norm-invariant.json`: item, split in three steps; no new DAG nodes.

`citations.json` records the verbatim quote for the scalar invariant-norm statement used by step 2. The item’s four original Mathlib searches and the additional second phrasing were run with `msearch.py` and are recorded in `searches.jsonl`.

Attachments: none. A search of `WeilConjectures/` for the item id, its mathematical terms, and the blueprint tag found no exact sorry-free declaration. The existing scalar node `lem-a1-affine-groupoid-invariant-norm` is a cited prerequisite, not an attachment.

WANTED: none; the Stacks sources are present locally.

The imported statement is unchanged. I retained the explicit “no constant rank” hypothesis. I initially considered citing the constant-degree norm-characteristic-polynomial node, but removed that citation because its hypothesis is a globally fixed degree and therefore does not cover this item. The final proof uses only finite-locally-free base change (elementary from Tag 02DV), the existing scalar invariant-norm statement, and coefficient comparison.

Nothing remains unfinished. No Lean was written or compiled, and no compiler, Lake, or local DAG/review tool was run. The required server `check_dag` preflight passed before this report was written.

## Not duplicates

`lem-a1-affine-groupoid-polynomial-norm-invariant` vs `lem-a1-affine-groupoid-invariant-norm`: the existing node treats one element of `A` and proves scalar norm invariance; this item applies that result after adjoining `T` and states invariance for every polynomial `F` together with the equalizer identification `C[T]`.

## Review by Q62

I read the item node, `lem-a1-affine-groupoid-invariant-norm`, and the Stacks sources `groupoids.tex` Tag 03BH and `exercises.tex` Tag 02DV(1),(3). The item’s affine schemes, functorial groupoid structure, finite-locally-free source and target, coefficientwise maps, equalizer `C`, and absence of constant-rank or reducedness assumptions agree with the source route. Tag 03BH proves scalar norm invariance by the groupoid composition diagram and norm base change; the polynomial paragraph of 03BJ applies the same argument after taking the product with the affine line.

Step 1 is the product construction: coefficientwise structure maps preserve all groupoid identities, and finite locally free morphisms remain finite locally free after the polynomial base change. This is marked elementary and does not smuggle in a global rank. Step 2 instantiates the cited scalar node with rings `A[T]`, `B[T]` and element `F`; its statement explicitly gives the norm in the source/target equalizer, and its local determinant characterization is the `Q_F` norm in the item. Step 3 compares coefficients of the two coefficientwise polynomial maps, which is elementary and gives exactly `C[T]` and the displayed equality in `B[T]`.

I checked the edge cases of the identity groupoid, the empty/zero-ring case, a disconnected affine with different finite-locally-free ranks on components, and a nonreduced ring. None requires reducedness, a global degree, or faithful flatness. The existing scalar node is strictly weaker and is the only non-elementary citation. The server `check_dag` check passed; no statement correction or source dispute was needed.
