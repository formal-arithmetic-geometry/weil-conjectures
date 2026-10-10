Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-artin-schreier-k.json`: item split into two proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-artin-schreier-surjective.json`: statement-only child corresponding to the closed project declaration `IsAlgClosed.surjective_pow_sub_self`.
- `citations.json`: verbatim quotes for both cited statements.

Attachments:

- `IsAlgClosed.surjective_pow_sub_self` belongs to the new node `lem-sc-artin-schreier-surjective` (the declaration is sorry-free in `WeilConjectures/Mathlib/FieldTheory/IsAlgClosed/Basic.lean:193`).

WANTED:

What was wrong in the imported material:

The imported proof was mathematically correct but left both its non-elementary clauses uncited and did not distinguish the project theorem that supplies surjectivity from the existing field-kernel result. The split now cites the closed project declaration for surjectivity and the existing node `lem-sc-field-artin-schreier-kernel` for the kernel. The child statement uses the exact hypotheses of the closed declaration, which are slightly more general than the item's positive-characteristic formulation.

What I could not finish:

Nothing. The second reader should verify that the existing field-kernel node's image-of-`ZMod p` formulation is the intended meaning of `\\mathbf F_p` in the item.

## Review by H1

I read the imported item and its blueprint proof, then read `WeilConjectures/Mathlib/FieldTheory/IsAlgClosed/Basic.lean` at the declaration and proof of `IsAlgClosed.surjective_pow_sub_self` (lines 188–197). This declaration states the surjectivity clause under `[Field k]`, `[IsAlgClosed k]`, and `[CharP k p]`, so it is recorded as the closed child `lem-sc-artin-schreier-surjective` rather than reproved. I also opened the existing node `lem-sc-field-artin-schreier-kernel`; its statement explicitly says that the canonical `\\mathbf F_p = \\mathbf Z/p\\mathbf Z` map has image exactly `{x : K | x^p = x}`, under the prime-characteristic field hypotheses. Step 1 uses only the closed child's surjectivity statement. Step 2 first rewrites `x^p - x = 0` as `x^p = x` and then uses exactly the fixed-point/image assertion of that existing node; the rewrite is elementary, while the field fixed-point theorem is the cited non-elementary fact. I checked the small cases `p = 2` and `k = algebraic closure of F_p` informally: the map is the usual Artin–Schreier map and its fixed points are precisely the prime field. I searched the whole DAG and blueprint before creating the child; no existing node states the surjectivity declaration, while the kernel node already exists and was reused. Mathlib searches were run for the item and child with LeanFinder, Loogle, grep, and LeanSearch; the LeanSearch service was unavailable and is recorded as such, and the exact surjectivity declaration was found in the project extension rather than Mathlib.

## Second reading by H1

- Item statement: checked against the blueprint node and project declaration; the field, characteristic, surjectivity, and kernel clauses agree.
- Step 1: checked against `IsAlgClosed.surjective_pow_sub_self` (lines 193–197); the cited child states precisely the surjectivity used.
- Step 2: checked against `lem-sc-field-artin-schreier-kernel`; its image is exactly the fixed-point set `x^p=x`, and the rewrite from `x^p-x=0` is elementary.
- New node `lem-sc-artin-schreier-surjective`: statement-only and self-contained through its field and characteristic definition dependencies; source, closed declaration, and recorded searches were checked.
- Existing-node search: the DAG and blueprint were searched for both formulations; the kernel node was reused and no duplicate surjectivity node exists.
- Edge cases checked: `p = 2`, `k = algebraic closure of F_p`, and the child theorem's permitted characteristic-zero specialization.

Changes: no mathematical statements or proof steps required correction; appended this second-reading record only. Citations remain verbatim.
