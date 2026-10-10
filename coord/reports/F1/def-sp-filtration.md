# Stage 1 report

## Files written

- `dag/nodes/sec-abelian-varieties/def-sp-filtration.json`: split definition; no child nodes; Mathlib searches found no exact match.
- `citations.json`: empty, because the item is a definition and has no proof steps.

## Attachments

None. I searched the project Lean source for `def-sp-filtration`, the notion's keywords, and the blueprint tag; no sorry-free project declaration states this definition exactly.

## WANTED

WANTED: none. The imported source identifies Stacks Project Definition 12.19.1, Tag 0121; the local blueprint markdown is not materialized in this checkout, but the node statement and citation table provide the source reference.

## Not duplicates

None: this is the sole DAG definition of decreasing filtrations of abelian-category objects; the existing filtration nodes are constructions or theorems that depend on it.

## What was wrong or incomplete

The imported node was still marked `imported` and had no Mathlib search records or completed blueprint `same_as` field. I changed only those bookkeeping fields and marked it `split`; the statement itself agrees with Tag 0121 and was retained. No proof decomposition is appropriate for a definition.

## What I could not finish, and why

No project Lean declaration implements this definition, so there is no attachment. No child statement is needed: the definition introduces the filtration, filtered object, graded pieces, and finite/separated condition directly.

## Review by F1

I read the imported item, its chapter and unit references, the Stacks citation entry for Definition 12.19.1 (Tag 0121), and all existing DAG nodes that cite `def-sp-filtration`. The item hypotheses are exactly an abelian category and an object in it; its clauses define a decreasing integer-indexed family of subobjects, the filtered-object pair, quotient graded pieces, and the finite/separated conditions. Existing uses treat it only as this definition. The Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch: the first three returned only ring/module filtration APIs or no hits, while LeanSearch was unavailable and is recorded as such. I checked small edge cases conceptually: the zero object with the constant-zero filtration satisfies the conditions, and a one-step filtration with `F^0 A = A`, `F^1 A = 0` has graded piece `A`; these confirm the indexing and quotient clauses. Since there are no proof steps, `citations.json` is necessarily empty.

## Second reading by F1

- Item statement: checked against Homology Definition 12.19.1, label `definition-filtered`, Tag 0121, at `/home/ubuntu/c1-stacks-review/homology.tex:4667`; the repaired statement now includes every source clause (decreasing filtration, filtered-object morphisms and category, induced and quotient filtrations, finite, separated, exhaustive) and the graded-piece quotient notation used by dependent nodes. Verdict: repaired and consistent.
- New node `def-sp-filtration`: statement-only form, self-contained abelian-category hypothesis, definition dependency `[def-sp-abelian]`, TeX escaping, and source tag/label checked. Verdict: one valid definition node; no child nodes are needed.
- Proof steps: none, so there are no step dependencies or citations to audit; `citations.json` remains correctly empty.
- Mathlib/project search: LeanFinder, Loogle, grep, and LeanSearch records were checked; the first three found only unrelated ring/module filtration APIs or no match, and LeanSearch was unavailable. Verdict: no Mathlib or project attachment.
- Edge cases checked: the zero object with the constant-zero filtration, a one-step filtration with `F^0A=A` and `F^1A=0`, and arbitrary finite bounds `F^nA=A`, `F^mA=0`; all agree with the repaired definitions.

Changes: corrected the inaccurate `F^0A=A`/single-tail formulation to the source's arbitrary finite bounds; added morphisms, `Fil(\\mathcal A)`, induced and quotient filtrations, separated and exhaustive definitions; recorded the exact source label and tag. The graded-piece clause was retained because existing dependent nodes use `\\operatorname{gr}^nA` through this definition.
