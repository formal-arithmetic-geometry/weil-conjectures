Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-mayer-vietoris-diagram.json` — statement, split; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-mayer-vietoris-open-cover.json` — statement-only support node; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-graded-localization-exact.json` — statement-only support node; no Mathlib match.
- `citations.json` — verbatim statement quotes for every proof citation.

Attachments: none.

WANTED: none.

The imported item had an empty proof despite stating the complete ladder. I kept its mathematical statement and supplied three proof steps. The first uses the open-cover Mayer–Vietoris statement for every graded twist and records the principal-open identities as elementary set identities. The second isolates exactness of homogeneous localization and degree-zero extraction in a new statement-only node. The third obtains the lower row from the same Mayer–Vietoris statement and cites derived-functor naturality for compatibility of restriction, denominators, and connecting maps. No source statement or hypothesis was changed.

## Review by G1

I read the item source as Stacks Project `coherent.tex`, Lemma 09MR, proof paragraph headed by the Mayer–Vietoris argument, and checked the tag references 01EB and 05QB named by the imported record. I searched the whole DAG and blueprint for an existing open-cover Mayer–Vietoris theorem or a graded-localization exactness theorem; none stated the needed facts. I also searched the Lean source for the item id, 09MR, and the relevant Mayer–Vietoris/localization terms; no declaration exists without `sorry`.

Step 1 cites `lem-sc-mayer-vietoris-open-cover`, whose statement explicitly supplies the natural long exact sequence for an open cover. Its hypotheses introduce the scheme, open subschemes, union, and quasi-coherent module. The identities for nonvanishing loci are direct set identities. Step 2 cites `lem-sc-graded-localization-exact`, whose statement says exactly that localization and degree-zero extraction preserve the short exact sequences used termwise. Step 3 cites the same Mayer–Vietoris statement for the localized cover, `def-sc-topological-abelian-cohomology` for long exact cohomology sequences, and `lem-weil-pbc-right-derived-universal-delta-functor` for naturality of connecting morphisms under maps of short exact sequences. The citation quotes were copied into `citations.json` and checked against the source node strings.

I tested the edge cases used by the source argument: `p=0` uses the convention `H^{-1}=0`; `V` contained in `U` makes the cover sequence degenerate in the expected way; and `s=0` makes every principal open empty, so both rows are zero. The new support statements are intentionally unsplit and carry no proof sketch. No hypothesis was added or dropped.
