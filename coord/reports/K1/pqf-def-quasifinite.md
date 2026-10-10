Files written:

- `dag/nodes/sec-nagata-compactification/pqf-def-quasifinite.json`: definition node, no child nodes, no Mathlib leaf.
- `citations.json`: empty because the item is a definition with no proof steps.

Attachments: none.

WANTED: none.

The imported node was not an attachment: no declaration under `WeilConjectures/` carries the `(blueprint: pqf-def-quasifinite)` tag or states this combined definition without `sorry`. Mathlib supplies component notions (`LocallyQuasiFinite`, ring-level `QuasiFiniteAt`, and finite-fibre lemmas), but no single declaration matches the Stacks Tag 01TD definition together with the separately stated finite-fibres convention. The statement and its dependency on `def-weil-pbc-scheme-conventions` were left unchanged. No new node is needed because this is a definition node and no proof argument is being split out.

## Review by K1

I read the item source recorded in the node (`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-zmt/pqf-def-quasifinite.md`) and checked it against Stacks Project Definition 29.21.1, Tag 01TD. The statement introduces the morphism, affine neighbourhoods, finite-type and ring-level quasi-finiteness conditions, local and global quasi-finiteness, finite fibres, and the scheme-theoretic fibre. Its only statement dependency is the existing conventions node, which supplies the scheme, affine, and finite-type terminology. There are no proof steps, so there are no cited-step quotes or hypotheses to verify in `citations.json`.

I searched the whole DAG and blueprint for the item and for the component notions; no duplicate definition node was found. I also inspected Mathlib's `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean` and ring quasi-finiteness sources. The recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results establish that Mathlib has only component declarations, not this bundled Stacks definition. I tested the boundary cases conceptually: a finite morphism is locally quasi-finite and has finite fibres, while a locally quasi-finite non-quasi-compact morphism need not be globally quasi-finite, so the separate clauses must remain explicit.

## Second reading by K1

- Item statement: checked against Stacks Tag 01TD, Definition 29.21.1, clauses 1–3; all hypotheses and conclusions agree, including the affine-local witness, locally quasi-finite clause, and finite-type plus isolated-fibre clause.
- New node `pqf-def-quasifinite`: checked as a statement-only definition against Tag 01TD and the project blueprint; it is self-contained, uses the existing scheme-conventions dependency, and has no proof steps or citation obligations.
- Mathlib status: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch searches; no single declaration matches the bundled Stacks definition, so no Mathlib leaf or child node should be added.
- Edge cases: checked a field-valued point, the empty scheme, a finite disjoint union of points, and the distinction between locally quasi-finite and globally quasi-finite morphisms; no clause is weakened or false.
- Changes: none to the node or searches; added this second-reading audit section as required.
