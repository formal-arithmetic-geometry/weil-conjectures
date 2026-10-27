# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-field-extension-component-local-dimension.json`: existing statement, now split in five steps; statement unchanged; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-locally-algebraic-dimension-components.json`: new statement-only, unsplit lemma; no Mathlib match after two semantic formulations, LeanSearch, Loogle and source searches. No Mathlib leaves were created.
- `citations.json`: every use in every item step has a verbatim quote from the cited statement. `searches.jsonl` retains the search command's actual records.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint id and dimension/field-extension concepts found no declaration stating every clause of the item. `AlgebraicGeometry.topologicalKrullDimAt_spec_tensorProduct_field_extension` in `AlgebraicGeometry/DimensionAtPointFieldExtension.lean:108` is the affine-algebra local-dimension equality only, not the scheme/component statement. Its existing DAG node is `lem-weil-pbc-dimension-at-point-field-extension`. `AlgebraicGeometry.dimension_locally_algebraic` handles an irreducible scheme, not the maximum over components of an arbitrary scheme. Neither is an attachment for this item or the new node.

## WANTED

None for the mathematical proof. All sources used are present. The inherited brief requests `coord/dag-sync.md`, which is absent in this clone; the current dispatch supplies the live-repository read-only and delivery rules used here.

## Audit of the imported node and route

The initial node had a correct statement but no proof. No statement dispute or correction was necessary. Its old searches, source, creation metadata and blueprint ancestry were retained. The source means local topological dimension (minimum of dimensions of open neighbourhoods), not dimension of a stalk. In particular a generic point of an affine line has local topological dimension one but stalk dimension zero. A proof using only prime height would therefore prove the wrong assertion.

I read the chapter record `sec-trace-formula`, the unit record `sk-i-curve-zero`, the current blueprint text of `lem-trf-local-term-locality`, and the parent `lem-trf-flat-dense-generic-fibre-pure-dimension`. The parent needs the present equality in its field-extension step after obtaining constant local dimension of an ordinary fibre. This split supplies that existing dimension-theoretic input below the semistable-alteration branch recorded in the item's ancestry. It changes neither the unit nor the chapter route. `lem-sc-fibre-dimension-after-base-change` is declared in `split_report.tool_uses`: it is a generic dimension tool, not a replacement for a trace-formula argument. The other off-unit results used are existing Mathlib leaves or definitions.

## Not duplicates

lem-trf-locally-algebraic-dimension-components vs lem-trf-field-extension-component-local-dimension: the new node is the maximum formula at an arbitrary point of one locally algebraic scheme; it contains no field extension, local-Noetherian conclusion or component-generic-point assertion. The item's steps prove these clauses using base change, sobriety and maximality, rather than restating them as a new node.

lem-trf-locally-algebraic-dimension-components vs lem-weil-pbc-dimension-at-point-components: the existing result assumes the scheme is the spectrum of one finite-type algebra; the new result allows arbitrary locally finite type schemes, including non-quasi-compact ones. Extending the affine formula requires the affine-component correspondence and preservation of component dimensions on nonempty opens, precisely the non-elementary argument in the proof of Stacks 0B1B. It is not a one-line specialization of the affine statement. The future proof of the new node should reuse that affine node.

lem-trf-locally-algebraic-dimension-components vs lem-sc-dimension-locally-algebraic: the existing statement assumes irreducibility and gives constant dimension on nonempty opens and at all points. It does not give the maximum over different components of a reducible scheme.

lem-trf-locally-algebraic-dimension-components vs lem-sbc-equidimensional-open-local-dimension: the existing result assumes every component has the same prescribed dimension; the new result computes the maximum without equidimensionality.

lem-trf-locally-algebraic-dimension-components vs lem-sbc-constant-local-dimension-components: the existing result assumes constant local dimension and concludes constant component dimensions, whereas the new result starts from an arbitrary locally algebraic scheme and computes its point dimension from its components.

Before creating the node I searched the whole DAG by 0A21, 0B1B, maximum/component/local-dimension wording and existing dimension-node ids. I also ran `tools/blueprint_refs.py search` for `0A21`, `0B1B`, `local dimension`, `dimension.*field` and `irreducible component`, and obtained the blueprint ancestor using the prescribed command. No blueprint node states the new formula. The new node cites the precise item tag 0B1B rather than the surrounding eleven-part tag 0A21. Its `blueprint.from.node` and `via` follow the existing ancestry, with this item prepended.

## Review by N6

I read `morphisms.tex` at label `lemma-dimension-fibre-after-base-change` (02FY), especially its first clause, and `lemma-finite-type-noetherian` (01T6). I also read `varieties.tex`, `lemma-dimension-locally-algebraic`, statement and proof of item `item-dimension-irreducibles-passing-through` (0B1B, part (5) of 0A21), and `schemes.tex`, `lemma-scheme-sober` (01IS). The tag-to-label mapping confirms each reference. The item agrees with these sources for arbitrary fields and extensions, and the new node is exactly the first equality of 0B1B. Locally algebraic here means locally of finite type over the given field; no algebraic closedness, reducedness, separatedness or global finite type is needed.

Step 1 cites `lem-weil-pbc-lft-base-change`, whose statement actually asserts local finite type of the second projection after arbitrary base change, and `pqf-lem-locnoeth-lft`, whose statement makes the source locally Noetherian from that hypothesis and a locally Noetherian target. I verified both statements. `pqf-def-locnoeth` supplies the affine-cover definition. The field is Noetherian by the written two-ideal argument, so the target hypothesis holds without a hidden finiteness condition on the extension.

Step 2 cites `lem-sc-fibre-dimension-after-base-change`, whose displayed statement gives exactly the equality at the two points of the corresponding fibres. I checked its locally finite type hypothesis against the given g, not against the projection p. `def-pc-scheme-fibre` supplies the fibre/topological-inverse-image identification. Over a field's single point the canonical residue-field morphism is the identity, so these are the original schemes. I read `def-kun-dimension` and `def-kun-topological-dimension-at-point`: both use the same minimum of neighbourhood Krull dimensions. This accounts explicitly for the notation used in the existing base-change node.

Step 3 uses `lem-sc-scheme-sober`, whose statement explicitly includes existence and uniqueness for every irreducible closed subset, in particular every component. It is not a citation of the generic-point definition for an existence claim.

Step 4 uses `def-sc-generic-point`, `def-weil-irreducible-components` and the new maximum formula. I read each statement: closure of the singleton is D; components are maximal irreducible subsets and are closed. Thus any component E containing z contains D by closedness and equals D by maximality. This is the written elementary argument making the maximum a singleton. The non-elementary input is the maximum formula, not hidden in the word generic. Its locally finite type hypothesis follows from step 1. Equality from step 2 then completes the required chain. The new node is not proved here and has empty proof, proof dependencies and null proof origin.

Step 5 substitutes the constant-dimension hypothesis at p(z). Its only citation is the fibre-product definition for the projection used in the empty case; there is no additional purity theorem being invoked. It is elementary. All non-elementary facts in the other steps have statement citations and matching quotes. No step exceeds 2000 characters; no long argument hides an uncited comparison lemma.

I tested the new maximum formula on empty X (no x), a point over a field, the affine line including its generic point, a disjoint union of a point and an affine line, intersecting components of unequal dimensions (the maximum is the larger dimension at their intersection), and an infinite disjoint union of affine spaces (no global dimension bound is assumed). I also checked the item's arbitrary-extension quantifier against a purely inseparable extension producing a nonreduced base change: the topology and dimensions, rather than reducedness, are what the formula uses. These tests show why neither irreducibility nor separability should be added. The new statement introduces every object, cites each specialized notion (including subspace topology), uses ordinary TeX escaping, and contains no proof sketch. No sources prohibited by the route lock are used.

## Unfinished work

No part of the item's split remains open. The one new lemma remains statement-only as required for a one-level stage-1 delivery. This is not a Lean proof or a claim of finished transitive dependencies.
