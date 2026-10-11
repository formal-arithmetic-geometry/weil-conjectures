Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-triangle-morphism-category-05r9.json`: split target, 0 Mathlib leaves.
- `dag/nodes/sec-smooth-purity/lem-pur-triangle-completion-ms6-05r9.json`: new statement node, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-triangle-common-refinement-ms3-05r9.json`: new statement node, no Mathlib match.

Attachments: none.

Source read: `/home/ubuntu/c1-stacks-review/derived.tex`, Lemma Tag 05R9 proof (the sandbox repository does not vendor this file).

The item was unsplit. No exact declaration carrying the blueprint tag or the 05R9 statement exists under `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2`. The available Mathlib APIs cover generic triangle completion and filtered-category notions, but not the saturated-system denominator construction or the resulting triangle-morphism category, so the item is not a Mathlib leaf.

## Review by J1

I checked the target statement against Stacks Tag 05R9 and `def-pur-saturated-triangulated-localization`: objects are the opposite (cofiltered) orientation of the source's morphisms of distinguished triangles, with all three components in `S`, and arrows are commuting triangle morphisms over the fixed triangle. The first proof step uses the completion helper's MS2/MS6 assertion; rotation supplies the Y and Z cases. The second step uses the common-refinement helper together with the filteredness of `S/X` to establish cofilteredness. The third step uses the filtered common-target/equalization argument in `S/X`, then completion and rotation, which is the definition of initiality. I verified every cited quote is copied verbatim into `citations.json`, and recorded the LeanFinder, Loogle, grep, and unavailable LeanSearch results for both new statements. Small edge cases are consistent: identity denominators give the identity triangle morphism, and the zero triangle and singleton index satisfy the cofiltered and initial conditions.

The helper proofs remain statement-only stage-1 nodes, as required; no Lean code was written or compiled for this statement split.

## Not duplicates

lem-pur-triangle-completion-ms6-05r9 vs lem-pur-triangle-morphism-category-05r9: the helper asserts only existence of a triangle morphism extending one prescribed denominator; the item additionally defines the whole category, proves cofilteredness, and proves initiality of all three projections.

lem-pur-triangle-common-refinement-ms3-05r9 vs lem-pur-triangle-morphism-category-05r9: the helper gives finite common refinements and equalizers of already-given triangle morphisms; the item packages these facts with the category definition and derives cofilteredness and projection initiality.

## Second reading by J1

- Item statement: checked against Stacks Derived Categories Lemma 05R9 (label `lemma-limit-triangles`, `/home/ubuntu/c1-stacks-review/derived.tex`, lines 1596--1750) and `def-pur-saturated-triangulated-localization`; verdict: the cofiltered statement is the opposite indexing category to the source's filtered category, with the same objects and projections `S/X`, `S/Y`, `S/Z`.
- Item step 1: checked against 05R9's MS2/MS6 construction and the completion helper; verdict: prescribed denominators are lifted to triangle morphisms, and rotation supplies the other two vertices.
- Item step 2: checked against 05R9's filteredness condition (2), MS2, MS6, and both helper statements; verdict: common targets and commuting triangle squares are now stated explicitly.
- Item step 3: checked against 05R9's cofinality paragraph and the definition of `S/X`; verdict: the argument now includes the filtered `S/X` common-target/equalization step before lifting and rotation.
- `lem-pur-triangle-completion-ms6-05r9`: checked against 05R9's MS2 then MS6 construction; verdict: self-contained denominator-extension statement, with all triangle data and components in `S` named.
- `lem-pur-triangle-common-refinement-ms3-05r9`: checked against 05R9 filteredness conditions (2) and (3); verdict: repaired to define `\\mathcal I`, its arrows, and componentwise equalization explicitly.
- Mathlib searches: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch results in `searches.jsonl`; verdict: no exact Mathlib theorem, so both helpers remain unsplit statement nodes.
- Small cases: identity denominators give the identity triangle object; the zero triangle and a singleton indexing category satisfy the stated cofiltered and initial conditions.

Changes made: repaired the common-refinement statement's missing category definition; expanded item steps 2--3 with the MS2/MS6 and `S/X` filteredness arguments; updated `citations.json` with verbatim quotes for every newly cited node; corrected the source review to the available Stacks file.
