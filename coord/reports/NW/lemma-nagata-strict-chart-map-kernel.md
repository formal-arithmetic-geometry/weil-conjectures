# Worker report: lemma-nagata-strict-chart-map-kernel

## Files written

- `dag/nodes/sec-nagata-compactification/lemma-nagata-strict-chart-map-kernel.json`: statement, split; seven actual Mathlib searches give no exact match or one-line specialization. Three proof steps, no new nodes and no new Mathlib leaves.
- `citations.json`: nine verbatim statement excerpts, one for every step/node citation.
- `report.md`: this report. The search command maintains `searches.jsonl`; all seven results were read and retained.

## Attachments

None submitted. The earlier attempt recorded that its dispatcher had forbidden repeating a rejected attachment; that historical observation is retained. This return requests rebasing and redelivering the approved stage-1 split, so I have not replaced that delivery with the former attachment claim. The present read clone does contain `WeilConjectures/Blowup/Affine/StrictTransformChart.lean`, including `AlgebraicGeometry.AffineBlowup.ker_strictChartMap` at line 220 and the elementary denominator calculation at line 111. This is different from the clone described in the rejection. I read it as reference material, ran no compiler, made no attachment claim, and completed the authorized natural-language split.

## WANTED

None. The current blueprint, the master proof, Stacks algebra.tex, and the needed existing nodes are available locally.

## What needed repair

The master proof deduces that the chart-map kernel is the localization kernel from a description of the image and surjectivity. That inference omits the essential comparison between the localized tensor chart and B_b. The current main-20261015 blueprint gives the kernel statement and keeps its proof in the separate `lemma-nagata-strict-chart-map-kernel.proof.md`; that proof contains the same omitted comparison. The previous report had incorrectly said there was no proof, because it read only the statement file; this repair reads both files. Step 1 now proves the needed elementwise denominator calculation explicitly; step 2 uses the existing power-torsion/localization-kernel statement in B. Surjectivity is neither needed nor cited. The statement now introduces its previously inherited ring map, ideal, element, chart algebra, and scalar action explicitly, without changing the assertion or adding a hypothesis. This is not a statement dispute.

I preserved the import metadata and blueprint_update verbatim. The item's blueprint.from remains null because it is itself an imported blueprint node; same_as is now the searched empty list. No chapter or unit record changed. This is not the unit's key node.

## Not duplicates

No new nodes. Whole-blueprint searches for power torsion, kernel statements and chart normal form, and DAG/Lean searches for tensor-localization and chart maps, led to reuse of the existing chart normal-form node, chart definitions, generic tensor-algebra leaf and power-torsion localization-kernel node. The common-denominator computation is a short explicit application of the existing normal form and tensor relations, not a new stand-alone lemma.

## Review by NW

I read the current main-20261015 item, the master's proof, the chapter and unit records, and SETUP's three-level rule. The unit calls for quotienting the pulled-back chart by a-power torsion; the split follows that route. I read Stacks Tag 052Q (`definition-blow-up` and its following fraction description), Tag 0BIP (`lemma-blowup-base-change`, both its assertion and proof), and Tag 00CO (`definition-localization` and the following paragraph giving the zero criterion), checked against the local tags table. The common-denominator detail is my explicit expansion of that chart argument, so proof_origin is agent, not an attribution of an unwritten proof to Stacks. There are no new nodes requiring separate source review.

For step 1 I read the statements of `def-nagata-strict-transform-basechange-chart-ring`, `lemma-nagata-chart-ring-normal-form`, `def-nagata-blowup-chart-ring`, and `lem-weil-pbc-algebra-tensor-pushout-universal-property`. The base-change definition gives C=B⊗_A A[I/a] and its structural A-action; the normal-form lemma gives exactly c_i=x_i/a^{n_i}; the chart definition embeds the chart in A_a, so a^{n_i}c_i=x_i really holds in the chart. Clause (1) of the tensor-algebra leaf supplies the multiplication and factor maps. Finite sums of pure tensors and their balancing relations are the elementary construction of the module tensor product. The displayed calculation gives alpha^N z=iota(w), with w explicitly specified. N is the sum of the finitely many exponents, so N-n_i is nonnegative, including the empty-sum case. No injection B->C or cancellation in C is assumed. This explicit finite-sum step contains no uncited comparison theorem or generic lemma hidden behind 'clear denominators'.

For step 2 I read the full statements of `def-nagata-strict-chart-to-extended-blowup-chart`, `lemma-nagata-power-torsion-kernel-localization`, and `def-nagata-power-torsion`. The map definition says sigma is a B-algebra map into a literal subalgebra of B_b; it gives both structural values used. The localization-kernel lemma is used for M=B over B and element b, and gives b^m w=0 from w/1=0. It is not used to assume that C->B_b is already a localization. The final multiplication alpha^m iota(w)=iota(b^m w) follows from the factor homomorphism and alpha=iota(b). Thus every non-elementary input is precisely the statement cited, not material from a cited proof.

For step 3 the same map definition and the power-torsion definition suffice. Invertibility of b/1 in B_b is the explicit fraction relation (b/1)(1/b)=1. Multiplication by its inverse and injectivity of a subalgebra inclusion prove the reverse inclusion. This is elementary even if the localization is the zero ring; there is no nonzero-ring assumption.

I checked the following cases. If a is a unit, A[I/a]=A, C=B, sigma is the identity, and power torsion is zero. If a is nilpotent (including a=0), A_a and the chart are zero, so C=0 and the assertion holds. If b=0 while a is not nilpotent in A, alpha=0 and the target is zero, so both ideals are all of C. If B=0, all objects are zero. For a nonflat example take A=k[x,y], I=(x,y), a=x, B=A/(y)=k[x]: C=k[x,t]/(xt), the target is k[x], and sigma sends t to zero; its kernel (t) is exactly the x-power torsion. This tests the point where incorrectly assuming tensoring preserves injectivity would fail. No finite-generation, flatness, noetherianity or nonzerodivisor hypothesis is used.

I reviewed delivery-errors B through E point by point: all objects are introduced, TeX has single escapes after JSON decoding, actual search results are recorded, every cited statement was opened, citations.json quotes are verbatim, there are no new nodes or clause relabelings, and the proof carries both inclusions. All proof steps are shorter than 2000 characters. The only off-unit statement is the generic tensor-algebra Mathlib leaf, declared in split_report.tool_uses. The dependency union equals proof_deps. No SGA source, Lean writing, compilation, repository mutation, launcher edit, or agent delegation occurred.

## Unfinished work

No mathematical work left for this one-level split. Server validation and direct delivery are performed with the required unmodified tools; their successful result is recorded below when complete.

## Repair of the 2026-10-21 return

The return identifies branch head `6418af0b72b`: the reader approved the mathematics, but the landing refused the side-project completion because it had not been promoted to the live DAG used by the queue. I retained the delivered proof, all seven logged Mathlib searches, citations and the previous review. I compared the retained item field by field with the current shared DAG: the live item is still imported, with the original abbreviated statement and the invalid image-to-localization-kernel inference; it has no newer reviewed split to overwrite. All original import fields, the source record, chapter, unit and blueprint_update agree and remain untouched. The delivery tool prepares the commit on the fetched current base rather than re-pushing the returned commit. Its initial repair dry run exited successfully with `OK (not pushed)` at `5541b614f8c`.

I reread every current dependency, rather than assuming that only the rejected item's file mattered: `def-nagata-power-torsion`, `def-nagata-strict-chart-to-extended-blowup-chart`, `def-nagata-strict-transform-basechange-chart-ring`, `lemma-nagata-chart-ring-normal-form`, `def-nagata-blowup-chart-ring`, `lem-weil-pbc-algebra-tensor-pushout-universal-property`, and `lemma-nagata-power-torsion-kernel-localization`. The chart-map definition now carries the reviewed Q139 construction by localization restriction and the tensor universal property. Its statement explicitly makes sigma a B-algebra map into a literal subalgebra of B_b, exactly what steps 2 and 3 require; the citation excerpts now include that construction. The other six statements still supply precisely the torsion definition, tensor chart with structural A-action, normal form, subalgebra inclusion, tensor multiplication/factor maps, and localization zero criterion used in the retained argument. None is merged into another id, and none introduces an extra flatness or nonzerodivisor hypothesis.

The repaired step 1 explicitly cites the current base-change chart definition for C and its structural scalar action, making that formerly implicit input auditable in citations.json. All nine excerpts are checked verbatim against the current node statements. The proof-dependency union is regenerated, both kernel inclusions remain explicit, no new node or Mathlib leaf is created, and all steps remain below 2000 characters. I also corrected the report's claim that the main blueprint had no proof by reading its separate proof file. This is a documented repair of the existing split, not an unchanged re-push; promotion of side completion remains the maintainer's action identified by the return, and I change no completion/queue metadata myself.
