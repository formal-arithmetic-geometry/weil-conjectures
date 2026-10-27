# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-generically-finite-quasifinite-over-dimension-one.json`: existing statement, now split by applying the identical existing reviewed lemma; no Mathlib match.
- `citations.json`: Step 1's two cited statements, copied verbatim.
- `report.md`: this report and self-review. Search responses are retained as `search-result-0.txt` through `search-result-4.txt`, and msearch.py recorded the five calls in `searches.jsonl`.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searches in `lean/WeilConjectures/` for the item id, its blueprint tag, generically-finite language, and the expected notions found no declaration stating the item. The related projective-space generic-finiteness theorem is only a nonempty-open finiteness result, not this statement. The identical existing DAG node records a former `Sheaf` theorem, but its module was deleted as dead code, its Lean audit is `none`, and it is not a project declaration under `WeilConjectures/`. It is used as an existing stage-1 statement, not claimed as a finished Lean attachment.

## WANTED

None. The source is present at `literature/stacks-project/varieties.tex`, Tag 0AB6, label `lemma-quasi-finite-in-codim-1`, lines 3187–3274.

## Findings and changes

The imported statement is correct and unchanged. It is exactly condition (1) of Stacks 0AB6, including algebraic rather than separable generic residue extensions and only a Noetherian dimension-at-most-one hypothesis on the chosen local ring. The source first reduces (1) to (2), localizes at the target point, passes to reduced components, and uses the dimension inequality; the existing reviewed node already splits those arguments. No additional hypothesis should be introduced here.

The whole-DAG search found `lem-per-generically-finite-quasifinite-over-dimension-one`, whose statement is character-for-character identical to this item's. That node is `split` and independently reviewed. Its 117-node statement/proof dependency closure does not contain this item, so citing it creates no cycle. I reused it instead of making another copy of its localization and dimension argument. The existing lemma is a generic scheme-theoretic tool, not a perverse-sheaf theorem; its cross-unit use is declared in `split_report.tool_uses`. The item's inherited blueprint ancestry has `from.node: null`, as confirmed by `tools/blueprint_refs.py ancestor`; its already specific `from.place` is retained. Whole-blueprint searches by 0AB6 and generic-finiteness language found no imported blueprint node stating this result. `same_as` remains empty; the matching per-node lemma is itself created, not imported.

The existing Mathlib search results were read and retained. Five fresh calls through msearch.py are appended verbatim, including two semantic phrasings, Loogle, LeanSearch, and grep. The semantic results define locally quasi-finite morphisms, give finite-morphism consequences, or assume quasi-finiteness to deduce finite residue extensions. Reading `Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean` confirms that the returned definitions, permanence, and finite-fibre criteria do not give 0AB6 from the hypotheses here. Loogle and grep returned no hits. No result is treated as an exact match or one-line specialization.

## Not duplicates

There are no new nodes. The item and `lem-per-generically-finite-quasifinite-over-dimension-one` are exact duplicates already present in the live repository; Step 1 cites the latter. I do not edit or merge another group's node. This is reuse of an existing reviewed statement, not creation of a node restating the item (delivery-errors D1/D2).

## Review by Q06

I read the source statement and full proof of Stacks Tag 0AB6, label `lemma-quasi-finite-in-codim-1`, in varieties.tex. Condition (1) states precisely the item's generic-residue algebraicity hypothesis. Its base ring condition concerns only the local ring at s; the source does not require a globally Noetherian target, properness, or normality. Both copies of the DAG statement retain those distinctions. I also read the chapter record `sec-six-functors-basics` and inherited unit `sk-thm-sf-ctf-stability`; this is the existing generic algebraic-geometric prerequisite in the inherited 0BFP codimension-one branch, not a replacement of a step in the unit.

Step 1 uses the statement of `lem-per-generically-finite-quasifinite-over-dimension-one`, which I opened and compared directly. Both quantify over the same schemes, the same locally finite type g, the same point s, the same Noetherian local ring with Krull dimension at most one, and every generic point of every source irreducible component with the same algebraic residue extension. Both conclude quasi-finiteness at every point over s. No conclusion from the cited lemma's proof is used in place of its statement. The explanatory definition citation `pqf-def-quasifinite` was opened too: it supplies pointwise affine-neighbourhood quasi-finiteness, not merely global quasi-finiteness or finiteness of all fibres. Both exact source statements are in citations.json. This closes C1 and C4 without any hidden non-elementary inference. Step 1 is under 2000 characters.

For B1–B9 and C5, there is no new object, new statement, or new node to audit. I searched the entire live DAG by Stacks tag and generic/quasi-finiteness concepts, and the imported blueprint with blueprint_refs.py. The exact pre-existing statement is reused, and its status, review, and closure were checked. The source is cited by both tag and label; TeX is preserved, and no definition is altered. The five Mathlib searches are actual msearch.py calls, with their complete output retained and their precise queries appended to the item's existing records. There is no fabricated search or unavailable service called a negative result.

For D1–D5, the single application points to an already split reviewed node, not a new node or a new clause moved out of the item. Its proof independently carries the source's vertical/horizontal component arguments; no circular reference to this item occurs anywhere in its closure. Since the theorem is already present verbatim, reproducing its ten-step proof would duplicate existing DAG work.

For E1–E7, the application requires no extra hypotheses. The dimension-zero local base is explicitly included by the cited statement, as are empty fibres, empty source, nonreduced schemes and inseparable algebraic generic extensions. As small checks, the empty source gives a vacuous conclusion; a finite field extension over a field meets the dimension-zero case; the identity of a DVR and a closed finite point over its residue field meet the horizontal and vertical dimension-one cases. A1 over a field fails the generic-algebraicity hypothesis, so its positive-dimensional fibre is not a counterexample. The blowup of A2 at the origin is generically birational but has a positive-dimensional exceptional fibre; the target local dimension there is two, outside the lemma. These tests preserve the necessary dimension and algebraicity hypotheses. I corrected no mathematical statement: the only change is replacing the empty proof by the explicit application of the existing exact theorem.

## Unfinished work

None in this stage-1 item. The cited lemma's downstream proof nodes remain the existing shared DAG's work; no Lean file was written, no compiler or build was invoked, and no repository or launcher file was modified.

## Validation

The required delivery dry run will run on the server, followed by push only after it reports OK.
