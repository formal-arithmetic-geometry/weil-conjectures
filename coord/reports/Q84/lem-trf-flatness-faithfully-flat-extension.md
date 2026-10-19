# Stage-1 report: lem-trf-flatness-faithfully-flat-extension

## Files written

- dag/nodes/sec-trace-formula/lem-trf-flatness-faithfully-flat-extension.json: statement; split into four elementary steps using three existing Mathlib definition leaves. The statement is unchanged. No new nodes and no new Mathlib leaves.
- citations.json: one verbatim statement quote for each node cited in each proof step.
- searches.jsonl: six actual searches made by msearch.py; all services used answered successfully. The item's four inherited Q91 search records are retained; the six Q84 records are appended, with the exact logged query texts.
- report.md: this report.

## Attachments

None. I searched WeilConjectures/ by the exact blueprint tag/id, faithfully-flat terminology, and flat/tensor criteria. The project declaration Module.Flat.of_flat_of_faithfullyFlat at WeilConjectures/Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean:55 is proved, but only says that C faithfully flat over B and A-flat implies B A-flat. It does not state the arbitrary B-module N assertion. Therefore it cannot finish this item. No Lean files were written or compiled.

## WANTED

None. All sources used are available locally.

## Problems found and corrected

The item is precisely Stacks Algebra Tag 0584, lemma-flatness-descends-more-general, part (2), with R=A, S=B, S'=C and M=N. Its hypotheses and both conclusions are correct. In particular, C need not be flat over A, and N need not be flat over B. I kept the statement, statement dependencies, source, chapter and unit.

The existing Mathlib result Module.Flat.iff_flat_tensorProduct (Flat/FaithfullyFlat/Basic.lean:601) compares flatness of N over B with flatness of C tensor_B N over C, assuming C faithfully flat over B. Our statement compares both modules over A. Substituting A for B would require faithful flatness over A, which is not a hypothesis. The candidate is not a match. I also read of_flat_tensorProduct at :588 and lTensor_injective_iff_injective at :385. Mathlib's Flat.trans and instTensorProduct have other base-ring hypotheses and are tools rather than one-line statements of this item.

The inherited blueprint locator called relative-flatness detection the final sentence of lem-trf-local-term-locality proof (1)--(2). The current main-20261015 proof instead quotes the specialization-to-the-normal-cone route of Varshavsky. The detection lemma is a descendant in the semistable-alteration/flattening refinement, not a literal sentence in that blueprint file. I made this distinction explicit in blueprint.from.place and split_report.blueprint, and expanded via from the current parent lem-trf-relative-flatness-source-cover. The nearest blueprint ancestor remains lem-trf-local-term-locality; no route or unit is changed.

## Unfinished work

None for this one-level split. No new statement-only children are needed: the existing tensor-product universal property and exactness definition of faithful flatness suffice for the short arguments written in the item. This is not an attachment and is not claimed to be a single Mathlib leaf.

## Not duplicates

No new nodes were created. I searched all dag/nodes for Tag 0584 and for flatness/faithfully-flat/tensor-reassociation facts and searched the entire blueprint with blueprint_refs.py (faithfully flat, flatness, tensor associativity). The exact 0584 statement was only the item. lem-weil-pbc-flatness-descends-faithfully-flat is the different same-base 00HJ statement described above; lem-weil-pbc-flat-algebra-faithfully-flat-descent is the algebra-only case. Existing tensor-cancel-base-change cancels a factor B in a scalar extension, whereas the needed comparison interchanges C with the test module U around N; its two maps and their naturality are elementary and are proved here rather than generating another node.

## Review by Q84

I read algebra.tex Tag 0584, lemma-flatness-descends-more-general, statement and entire proof at lines 8930--8957, together with Definition Tag 00HB, definition-flat, items (2) and (4), and Lemma Tag 00HD, lemma-flat, injection criterion. I also read the balancing setup and Tag 00D2, lemma-tensor-with-bimodule, and morphisms.tex Tag 02JZ, lemma-flat-permanence, which is the parent application. No SGA source is used. There are no new nodes needing a separate source audit.

I opened the full statements of all three cited nodes. def-weil-pbc-flat-ring-map explicitly defines flatness by preservation of injections. def-weil-pbc-faithfully-flat-ring-map explicitly states reflection and preservation of exactness for every complex of B-modules. def-weil-pbc-module-tensor-product supplies the universal property, generation by pure tensors, and induced-map formulas. Each citation in citations.json is copied verbatim from the corresponding statement, not from its proof or Mathlib metadata.

Step 1 uses the faithful-flatness definition with the complex 0 -> P -> Q. Exactness in the middle is precisely zero kernel; tensoring the zero module is zero by the bilinearity/generation assertions of the tensor-product node. This is why injectivity reflection follows from the actual cited statement, without a missing kernel-base-change theorem. There is no assumption that g is already injective in the reflection direction.

Step 2 uses only the tensor-product node. I checked that U tensor_A N is a B-module via N, that the displayed interchange map respects both A- and B-balancing, and that the inverse respects the same relations. The composites fix generators. Naturality is not assumed: both composites are evaluated on c tensor (u tensor n), and agree there. Consequently the square really compares C tensor_B (f tensor_A identity_N) with f tensor_A identity_(C tensor_B N), even though U and V have only A-module structures. No flatness or finite generation is used in this step.

Step 3 invokes exactly the injection-preserving clause of def-weil-pbc-flat-ring-map for N over A. The map f tensor_A identity_N is B-linear, so Step 1 applies over B; Step 2 gives a commuting square with invertible vertical maps. The text checks injectivity through that square explicitly. It concludes flatness over A by the same cited definition. It does not assert that A -> B is flat or that N is B-flat.

Step 4 applies the same injection criterion to N_C over A and uses the inverse square. Its only additional fact is Step 1, already proved directly from the faithful-flatness definition. Thus it proves injectivity before invoking flatness of N, with no circularity. Steps 3 and 4 cite the flat definition they use, and refer to earlier numbered arguments for the other facts, rather than adding artificial nodes for clauses of the item.

Against delivery-errors B--E: the statement introduces every ring and module, its existing definition nodes really define the notions, and the source tag/label were checked in tags/tags. The four steps are short arguments from the stated definitions and pure-tensor relations, so they are marked elementary; no exactness-preservation theorem is silently deduced from an injection-only definition. No non-elementary assertion is hidden by a word like 'transport': the interchange, inverse, square and injectivity argument are all given. All steps are under 2000 characters (594, 868, 623, 564). The graph gains edges only to existing definition leaves, so there is no self-dependency, duplicate helper or moved clause. I left all maintainer-owned fields intact.

I tested N=0, B=C (the identity extension), and A=B (which recovers the usual situation without changing the ring used to test flatness). The zero-ring case is included: B=0 forces N=0 and any unital B-algebra C=0, making both sides flat. To check that I had not smuggled in A-flatness of B, I used A=Z, B=Z/2Z, C=B[t], N=B: the extension B->C is faithfully flat, but multiplication by 2 on the test injection Z->Z is killed on both N and N_C, so both sides fail to be A-flat as required. If faithful flatness is removed, A=B=Z, C=Q, N=Z/2Z has C tensor_B N=0 flat but N nonflat; this confirms the reflection hypothesis is essential. No correction to the mathematical statement was needed.
