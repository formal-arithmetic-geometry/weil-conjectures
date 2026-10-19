# Q110 stage-1 report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-quasi-affine-fpqc-effective-descent.json`: statement; ten-step split; no Mathlib match for effectivity.
- `dag/nodes/sec-trace-formula/lem-trf-quasi-affine-base-change.json`: statement-only support lemma, unsplit; no Mathlib match under precisely these hypotheses.
- `dag/nodes/sec-trace-formula/lem-trf-quasi-affine-canonical-affine-embedding.json`: Mathlib leaf for the canonical open immersion, compactness and separatedness of a quasi-affine scheme.
- `citations.json`: 44 verbatim statement quotations, one per step/node citation.
- Search records and working scripts are in the sandbox. Two new nodes, one Mathlib leaf.

Attachments: none for the item. Read-only project-source searches for its blueprint tag and quasi-affine/effective descent found no sorry-free project declaration stating the item. The new Mathlib leaf records its canonical-map instances separately.

WANTED: none.

The imported item had no proof. Its statement agrees with Stacks Tag 0247 specialized to singleton covers, including the absence of local finite-presentation hypotheses, and is retained verbatim. Its singleton-fpqc definition does not force the original map to be quasi-compact; the proof uses the existing Tag 02W3 reduction instead of silently imposing that assumption. The first sandbox draft moved the affine-case argument into a new node. I removed that proposed node and wrote the actual affine-envelope and invariant-open argument into the item. I also repaired the finite-coproduct argument: the intersection with an affine target open is affine because the component is clopen, rather than because intersections of affine opens would automatically be affine.

Unfinished: no part of the assigned split. The new base-change support lemma is intentionally statement-only for a one-level split.

## Not duplicates

lem-trf-quasi-affine-base-change vs lem-trf-quasi-affine-fpqc-effective-descent: arbitrary base-change stability of a morphism property is different from effectivity of a descent datum, and is not an affine case or conclusion clause of the item.

lem-trf-quasi-affine-canonical-affine-embedding vs lem-trf-quasi-affine-fpqc-effective-descent: the new node identifies a canonical affine envelope with no cover or datum; the descent argument remains in Steps 4–10.

lem-trf-quasi-affine-canonical-affine-embedding vs lem-weil-pbc-morphism-into-affine-scheme: the latter gives the Hom/global-sections bijection and principal-open preimages, not the open-immersion assertion.

lem-trf-quasi-affine-canonical-affine-embedding vs lem-coef-infinity-comma-mapping-pullback: the common string 01P9 denotes Kerodon's mapping-space tag in the existing node and Stacks Properties Tag 01P9 here; their statements concern different subjects.

lem-trf-quasi-affine-canonical-affine-embedding vs lem-coef-infinity-mapping-excision: the existing node concerns mapping spaces and cites Kerodon 01P9, whereas the new one concerns schemes and Stacks 01P9.

## Review by Q110

I read the item, its parent, chapter `sec-trace-formula`, unit `sk-i-curve-zero`, and ancestor `lem-trf-local-term-locality` to locate this ingredient of the geometric quotient-presentation route. I read the complete proof of Stacks `descent.tex` Tag 0247 (lemma-quasi-affine) and the generic reduction Tag 02W3. The split follows that route. Over the reduced affine base it uses ordinary spectra and the existing global-sections flat-base-change lemma instead of relative spectra and sheaf-level base change; the tensor formula explicitly verifies the induced cocycle.

For the new base-change node I read `morphisms.tex` Tag 01SO, including its proof. It states arbitrary base-change stability with no finite-presentation hypothesis. For the new canonical-embedding node I read `properties.tex` Tag 01P9 and its proof, which gives the canonical quasi-compact open immersion and explains separatedness. I read Mathlib `AlgebraicGeometry/QuasiAffine.lean:30–57`: the class extends compactness (34), separatedness is an instance (41), and the canonical map is an open immersion (46). From a quasi-compact open embedding into an affine scheme, `Scheme.IsQuasiAffine.of_isImmersion` (54) gives Mathlib's class in one line. The leaf therefore uses the same notion of quasi-affine as the item.

I searched the entire DAG for the tags, canonical quasi-affine maps, base change and the candidate declarations, and used `tools/blueprint_refs.py search` for quasi-affine, 01P9 and 01SO. None of the 13 quasi-affine blueprint hits states either new lemma. The two tag-only apparent duplicates are Kerodon nodes explained above. Both new nodes carry the full ancestor chain with this item prepended, and `same_as` is empty after these searches.

I opened every cited node and checked the statement, not just its title. Here is the substantive use-by-use review.

1. The quasi-affine definition gives isomorphism invariance, and the new base-change lemma gives exactly the arbitrary base-change condition (1) of Tag 02W3. No descent fact is inferred from a definition.

2. The coproduct-family statement supplies clopen components. The clopen/idempotent and principal-localization statements show that intersection with an affine target open is affine. Quasi-affineness supplies componentwise quasi-compact opens in affines, and affine-morphism permanence clause (4) makes their finite disjoint union affine. Finite-union compactness and the empty case are written out. This verifies condition (2), including zero components.

3. The affine-qcqs and qcqs-permanence statements make the reduced flat-surjective map quasi-compact. The fpqc definition is then checked by finite affine covers of preimages of affine opens. As A is affine, the source V is quasi-affine by its definition. The new embedding leaf makes V qcqs and gives j. The Hom/global-sections bijection shows that j is over A, and the separate existing morphism-affine-schemes-affine statement gives affineness of W to A.

4. Flat base change gives flatness of the double-overlap projections, and the affine fibre-product statement gives affine sources and the tensor-product spectrum. The global-sections base-change lemma requires affine S and S-prime and qcqs X; all three are checked. Its exact tensor formula and the Hom/global-sections bijection identify the pulled-back j with the canonical map.

5. Contravariant functoriality of the affine-spectrum node turns the ring isomorphism induced by phi into psi. The Hom/global-sections bijection proves the equality with j by equality of the induced ring maps. This uses an actual Hom bijection, not an unrelated full-faithfulness statement.

6. On triple overlaps, each forgetting map is a base change of p, or a composite of two such maps. Permanence gives qcqs of the pullbacks of V: V to affine A is qcqs, this survives base change, and A2 is qcqs. Thus global-sections base change applies again. Equality on tensor generators checks compatibility with phi and with successive base change; functoriality of Spec then gives the cocycle demanded by the descent-datum definition. This is the routine functoriality verification in the main proof of Tag 0247; no independent comparison theorem is assumed.

7. The affine-effectivity statement returns exactly the required compatible isomorphism, under the affine and singleton-fpqc hypotheses already checked. Its conclusion does not assert W-prime is affine; the proof does not need that assertion. The flat, surjective and quasi-compact base-change statements give all three properties of q. Both off-unit non-Mathlib descent tools are declared in `split_report.tool_uses`, as Tag 0247 explicitly uses this route.

8. The fibre-product universal property identifies the two projections after compatible affine descent. Base change of open immersions and the definition of open immersion give the inverse-image open subschemes. Since phi is an isomorphism and psi extends it, the two inverse images of O coincide.

9. Scheme fibre products are not merely set-theoretic fibre products. The points-of-fibre-product statement parametrizes a lift of two points over the same point by a prime of the tensor product of their residue fields. Nonemptiness of that spectrum follows from surjective base change of a map of one-point field spectra, using the affine fibre-product formula. This supplies a lift, proves saturation of O, and gives q-inverse(U)=O. The quotient-map statement requires precisely the flatness, quasi-compactness and surjectivity established for q, and makes U open.

10. Base change of the open U is its inverse-image open O by the fibre-product universal property and open-immersion base change. The open-immersion definition identifies V with that scheme, not just that topological space. Step 5 ensures restriction of the canonical descended datum is the specified phi. Finally, Tag 02W3 has exactly the three conditions established above and returns effectivity for the original arbitrary singleton fpqc cover.

I tested the statements on an empty source, empty base, identity cover, and zero or one coproduct components. No nonemptiness or local finite-presentation assumptions were added. The canonical affine spectrum is Spec(0) for empty V, so the construction works there too. Every step is under 2000 characters; I additionally checked the triple-overlap and saturation arguments for hidden inputs. The 44 citation quotes are generated directly from the cited JSON statement strings and are verbatim.

The Mathlib records contain actual search-command output, including two natural-language phrasings per new node. The initial dry run rejected my earlier use of a new node id as the log argument; I reran all new-node searches under the assigned item id and retained the correctly logged results. An incomplete single-file grep is recorded as such and followed by a directory-scoped grep giving the actual file and line 46. Relative base-change searches found only absolute quasi-affine or affine-morphism results in Mathlib. The project's `AlgebraicGeometry.IsQuasiAffineHom.of_isPullback`, `WeilConjectures/Mathlib/AlgebraicGeometry/QuasiAffine.lean:230`, additionally requires separate `QuasiCompact p` and `QuasiSeparated p` instances. It is a partial candidate rather than an exact attachment under the stipulated hypotheses; discharging those extra relative conditions is not a one-line specialization. No SGA source is used. No Lean was written and no compiler or build was run.

The first preflight of the revised split required a structured `mathlib_match.line` field in addition to the lines already in `how`; I supplied line 46, checked above in the pinned source.
