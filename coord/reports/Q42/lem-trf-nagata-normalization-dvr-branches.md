# Q42 stage-1 delivery: lem-trf-nagata-normalization-dvr-branches

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nagata-normalization-dvr-branches.json`: item, statement, status split. Seven proof steps; no new nodes and no new Mathlib leaves. The statement, statement dependencies, source, created record and blueprint ancestry are retained.
- `citations.json`: 17 entries, one for every use in the seven proof steps. Each quote is copied verbatim from the cited node's statement.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `write_split.py` is sandbox-only preparation code.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact item id, Nagata/normalization terminology, total quotient terminology, and integral-closure products. The project theorem `integralClosure_finite_pi` covers product-base integral closure, not this item's reduced Nagata normalization, finiteness and DVR conclusions. The other project normalization declarations likewise do not give every clause. No project declaration is proposed as an attachment. Existing Mathlib leaves are cited through their existing DAG nodes.

## WANTED

None. The needed Stacks source is available locally in `literature/stacks-project/algebra.tex`, `varieties.tex`, and `tags/tags`.

## Corrections and scope

The item had no proof. Its statement is correct and unchanged. In particular dimension is exactly one, not at most one; no minimal component is a zero-dimensional field component of a one-dimensional local ring. No completion, excellence or separability assertion is added. The surrounding blueprint route remains unchanged: this is the component-normalization/DVR input below the semistable-curve branch of `lem-trf-local-term-locality`, not a new route through SGA.

I use two generic off-unit tools, declared in `split_report.tool_uses`: `lem-weil-pbc-reduced-noetherian-total-ring-fractions` for the actual canonical total-fraction product map, and `lem-weil-pbc-integral-injective-dimension-equal` for dimension preservation. Neither is supplied by a statement of this unit. All other off-unit statement inputs are existing Mathlib leaves; the remaining inputs are definitions.

## Unfinished work

None in this stage-1 split. The existing unsplit dimension-preservation node remains a separate queue item: this delivery cites its statement and does not claim to prove that dependency.

## Not duplicates

No new nodes. All required non-elementary statements were already in the DAG. The component-product proof, the finite supported generating family, and the prime/localization idempotent argument are elementary written steps, not new nodes. Searches of the full DAG and `tools/blueprint_refs.py search` for normalization, integral closure, and Dedekind found no blueprint statement equivalent to this whole item. `blueprint.same_as` remains empty. The ancestor command gives `lem-trf-local-term-locality`, as retained in the item.

## Review by Q42

I read the item against Stacks Tags 0C3S (`lemma-pre-delta-invariant`) and 0C3V (`lemma-normalization-same-after-completion`) in `varieties.tex`, especially the first proof's finite-normalization argument and the second proof's local normal dimension-one input. I also read the underlying Algebra results in `algebra.tex`: 032R (`definition-nagata`), 032F (`definition-N`), 00FN (`lemma-Noetherian-permanence`), 00FR (`lemma-Noetherian-irreducible-components`), 00EU (`lemma-minimal-prime-reduced-ring`), 00EW (`lemma-reduced-ring-sub-product-fields`), 02LX (`lemma-total-ring-fractions-no-embedded-points`), 034L (`lemma-integral-closure-in-normal`), 00OK (`lemma-integral-sub-dim-equal`), 034X (`lemma-characterize-Dedekind`), and 00PD (`lemma-characterize-dvr`). I verified their tag/label pairs using `tags/tags`. There are no new-node sources to audit.

For step 1, I opened the statements of `def-weil-pbc-nagata-ring`, `lem-weil-pbc-noetherian-finitely-many-minimal-primes`, `lem-weil-pbc-surjective-image-noetherian`, and `def-weil-pbc-krull-dimension-ring`. The first gives precisely Noetherianity and N-2 for every prime quotient, the second gives the required finite enumeration, and the third applies to the surjection to each quotient. I wrote the quotient ideal correspondence, locality, strict chain and N-2-for-all-prime-quotients checks in the step itself. This proves the whole claimed component type, without citing an unrelated definition for a permanence theorem.

For step 2, I opened `lem-weil-pbc-reduced-noetherian-total-ring-fractions`, whose statement gives both the canonical product map and that each minimal localization is a field with zero extended prime. Its reduced and Noetherian hypotheses are present. The fraction description in `def-weil-pbc-localization-at-prime` then gives the kernel and fraction-field identification explicitly. I did not infer a kernel statement from the proof of some other node.

For step 3, I checked `def-weil-pbc-japanese-domain`: the trivial extension is explicitly allowed and gives the finite module assertion. The statements of `lem-weil-pbc-finite-algebra-noetherian`, `lem-weil-pbc-integral-closure-finite-extension-normal`, and `lem-weil-pbc-integral-injective-dimension-equal` give exactly Noetherianity, normal domain/fraction field, and equality of dimensions. Their hypotheses are respectively the finite module already obtained, a domain with fraction field and finite extension (the identity extension), and an injective integral map. All hold. `def-weil-pbc-integral-closure` supplies the monic-equation meaning, and the injection is the actual inclusion in the field. The integral-closure normality leaf does not require a Dedekind base.

For step 4, I checked the integral-closure definition again. Projection takes a monic equation to the quotient base, and in the reverse direction each lifted monic polynomial has the intended vanishing coordinate. Their product is monic and vanishes in every coordinate. This is a direct finite polynomial computation, so no new product-closure lemma is hidden in the step. In particular I do not mistake integrality over a product base for integrality over the diagonal image of A.

For step 5, I checked `def-weil-finitely-generated-module`; it asks for an actual finite spanning set. The step specifies one, the supported component generators, and lifts each coefficient along the surjection A to D_i. This proves A-module finiteness rather than merely claiming that a product of finite modules is finite.

For step 6, I checked the localization definition and wrote the prime classification and both maps. Orthogonal idempotents with sum 1 select exactly one factor. The projection kernel lies in the prime, so its projected ideal really is prime. The equality of the inverse-image ideal verifies exactly which denominators are allowed. After localization the selected idempotent is 1 and every other coordinate vanishes; this proves the fraction maps are inverse and pins down the canonical A-compatible isomorphism. The contraction to the stated component maximal ideal is checked through the actual structural map.

For step 7, I opened `lem-weil-pbc-integral-prime-over-maximal-maximal` and `lem-sc-dedekind-localization-dvr`. The first gives maximality from integral extension and maximal contraction; the second applies to an already proved Dedekind domain of dimension exactly one. I checked separately that the prime is nonzero: the nonzero maximal ideal of the component domain injects into it. This also verifies the nonzero-prime hypothesis of Mathlib's DVR theorem, avoiding its field exception.

I checked small cases: a DVR gives one factor and the identity normalization; an irreducible singular local curve gives one finite normal overring that may have several maximal ideals; an ordinary reducible node gives distinct domain factors and one selected factor at each prime of the normalization. Zero rings and fields are excluded by dimension one. A maximal ideal cannot be a minimal prime in the local dimension-one situation, which is why no zero-dimensional component case was silently discarded. The product and localization constructions also work when there is only one factor. There is no assumption that the normalization of an irreducible local curve is itself local.

For the delivery-errors B--E audit: there are no new nodes, no opaque definitions, no changed hypotheses or conclusions, and no proof sketch masquerading as a statement. Every non-elementary inference is named in a use-list and has a verbatim statement quote in `citations.json`; the three elementary steps contain their polynomial, generator and idempotent/fraction arguments. I checked that no dependency descends from this item, and the server DAG check is required before delivery. All steps are below 2000 characters (largest 1241), so there are no long steps needing further lemma extraction. Searches were made only with the required msearch command, and the original imported searches are retained separately from the newly logged exact queries.

The Mathlib searches used LeanFinder twice with different formulations, Loogle, LeanSearch, and two grep queries. I read their hits. The searched Dedekind integral-closure result at `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:234` assumes a base already Dedekind, unlike D_i, and the DVR-localization result assumes the Dedekind conclusion we first have to establish. The second phrasing finds Kummer-Dedekind and normal-closure results with additional hypotheses and no full reduced-Nagata product theorem. The grep Nagata result is only a historical attribution in Noether normalization. Thus the whole item is not a Mathlib leaf, although several existing input nodes are.
