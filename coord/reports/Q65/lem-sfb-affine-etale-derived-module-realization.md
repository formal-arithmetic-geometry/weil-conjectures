# Q65: affine small-etale derived module realization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-etale-derived-module-realization.json`: statement, split, no Mathlib match. The mathematical statement is unchanged. Five proof steps now give the associated-sheaf identification, section normalization and faithfulness, exactness, natural cohomology, composite unbounded equivalence and K-injective computation.
- `citations.json`: one verbatim statement quotation for every citation in each numbered proof step.
- `searches.jsonl`: actual msearch results; the item's inherited Q47 searches remain intact in its JSON, and Q65's additional searches are appended there.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches for the exact blueprint tag and for affine/etale derived realization in `lean/WeilConjectures/` found no declaration giving this whole item. `AlgebraicGeometry.exists_affineQCohDerivedEquivalence` in `WeilConjectures/AlgebraicGeometry/AffineQCohDerivedEquivalence.lean` gives the Zariski part, not the etale conclusion. It is represented by the existing node `lem-pc-affine-qcoh-derived-equivalence`, which is cited. Ordinary constant-ring etale module equivalences concern a different coefficient sheaf and do not attach this item.

## WANTED

None. Every source used is present under `literature/stacks-project/`.

## What needed repair

The unsplit item's source correctly named the composition of Tags 071Q and 06Z0, but gave no argument. Both equivalences already exist as DAG statements, so no child repeating either the item or these facts is created. We reuse `lem-sfb-scheme-derived-etale-qcoh-comparison`, whose statement explicitly includes derived global sections comparison, instead of creating another 071Q node. The broader `lem-sfb-derived-etale-zariski-equivalence` also exists, but its extra pullback coherence is unnecessary here.

The inherited blueprint ancestry has `from.node: null`; `tools/blueprint_refs.py ancestor` returns None for both this item and `lem-sfb-admissible-direct-image`. Its detailed original place and via list are retained. This is not repaired by inventing an imported blueprint ancestor. The newest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, proof (3), uses compactification, proper image and open image; this affine module realization remains a generic tool below the supplied internal-Hom/coherent-Ext prerequisite chain, not a replacement of that unit route. Chapter and unit files were read and remain untouched.

The item itself is true; no statement dispute or changed hypotheses. There is no Noetherian, finite-presentation, nonzero-ring, boundedness or finite-Tor hypothesis. None is inserted in the proof. The use of the word bounded in the source label `lemma-affine-compare-bounded` does not restrict its statement: Tag 06Z0 explicitly states all three unbounded derived equivalences.

## Not duplicates

No new nodes were created. Searches across DAG statement/source fields and blueprint_refs searches for 071Q, 06Z0, etale/Zariski, derived/affine, quasi-coherent and tilde located the existing affine and site-comparison statements. In particular the ordinary quasi-coherent equivalence, affine finite-limit preservation, affine unit/adjunction, affine pullback section formula, exact-functor factorization and unbounded K-injective tools were all reused.

## Review by Q65

I read `spaces-perfect.tex` Tag 08H8 (`lemma-epsilon-flat`), the full statement and proof of 071Q (`lemma-derived-quasi-coherent-small-etale-site`), and 08GH (`remark-match-total-direct-images`); `perfect.tex` Tag 06Z0 (`lemma-affine-compare-bounded`), statement and its unit/counit proof; `schemes.tex` Tags 01HV (`lemma-spec-sheaves`) and 01I9 (`lemma-widetilde-pullback`); and `sites-cohomology.tex` Section 07A5, including the existence and module-valued global-sections examples. These sources agree with the item's coefficient category of structure-sheaf modules. In particular the arbitrary-cohomological-degree argument belongs to the unbounded comparison theorem already in the DAG; the proof does not apply a bounded-below spectral sequence to an unbounded object. There are no new-node statements requiring source review.

For step 1 I opened the statements of `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`, `lem-weil-pbc-module-pullback-affine-sections` and `lem-weil-pbc-affine-tilde-gamma-adjunction`. The first explicitly identifies epsilon tensor pullback with the tensor-sections associated sheaf and normalizes sections on opens. The second explicitly supplies the natural affine section map, not just existence of a pullback. The third supplies the natural unit M to sections of tilde M. Together these give exactly the stated B tensor M values, transition maps, coefficient morphisms and final-object section isomorphism. Applying that last natural isomorphism to two maps proves faithfulness without any unproved conservative-functor claim.

For step 2 I opened `lem-sc-tilde-preserves-finite-limits`, the affine adjunction statement again, and `lem-sfb-scheme-derived-etale-qcoh-comparison`. Their statements respectively supply all finite limits for tilde, all small colimits for tilde, and exact epsilon pullback. This proves exactness into the ambient module-sheaf category. The proof does not infer ambient exactness merely from an equivalence of full quasi-coherent categories; that would need additional justification.

For step 3 the non-elementary localization and termwise computation are exactly `lem-weil-pbc-exact-functor-derived-factorization`, whose full statement I read. `def-weil-abstract-derived-category` explicitly gives cohomology as kernel modulo image and its factorization through localization. The short kernel/image/quotient argument proves the cohomology comparison, and the roof description explains naturality on derived morphisms. This is a routine argument from exactness and these two statements, not a hidden affine or etale lemma.

For step 4 I read both cited equivalence statements in full. `lem-pc-affine-qcoh-derived-equivalence` concerns arbitrary rings and unbounded module complexes, and specifies derived Zariski sections as inverse. `lem-sfb-scheme-derived-etale-qcoh-comparison` concerns every scheme, not only a proper or finite-type scheme, and its final sentence explicitly identifies derived global sections on both sites. Its qcqs condition belongs to the preceding direct-image comparison clause; we do not apply that clause to an unqualified morphism. The displayed composition of inverse functors explains why the inverse here is actual etale derived global sections. Composing the existing equivalences is elementary category theory; no new node merely restating the affine etale conclusion is introduced.

For step 5 I read `prop-pur-kinjective-resolutions-exist`, which applies to module sheaves on any small ringed site and supplies resolutions for arbitrary complexes, and `lem-weil-pbc-kinjective-total-derived`, which supplies the universal total right derived functor and its computation at K-injectives. The small etale site is taken in its ordinary chosen universe. The cone/shift argument verifies the exactness hypothesis on the functor between homotopy categories using only finite direct sums. Its target is D(A), retaining the structure-ring action; no constant coefficient sheaf is substituted. Uniqueness from the stated derived universal property identifies this computation with the sections functor of step 4.

I checked B through E of delivery-errors against these steps. Every citation is backed by its actual statement in `citations.json`; no citation relies on an argument hidden in a dependency's proof. The source tags are locators for steps, not substitutes for DAG citations. Every genuinely non-elementary input is an existing cited node. No step exceeds 2000 characters. The statement is self-contained as imported, with all its notion references retained, and no clauses are transferred into a new node. The zero ring yields the empty affine scheme and only zero modules, so sections, faithfulness and the zero derived equivalence still hold. The zero module, arbitrary infinite modules, shifted single modules and complexes unbounded in both directions all fit the cited hypotheses. Nothing uses finite generation or invertibility of a scalar. All off-unit generic tools are declared in `split_report.tool_uses`.

Mathlib searches were run only via the required msearch.py command and their hits read. General derived localizations and affine Zariski site sheaf equivalences do not compare unbounded quasi-coherent complexes on the small etale site. The second semantic phrasing returned affine-limit and ordinary sheaf-presentation infrastructure, again no match. The exactness-oriented extra search returned general exact functor and module localization results; those were not claimed to prove the item. No fabricated query or unavailable-service absence claim is recorded.

## Unfinished work

No mathematical part of the one-level split is unfinished. Existing dependencies remain assigned to their own nodes. Required server dry run and direct push follow this self-review.
