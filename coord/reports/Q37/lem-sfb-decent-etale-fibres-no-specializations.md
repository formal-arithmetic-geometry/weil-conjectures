## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-decent-etale-fibres-no-specializations.json`: statement, split into five steps; not in Mathlib after the recorded searches. No new nodes and no new Mathlib leaves.
- `citations.json`: sixteen step/node records, quoting the cited statements verbatim.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, decent spaces, algebraic spaces and the specialization notion found no declaration proving this statement. Scheme specialization and stalk identities do not establish the algebraic-space assertion.

## Wanted

None. All sources used are in the read clone.

## Corrections and scope

The imported statement is correct and unchanged. Its empty proof is replaced by the actual argument behind Stacks Tag 03K5. The hypothesis is condition (4) of 03JV; step 2 supplies the finite-chart-fibre consequence rather than assuming quasi-separatedness or citing the converse criterion. The monomorphism part of the hypothesis is stronger than needed for that particular consequence and is retained. No chapter, unit, target or source file is changed.

The inherited blueprint record already has a detailed `from.place`; its `from.node` is null, exactly as `tools/blueprint_refs.py ancestor` reports for this inherited chain. The full imported-blueprint searches for `specializations` and `decent` returned zero matches, and a search of the current `literature/blueprint/latest/blueprint/` found no duplicate. `same_as` remains empty. I read the current unit and its direct-image proof as well as the stored chapter/unit records. This is a supporting point-topology lemma below the inherited closed-point field-immersion input, not a replacement for a direct-image step. The generic scheme/topology tools from other units are declared only in `split_report.tool_uses`.

## Unfinished work

None in this one-level split. No new unsplit lemmas are needed. Independent mathematical review remains with the maintainer.

## Not duplicates

No new nodes. In particular the existing finite-groupoid orbit-incomparability lemma requires finite projections, whereas the projections here are only etale. The existing quasi-separated-space etale-specialization lemma requires a quasi-compact diagonal, which is not a hypothesis of this item. Neither is used to smuggle in an extra assumption. The finite-chart decency criterion proves a converse direction and is not used as the finite-fibre input.

## Review by Q37

I read `decent-spaces.tex` at Tag 03K5 (`lemma-decent-no-specializations-map-to-same-point`), the full proof of Tag 03IM (`lemma-no-specializations-map-to-same-point`), and the conditions and proof of Tag 03JV (`lemma-UR-finite-above-x`). The intermediate bounded-fibres lemma 03JX merely packages the implication needed here; I expanded the applicable (4) to (3) argument directly. I also read `spaces-properties.tex` Tag 03H4 (`lemma-points-cartesian`), `morphisms.tex` Tag 02GL (`lemma-etale-over-field`) and Tag 03HV (`lemma-generalizations-lift-flat`). There are no new nodes whose sources need review.

For step 1 I opened the statements of `lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-etale-composition-cancellation`, `def-trf-algebraic-space` and `lem-trf-space-fibre-products-etale-covers`. They supply an affine neighbourhood, open restriction of an etale morphism, the representable scheme tests, and the categorical sheaf fibre product. The claim that the general point remains in the neighbourhood is the elementary definition of specialization. No affine intersection is asserted. Scheme representability of the self-relation and etaleness of its projections follow directly by testing the representable etale chart against itself; no covering or surjectivity assumption on the chart is used.

For step 2 I checked the actual discrete-fibre statement `lem-weil-pbc-etale-fibre-discrete-separable-points`, the fibre construction and subspace comparison of `def-pc-scheme-fibre`, the scheme-test definition of `def-trf-algebraic-space`, and the image equality in `lem-a1-space-point-open-calculus`. The selected field map is quasi-compact on the affine test W, so its pullback P is quasi-compact. P is etale over the field and therefore discrete. Its singleton cover has a finite subcover, and its image is exactly the point fibre A. Finiteness here is topological finiteness, not an unproved claim that a morphism is finite. The fibre over the unique point of Spec F is P since the canonical residue-field map is an isomorphism. This works over arbitrary S, not just over Spec Z.

For step 3 the definition `def-weil-etale-morphism` explicitly includes flatness, and `lem-weil-pbc-flat-generalizations-lift` explicitly gives the required lifted specialization. I wrote the arrow orientation to remove any ambiguity in the words “specializing to”. The discrete-fibre theorem together with the fibre-subspace homeomorphism really excludes comparable distinct points of an s- or t-fibre. I checked `lem-sc-scheme-sober` for uniqueness of the generic point, which yields antisymmetry on W without Noetherianity.

For step 4 the surjection onto the point fibre product in `lem-a1-space-point-open-calculus` gives the first relation point even though the chart is not surjective. The subsequent lifts use the flat-lifting statement and the flatness clause of the etale definition. Continuity of the scheme projection gives the next specialization; equality as=at keeps every point in A. The induction specifies both coordinates of each relation point, its specialization and its common image. Only |A|+1 choices are needed, so this is a finite induction, not an unstated infinite-chain theorem.

Step 5 uses only the established discrete-fibre consequence, antisymmetry and the pigeonhole principle. I checked the backward indices: an equality v_(n+2)=v_(n+1) forces equality of r_(n+1), r_n by s, then equality v_(n+1)=v_n by t. A repeated nonadjacent point in a specialization chain forces an adjacent equality by antisymmetry. This proves the original equality rather than moving it into a new lemma.

Against B1–B10 there are no new nodes, no hollow definitions or missing Mathlib leaf metadata; the original self-contained statement and notion dependencies are retained. All five fresh Mathlib searches were run with msearch and read: the two semantic phrasings returned scheme/stalk facts, LeanSearch returned scheme etale/valuative facts, Loogle and the local algebraic-geometry grep had no hits. Their exact queries and log summaries are appended without changing the inherited searches. Against C1–C8 every non-elementary input has a node, every cited node's statement was opened, and every use has a verbatim quote in citations.json; the off-unit generic tools are explained in split_report. Against D1–D5 the item itself carries the finite-fibre and specialization argument, with explicit induction base, step and collapse. Against E1–E7 I checked all hypotheses and fibre products, and found no source or statement error.

The small cases also check out: an empty chart admits no u and is vacuous; once u is chosen the finite fibre is nonempty; a one-point fibre gives equality immediately; a disconnected or infinite chart is reduced only to one affine neighbourhood; no global finiteness, quasi-separatedness or Noetherianity enters. A nontrivial scheme specialization cannot lie in a discrete etale scheme fibre. Every proof step is under 1000 characters, so none triggers the long-step hidden-lemma issue. All writes are confined to this sandbox, and no Lean compiler or build tool was run.
