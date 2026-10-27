# Worker report: lem-sfb-field-geometric-fibre-covering-test

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-geometric-fibre-covering-test.json`: statement, split into eight proof steps; no full Mathlib match.
- `citations.json`: 22 verbatim statement quotations, one for each step/dependency occurrence.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log; `prepare.py` is an item-local preparation script, not a delivery file.

No new DAG nodes or Mathlib leaves were created. No Lean was written or compiled. The item is not the unit's key statement, so no unit realization was changed.

## Attachments

None. Searching `lean/WeilConjectures/` for the item tag gives no declaration. Searches for ind-etale algebras, geometric fibres, Galois sites and profinite constructions locate component results, not a declaration giving every clause. The related `AlgebraicGeometry.ProEtale.FieldGaloisSite.field_profinite_galois_site` in `lean/Sheaf/Paper/FieldProfiniteGaloisSite.lean:172` ends with `sorry`, and concerns the parent equivalence; it is not an attachment for this item. `Algebra.IndEtale.isSeparable_residueField_of_field` is likewise only a component assertion, already represented by existing residue-field nodes.

## WANTED

None. All source material needed here is available locally.

## What needed repair or clarification

The imported item had a statement and search records but no proof. Its statement is correct and is preserved exactly, together with all six statement dependencies and the inherited blueprint provenance. In particular, separably closed does not mean algebraically closed, and it would be wrong to use arbitrary algebraic residue extensions: the proof instead uses finite etale subalgebras, which split over the separably closed field.

The source's brief phrase reducing the covering criterion to the separably closed case requires both directions. The proof explicitly chooses a finite original subfamily before base changing it, and conversely lifts an arbitrary original point along the surjective separable-closure base change. It never extracts a finite subcover from an arbitrary union of closed images.

The inherited nearest blueprint ancestor is null, as `tools/blueprint_refs.py ancestor` confirms. The recorded `from.place` already specifies the separable-closure paragraph and parent old steps 6–7; this is retained. Whole-blueprint searches for `ind-etale`, `geometric fibre`, `finite split`, `affine fibre`, and `fpqc`, and whole-DAG searches for the concepts and relevant node names, found the finite-stage and generic inputs used here, not another statement of the whole item. The split stays below the prescribed field-site route and changes no unit or chapter.

## What remains unfinished

Nothing at the requested stage. Existing cited inputs remain separate DAG work items as appropriate; they are not silently assumed proved in Lean.

## Not duplicates

No new nodes exist, so there are no new/existing pairs to justify. In particular the split reuses `det-pe-condensed-point-basis` only for finite splitting and `lem-sfb-field-geometric-fibre-construction` for directed finite subalgebras and fibre topology. It does not recreate either result, the generic spectrum-limit theorem, the affine tensor-product fibre-product theorem, or the fpqc axioms.

## Mathlib search assessment

The original Q82 search records are retained. Six additional searches were run through the required Q75 search command and are recorded with their exact query text and returned result summaries. All four services answered. A second semantic phrasing was tried. Loogle found `Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum` and its kernel formula; I read `Mathlib/RingTheory/TotallySplit.lean`, including the finite-split hypothesis and the separably-closed instance. This result handles finite split algebras, not arbitrary ind-etale algebras or the topology and covering assertions. LeanSearch's etale-field classification and LeanFinder's purely inseparable spectrum homeomorphisms also do not state the item. The second grep found the finite-split source. Consequently the complete item is not a Mathlib leaf. There are no invented searches and no unavailable result recorded as absence.

## Review by Q75

I read Bhatt–Scholze, Definition 4.1.1 and Examples 4.1.4 and 4.1.10, pp. 27–28, in the local PDF. The last example supplies the field-site and finite-cover route; I expanded its finite-splitting and base-change arguments rather than using the field-site equivalence as a circular premise. I also read the current condensed-point-basis blueprint, Stacks `limits.tex` labels `lemma-inverse-limit-sets` and `lemma-inverse-limit-top` (0CUE/0CUF), `schemes.tex` label `lemma-fibre-product-affine-schemes` (01I4), `topologies.tex` definition `definition-fpqc-covering` (022B) and lemma `lemma-fpqc` (022D), and `morphisms.tex` label `lemma-base-change-surjective` (01S1). No SGA source is used.

For each proof step I opened every cited node and read its statement, not merely its proof or title. The quotation matrix records those actual statements.

1. `lem-weil-pbc-ind-etale-stability` supplies base change. `lem-sfb-field-geometric-fibre-construction` supplies a directed union of finite etale subalgebras over the field Omega, taken as its own separable closure. Clause 1 of `det-pe-condensed-point-basis` gives precisely finite powers of Omega. `lem-weil-pbc-spec-finite-product-fields` describes their primes. Given a prime of the union, the scalar map into its quotient is injective and surjective by these finite stages; its fraction field is therefore canonically Omega. No hypothesis of algebraic closedness, finite type of the whole algebra, or nonzero algebra is introduced.

2. The finite-product node gives discreteness and coordinate kernels; the idempotent calculation in the step proves the map classification. The construction node gives the Hom inverse limit. The spectrum-limit node applies to the small nonempty directed poset of finite subalgebras, with arbitrary transition maps allowed. Coordinate kernel equality proves compatibility, so the induced homeomorphism is the required kernel map.

3. The only additional input is the construction node's topology and directed finite subalgebras. The tensor formulas are balanced and inverse. For continuity in each direction I checked explicitly which finite generating list or finite list of tensor coefficients controls the restriction. This avoids identifying two potentially different finite-subalgebra topologies without proof.

4. The formulas compute naturality on every pure tensor; contraction of kernels is exactly the spectrum map of `def-weil-affine-spectrum`. The calculation really uses precomposition by an arbitrary algebra map, not just an inclusion. The action on the right is forgotten as requested.

5. The stability node explicitly says every map between two ind-etale base algebras is ind-etale and hence weakly etale. The ind-etale definition and the scheme weakly-etale definition identify the induced morphism as flat. All members of an arbitrary covering family satisfy flatness, including those outside the finite selection. This is not an inference from joint surjectivity alone.

6. The covering definition supplies the finite selection for the whole affine target. For the converse, the affine fibre-product node supplies affineness of every inverse image of an affine open. On review I added the existing open-immersion-base-change node to justify that this fibre product is an open subscheme of the source; citing only the definition of a fibre product would have omitted that fact. Its image is the ordinary inverse image of the given open, because its map is the pullback of the open inclusion. These finitely many opens give exactly the images in the definition. This is a few-line assembly of existing statements, not a new generic covering lemma.

7. Clause (3) of the fpqc-axioms node applies to the already finite covering family. The affine fibre-product node and the displayed mutually inverse tensor maps identify its actual sources with the base-changed algebras. The covering definition gives surjectivity; the previous naturality formula identifies the same maps on geometric fibres. No larger or varying set of indices is used.

8. The spectrum definition makes the map between field spectra surjective. Surjective-base-change and affine fibre products give surjectivity over the original target. Lifting a point through the finite geometric family then projects to an original source point. Step 6 finishes the covering test. I checked B=0 (all target algebras must then be zero), zero source algebras, empty families, B=k, finite products of fields, and the specialization k=Omega. Nonzero B has nonempty fibre by the construction node, so an empty family cannot accidentally cover it.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files. There are no statement-only children to hide clauses in, no new duplicate definitions, and no use of a cited proof beyond its statement. The generic off-unit inputs are declared with reasons in `split_report.tool_uses`; they retain the unit's route. A dependency traversal found no path from any proposed input back to this item. All eight steps are below 2000 characters and each contains one explicit argument; no long-step extraction is needed. The canonical residue field and topology clauses, all hypotheses, both implications of the covering criterion and the degenerate cases have been accounted for.
