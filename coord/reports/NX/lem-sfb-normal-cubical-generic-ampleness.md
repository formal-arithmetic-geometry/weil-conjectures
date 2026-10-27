# Stage-1 report: lem-sfb-normal-cubical-generic-ampleness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-cubical-generic-ampleness.json`: split item, eight proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-raynaud-generic-ample-power-model.json`: new statement-only auxiliary existence node; Mathlib searches found no match.
- `citations.json`: verbatim statement quotations for every cited node in every step.

## Attachments

No finished Lean declaration was found. The fixed-model isomorphism spreading step attaches to existing `lem-trf-fp-module-limit-isomorphism-descent`; relative ampleness restriction and affine-cover locality attach to existing Stacks-derived nodes named in `tool_uses`.

## WANTED

- WANTED: Raynaud, *Faisceaux amples sur les schémas en groupes*, LNM 119 (1970), XI 1.13 and XI 1.16, for `lem-sfb-raynaud-generic-ample-power-model` and the connected-fibre ampleness input. The original is not present in `literature/`; the node is agent-formulated from the cited secondary accounts.
- WANTED: Moret-Bailly, *Pinceaux de variétés abéliennes*, Astérisque 129 (1985), I 2.6 and VI 3.0--3.1, for the relative cube and the supplied-line conclusion. The original is absent locally; the assembly is marked agent-written.

## What was wrong or missing

The imported item was unsplit and its inherited blueprint provenance points through a long stable-Picard chain whose latest blueprint text has no literal cubical node. The key proof input is an ordinary relatively ample model of a positive generic power; it must be separated as its own statement-only node so that the item does not cite its parent `lem-sfb-symmetric-ample-power-extension` circularly. The existing symmetric extension node applies only over a dense open, so a generic isomorphism must first be spread using the existing finite-presentation limit lemma. No statement was changed.

The Mathlib searches for the new node and the item returned only generic affine-localization, limit, Picard, or unrelated `Ample` declarations. A second natural-language formulation was run for the new node. The grep hit mentioning Raynaud was flat descent, not this theorem. Therefore the new node remains unsplit rather than a Mathlib leaf.

## Not duplicates

lem-sfb-raynaud-generic-ample-power-model vs lem-sfb-normal-cubical-generic-ampleness: the new node constructs an auxiliary ordinary ample model from generic data; the item proves ampleness of a fixed supplied cubical line, requiring a comparison argument.

lem-sfb-raynaud-generic-ample-power-model vs lem-sfb-symmetric-ample-power-extension: the existing parent starts with a rigidified line over a dense abelian OPEN and concludes an extension there, whereas the auxiliary node starts with only a generic line and promises only a generic ordinary isomorphism; it does not give the required dense-open compatibility or cubical comparison. The parent depends on this item and is not used in the proof.

lem-sfb-raynaud-generic-ample-power-model vs lem-sfb-symmetric-line-power-prolongation: that node extends a power over a specified dense open but assumes no positivity and concludes no ampleness. It cannot supply the auxiliary relatively ample model.

lem-sfb-raynaud-generic-ample-power-model vs lem-sfb-normal-symmetric-cubical-extension: that node gives cubical extension and full faithfulness, with no positivity conclusion. The item uses its dense-open full-faithfulness clause after spreading, not as the new existence input.

## What could not be finished

The Raynaud original and the Moret-Bailly proof pages are WANTED, so source-level verification of their exact hypotheses remains for a later stage. Lan's public revised thesis was used only as corroboration; its Chapter 4 has a complete Noetherian adic-base scope and is not silently substituted for the locally Noetherian normal statement here.

## Review by NX

I read the item and every statement quoted in `citations.json`. Step 1 checks the affine normal restriction, all semiabelian and proper-generic hypotheses, and invokes only the new ordinary-line existence node; it deliberately does not invoke the parent supplied-line theorem. Step 2 reads the invertible-module definition, the base-change ampleness statement, and the tensor-pullback/rigidification definitions; it verifies local freeness, normalizes the generic scalar, and records why ampleness is unaffected. Step 3 reads the relative cube statement and the cubical-line definition. I checked the connectedness argument fibre by fibre: a clopen decomposition is constant on the connected torus cosets and descends through the fppf quotient to the connected abelian quotient. The tensor product of the cube equations gives the cube on the positive power. Step 4 reads the finite-presentation limit statement and explicitly constructs the directed localization system, its affine transitions, its scheme limit and the inverse isomorphism data; finite presentation of lines and quasi-compact/separated hypotheses are supplied by the item. Step 5 checks the rigidification scalar in the domain localization and then uses exactly the restriction and rigidification-preserving-isomorphism clauses of the cube node. Step 6 reads the normal symmetric extension statement: it is used only for full faithfulness over the dense open, and its normal, integral, locally Noetherian, semiabelian hypotheses are verified after restriction. Step 7 reads the ample definition and checks the section on a positive tensor power is the same section of a further positive power, so the nonvanishing affine condition is unchanged; this is elementary and no new node was created. Step 8 reads the affine-cover locality statement and checks quasi-compactness from finite presentation before obtaining the required conclusion for every affine open of the original base.

I compared the auxiliary node with the parent power-extension theorem, the normal symmetric extension theorem, the sibling power-prolongation theorem, and the supplied-object item. The auxiliary node has no supplied cubical line and concludes only existence of an ordinary relatively ample model, so none is a restatement or a clause of the item. I tested the zero-torus (abelian) case, the torus-rank-positive semiabelian case, a DVR base, and the case `d=1`; all localization, tensor-power, and rigidification arguments still apply. No SGA 4 or SGA 4-half source is used.

## Sources and search record

I read Stacks `limits.tex`, lemma-descend-modules-finite-presentation (Tag 01ZR), parts (2),(3), and `morphisms.tex`, lemma-characterize-relatively-ample (Tag 01VJ), including the affine-cover implication. These are exactly the sources of the reused limit and locality statements; the base-change tool cites Tag 0893. The new geometric existence node has no Stacks tag; its Raynaud source is WANTED, rather than an invented Stacks citation.

I consulted the primary online accounts at [Lan revised thesis](https://www.kwlan.org/articles/cpt-PEL-type-thesis-revision-dense.pdf), Proposition 3.2.3.1, Proposition 3.3.2.2(1), Theorem 3.3.2.3(2), and Lemma 4.2.1.6; and the indexed relevant pages of [Moret-Bailly's thesis](https://www.numdam.org/item/BJHTUP11_1984__0154__P0_0.pdf), VI 3.0--3.1, printed pp.136--137, and [Astérisque 129](https://numdam.org/item/AST_1985__129__1_0.pdf), II 3.3.3, printed p.53. Full Numdam files exceeded the browser retrieval size limit; these were indexed page excerpts, not a claim to have read the full originals. The accounts separate an ample-extension input from cube uniqueness; the new precise generic-power statement records agent responsibility for its formulation. No original was downloaded and no original-source proof is claimed.

Whole-DAG and latest-blueprint searches were made for cubical, symmetric, Raynaud, generic fibre, ample extension, the proposed id and the relevant source places; `blueprint_refs.py search ampleness` found only unrelated curve-degree and very-ample descent nodes, and `ancestor` returned `None`. Existing nodes were opened and reused where applicable. The project Lean source was searched for the id, cubical/cubist, semiabelian and generic-ampleness terminology; no exact finished declaration was found. `searches.jsonl` retains all command results and the node records retain the precise queries. Spreading searches were reused as evidence before finding the existing 01ZR node; no redundant spreading node was created.

All eight proof steps are shorter than 2000 characters. I checked delivery-errors B--E against the written split: definitions have all mathematical data; the new node is neither a two-line consequence nor a supplied-object conclusion; every non-elementary imported theorem used by a step is a node in its `uses`; every quote in `citations.json` is copied from its actual statement; generic-point full faithfulness is not substituted for the dense-open theorem; local ampleness is upgraded to all affine opens by the explicit 01VJ tool. Base a field and dimension-zero group work without any shrinking, and a non-quasi-compact locally Noetherian base is covered by the final locality step.
