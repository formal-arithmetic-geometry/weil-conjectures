# Stage-1 report: lem-sfb-fibrewise-flat-complex-concentration

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-fibrewise-flat-complex-concentration.json`: statement, split; seven proof steps; no change to the statement. All proof inputs reused from existing nodes.
- `citations.json`: 19 entries, one for each step/node pair, copying the cited statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command’s own log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for fibrewise/fiberwise flat-complex terminology. No project declaration states the whole item. `WeilConjectures/RingTheory/FlatModInjective.lean` gives the already attached local algebra tool, not this complex or its zigzag. A sorry-free tool for one step is not an attachment of the item.

## WANTED

None. The proof sources used here are present in `literature/stacks-project/`.

## What was wrong or missing

The imported node had no proof, despite a precise source reference. I kept every hypothesis and conclusion, and supplied the source’s cokernel argument and the explicit checks for the canonical zigzag. In particular I did not replace the zigzag by an unspecified existence of an isomorphism.

The inherited `blueprint.from.node` is null: `tools/blueprint_refs.py ancestor` reports None because the created.item chain ultimately points at the stage-3 module `Sheaf.SixFunctors.CtfStabilityDirectImages`, not at a DAG node. The inherited detailed `from.place` already identifies det-thm-sf-ctf-stability-direct-images and the intermediate input. I retained this provenance and documented its mathematical place in split_report.blueprint; I did not edit anybody else’s ancestry. I read the current files under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, including the unit and the direct-image proof. The imported unit record has an older chapter-level organization; no unit or chapter route is replaced by this generic algebra calculation.

Whole-blueprint searches for “flat complex”, “fibrewise”, and “universally injective” found no duplicate of the item. The only universally-injective blueprint hit concerned scheme conventions, not module maps. Searches of the DAG for Tag 00ME and relevant titles found the exact existing local criterion and the general tensor/localization tools used here. This is why no new lemma nodes are necessary.

## Mathlib searches

The five Q73 searches in searches.jsonl were executed and their returned types read: LeanFinder with two phrasings, Loogle with `Module.Flat, CochainComplex`, LeanSearch for the fibre-concentration/truncation claim, and the logged grep pattern. All services answered. LeanSearch found truncation quasi-isomorphism criteria, whose hypotheses already assert the support that this item must establish after arbitrary scalar extension. I also read the beginning of `Mathlib/Algebra/Homology/Embedding/CochainComplex.lean`: it defines and studies truncations, not the Noetherian residue-fibre argument. LeanFinder found flat-tensor exactness and faithfully-flat reflection of exactness; the tensor factor here need not be flat. The grep hits were unrelated uses of “fiberwise”. These are no match for the whole item. Original imported search records were retained, and only actually run Q73 queries were appended.

## Not duplicates

No new nodes were created. The local criterion is reused as lem-weil-pbc-flat-mod-injective (00ME), rather than reintroduced globally or as a complex-specific variant. The stalkwise universal-injectivity lemma, the universally-exact flat-submodule lemma, and the flat-kernel lemma already give the remaining non-elementary inputs.

## Review by Q73

I read the last two proof paragraphs of dualizing.tex, Tag 0E2F, lemma-base-change-relative-dualizing, beginning with the cokernels Q^n. That proof uses a bounded-below complex with finite terms flat over its Noetherian base, applies 00ME independently in each degree other than zero, then treats Z^0 and H^0. This exactly supplies the item’s route. The item’s additional flatness hypothesis on H^0 was retained and is used in step 6. No finite type or flatness of the scalar extension is introduced.

For step 1 I opened lem-weil-pbc-tensor-right-exact and algebra.tex Tag 00DF, lemma-tensor-product-exact. Its statement gives the cokernel identification after tensoring for any module, hence the kernel description of fibre cohomology. Finite generation of Q^n is the explicit image of the given generating list, not an appeal to an uncited finiteness theorem.

For step 2 I opened every cited statement: the prime-localization definition states its maximal ideal; the Noetherian-ring definition states ideal finite generation; localization-module-exact states exactness for modules; localization-tensor-over-base states precisely the natural tensor comparison needed; flat-tensor-exact preserves the injection; and flat-over-localization gives equivalence over R and R_p for a module already admitting R_p action. I read algebra.tex Tag 00CS (proposition-localization-exact), Tag 00DK (lemma-tensor-localization), Tag 00D2 (lemma-tensor-with-bimodule), and Tag 00HT (lemma-flat-localization). The step checks locality by inverse image of the maximal ideals. It proves Noetherianity of S_q by contraction of ideals and finite generation of Q^n_q by localized generators. It writes out the residue-field/quotient tensor identifications. Thus the criterion is applied over the local rings R_p and S_q, not over the original possibly nonlocal rings. The use of exact localization on a sequence with zero first term legitimately preserves injectivity.

For step 3 I read lem-weil-pbc-flat-mod-injective and its source algebra.tex Tag 00ME, lemma-mod-injective. It assumes only that the source module is finite over the Noetherian target local ring and that the target module is flat over the base local ring; it does not require that source module to be flat in advance. Its conclusion explicitly gives both injectivity and flatness of the cokernel. I read lem-weil-pbc-flat-quotient-tensor-injective against Tag 00HL, lemma-flat-tor-zero, before using that flat cokernel to obtain universal injectivity. Finally I read lem-trf-universal-injective-check-stalks against Tag 05CL, lemma-universally-injective-check-stalks. Its statement is exactly the needed equivalence for an S-linear map tested over R_p at every prime of S. These are tools of other units, declared in split_report.tool_uses where needed; they do not replace a six-functor proof route.

For step 4 the universal injection gives vanishing for every coefficient module using step 1, not just for residue fields. I opened lem-trf-universally-exact-flat-submodule and read Tag 058P, lemma-ui-flat-domain, which explicitly states the flat-submodule conclusion used for Q^1 inside E^2. Right exactness supplies universal exactness of the cokernel sequence. I then opened lem-weil-pbc-flat-ses-kernel-flat and Tag 00HM, lemma-flat-ses: E^1 and Q^1 are the two flat modules in its hypothesis, and B^1 is their kernel. No unproved flatness of Z^0 is assumed.

For step 5 both applications of the flat-quotient tensor lemma have the required flat last term, respectively B^1 and Q^1. The displayed factorization of the tensor differential proves that its kernel is the image of Z^0 tensor L. This checks the precise inclusion map and avoids assuming that arbitrary tensor products preserve kernels. The argument is about ordinary termwise tensor complexes, not a claim that every bounded-below flat complex is K-flat.

For step 6 I checked the short exact sequence with quotient H against the explicit H-flat hypothesis of the item and the same flat-quotient lemma. Right exactness makes E^{-1} tensor L surject onto B^0 tensor L. The degree-zero quotient is therefore exactly H tensor L. I verified the negative boundary degree -1 separately: its outgoing differential has the same kernel because Z^0 tensor L injects into E^0 tensor L. The abstract-derived-category definition, whose statement I opened, defines ordinary cohomology and quasi-isomorphisms and therefore gives both claimed quasi-isomorphisms from these calculations. The sheaf-complex definition already listed among the item’s statement dependencies can be interpreted on the one-object ringed site; the ordinary complex notion and cohomology are also explicitly provided by the abstract-derived-category node. I made no statement change.

For step 7 I opened the tensor-product and abstract-derived-category definitions. The tensor definition supplies generators, bilinearity, functoriality and the universal property. The proof writes the two inverse scalar-associativity formulas and checks both zigzag squares before localization; equality on pure tensors proves equality of maps. Step 5 and step 6 also identify the good truncation and H^0 after an initial extension, so these are the zigzags for the base-changed complex under the displayed identifications, even when that new ring is non-Noetherian. The derived isomorphism is explicitly Q(b)Q(a)^{-1}, which proves the requested naturality. This is a routine verification from the displayed maps, and is marked elementary.

I checked B1–B10: no new statement-only nodes, invented Mathlib leaves or unrun searches; no data or Lean written; all node citations exist; TeX has a single layer of escapes; blueprint same_as was searched. I checked C1–C8 by opening every cited statement and writing one verbatim citation entry for each use; no proof-internal object of another node is used, and all external tools are generic module lemmas. I checked D1–D5: the item itself carries the cokernel and truncation argument, no content is hidden in a renamed child, and the source applies the criterion independently in each nonzero degree. I checked E1–E7: local versus global rings, finite generation, the flat target versus flat cokernel, and tensor directions are all explicit. Small cases tested were the zero complex, a flat module concentrated in degree zero, a contractible two-term complex, and extension to the zero ring; all give the specified identity or zero zigzags. A differential given by multiplication by a nonunit in a two-term free complex fails the fibre hypothesis at primes containing that element, so it supplies no counterexample. The argument never uses an upper bound on the complex and thus does not silently add one. Every proof step is shorter than 2000 characters. No statement dispute or route correction was needed.

## Unfinished work

No mathematical part remains unfinished. The split still rests on the existing nodes that are not yet Lean-closed, as expected in stage 1. Delivery validation is run with the prescribed server tools; no local check_dag, review_split or preflight script and no Lean/compiler/Lake command is used.
