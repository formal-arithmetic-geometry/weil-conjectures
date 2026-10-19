# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-affine-generic-localization-intersection.json`: statement node, now split in six steps; no exact Mathlib match.
- `citations.json`: twelve step/node entries with verbatim statement quotations.
- No new nodes and no new Mathlib leaves. `searches.jsonl` contains the actual new search results. `write_split.py` is sandbox scratch material only.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, localization/generic-fibre/product language and related ring-theory declarations found no declaration giving the item's conclusion. The item has no recorded Lean declaration/audit frontier. The upstream master reference was not treated as a finished proof.

## WANTED

None. All mathematical sources used are present in `literature/stacks-project/`.

## Audit and changes

The item statement is unchanged. I read Stacks `flat.tex`, Tag 0810 (`lemma-helper-blowup-affine-space`), including the final paragraph where its product injection is used, and Tag 05DH (`lemma-base-change-universally-flat`). I also read the statements and proofs of Tag 05FQ (`lemma-universally-injective-local`) and Tag 05FT (`lemma-fibres-irreducible-flat-projective-nonnoetherian`). The all-field-extension domain condition is exactly geometric integrality of the fibre rings, and no Noetherian or reduced-base hypothesis is imposed.

The source abbreviates the crucial inclusion from a base-prime localization to the fibre-generic local ring by 05DH. This split proves that inclusion using two already existing, smaller inputs: 05FT makes the source projective over the local base, and 05FQ gives injectivity from the reduced map. This is the same local-inclusion/product route, not a replacement of the unit's semistable-alteration or flattening argument. The six steps contain all the localization computations and the final annihilator argument; no new node merely renames the item or one of its clauses. The proof is marked agent-origin because this particular specialization of 05DH is written here rather than copied from its proof.

The original ancestry referred only to Tag 0810; I clarified `blueprint.from.place` with the semistable-alteration/flattening place of the ancestor proof and retained its full `via` list. The item is not the unit's key node, so no unit record is changed. Read `dag/chapters/sec-trace-formula.json` and `dag/units/sk-i-curve-zero.json`. No `blueprint_update` is attached to this item.

## Searches and reuse

Searched the entire DAG by the item id, tags 0810/05DH/05FQ/05FT, product injection, fibre-generic localization, projectivity, and localization detection. Whole-blueprint searches used `tools/blueprint_refs.py ancestor` and `search` for “generic fibre localization injection 0810”, “localization intersection”, “fibre-generic”, “generic point of the fibres”, “0810”, “localization” and “universally injective”. None states this item. The generic local-algebra results are not blueprint duplicates. No new node was needed.

The five new Mathlib searches were run through `msearch.py` and are copied, with exact tool/query and returned records, into the item. Both semantic phrasings were read. `PrimeSpectrum.toPiLocalization_injective` (`Mathlib/RingTheory/Spectrum/Maximal/Localization.lean`, lines 164–175 read) uses all primes of a ring and does not give restriction to the fibre-generic primes. `instFlatAtPrime`, `RingHom.Flat.localRingHom`, going-down and general localized flatness only supply ingredients; `Mathlib/RingTheory/Flat/Localization.lean`, lines 45–95 read, confirms their scope. Thus the item is not a one-line specialization of those hits. The inherited searches from Q35 remain intact and are not claimed as searches run by Q84. No unavailable result was recorded as a negative match.

## Not duplicates

No new node pairs exist. Maintenance observation only: `lem-trf-affine-geometrically-integral-projective` and `lem-trf-local-fibres-integral-projective` both state the same 05FT result, the latter phrased geometrically. I cite the former, already the immediate parent's dependency, and leave both existing files untouched. `lem-trf-local-universal-injective-localization` is preservation of an already universally injective map under localization, and cannot replace the residue-injectivity criterion used here. The generic-fibre localization/domain node assumes the total algebra is a domain and cannot prove this item over a nonreduced base.

## Review by Q84

I reviewed the written node against delivery-errors B–E, reading every cited statement rather than its title or proof. For the item I checked 0810's final displayed product and the statements of 05DH, 05FQ and 05FT. There are no new nodes to source-check, search or edge-test. The sole statement remains the original full product injection.

Step 1 uses exactly the local-ring, maximal-ideal and fibre-quotient assertions of `def-weil-pbc-localization-at-prime`. A domain fibre is nonzero, so its coefficient field embeds. This proves that the specified inverse-image ideal is prime with contraction p, which is enough to define the map C -> D. It does not assume that B is a domain or identify a fibre ring with B/pB. The field-kernel calculation and inversion of base denominators are elementary.

Step 2 takes the projectivity conclusion of `lem-trf-affine-geometrically-integral-projective` with exactly the item's hypotheses. `def-weil-pbc-projective-module` explicitly includes the split-free characterization. `def-weil-pbc-module-localization` gives localization of the two split maps and their composition. I checked the inverse to the localized direct-sum comparison using finite supports and common denominators, so no finite-generation assumption on B over R or on the free basis is introduced. The statement of the projectivity node, not its internal proof, supplies all that is used.

Step 3 cites the injection-preservation definition of flatness and proves the preservation under the particular localization by its fraction-zero criterion. The stated tensor maps have inverse formulas; their A-balancing uses the invertible R\p action. Thus D is flat over A, as needed in 05FQ, not merely flat over B or R. `def-weil-pbc-module-tensor-product` states the generator/universal-property description used for these maps. This is a routine tensor-and-fraction argument, judged elementary, rather than an uncited invocation of a flatness theorem.

Step 4 uses the fibre-quotient identification of the prime-localization definition and the fraction criterion of the module-localization definition. I checked that quotienting by m and inverting B\q produce the stated actual reduction map. Every denominator has nonzero image in the domain F; multiplication by it is injective. Thus the residue map is injective. No assumption that q is maximal or that D is a field is made. The explicit inverse representative b/(rt) is well-defined modulo mD by the same fraction relation; no comparison lemma is hidden behind “transports”.

Step 5 applies the exact statement of `lem-trf-local-universal-injective-residue`: A local (step 1), C projective (step 2), D flat (step 3), and C/mC -> D/mD injective (step 4). Taking L=A gives injectivity of the actual canonical C -> D. This is not a circular citation of the product injection and does not invoke 05DH without a DAG node.

Step 6 uses exactly the proper-ideal containment assertion of `lem-weil-pbc-proper-ideal-contained-in-maximal`, and the explicit zero-fraction criterion from `def-weil-pbc-module-localization`. The annihilator is an ideal of R of the single element b in the R-module B, not a supposed ideal of B with the same name. If b were nonzero it would be proper. A maximal ideal containing it contradicts the annihilator outside that prime supplied by b/1=0. This proves the kernel-zero conclusion and then full injectivity by subtraction. The zero ring case has no primes and B=0, so the empty product causes no exception.

Small cases checked: R=k, B=k[x] (the sole factor is k(x)); R=k[epsilon]/(epsilon^2), B=R[x] (nilpotents of R survive, so a residue-field-only product would be wrong, but the local rings used here retain them); R a product of two fields with B=R[x] (the two base-prime localizations detect both components); the identity R -> R for arbitrary nonreduced R (the conclusion is the usual local detection); R=0 (empty product). The field-kernel, localized projectivity and flatness checks work in each case. No extra Noetherian, finite-module, injective base-map or reducedness hypothesis enters. No step exceeds 2000 characters and no source's omitted comparison remains implicit. Proof dependencies are the union of step uses, and citations.json quotes the full exact statement for each of its twelve entries.

The review corrected the source-only blueprint place and filled the missing proof; no statement dispute or mathematical correction was needed. There are no off-route statement tools: the two non-Mathlib theorem inputs belong to the same unit; the other inputs are existing definitions or Mathlib leaves. No SGA source is used. Only stage 1 work was performed; no compiler, Lake, Lean-file writing, live-repository writing or git command was used.

## Unfinished work

None in this one-level split. The two existing unsplit theorem inputs remain their own DAG items.
