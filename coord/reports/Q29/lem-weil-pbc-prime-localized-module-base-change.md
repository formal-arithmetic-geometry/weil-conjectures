# Stage-1 delivery: lem-weil-pbc-prime-localized-module-base-change

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-prime-localized-module-base-change.json: statement item, split in five steps, using existing Mathlib leaves; statement unchanged.
- citations.json: ten entries, each quoting the actual cited statement verbatim.
- report.md and searches.jsonl: review and actual search log. No new nodes; no new Mathlib leaves.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint id and localized-module/base-change/residue-field concepts found constituent comparisons and geometric stalk comparisons, but no declaration giving this item's entire statement. In particular affineBaseChangeTildeModuleMap_localized is about a specified geometric derived comparison; localizedModule_of_liftedTensorComparison assumes a module comparison and does not assert these two prime and residue-field comparisons.

## WANTED

None. The needed Stacks sources are present locally.

## Corrections and scope

No statement dispute or statement change. The item was unsplit and had no proof. Its inherited searches and metadata were retained; the sandbox initially contained only launcher brief markers. New searches used only msearch.py. Their hits include LocalizedModule.equivTensorProduct, IsLocalizedModule.rTensor, IsLocalizedModule.isBaseChange, ModuleCat.extendScalarsComp, and Localization.isLocalHom_localRingHom. The constituent facts already have DAG nodes, so none was created. Two semantic phrasings were tried; the whole paired comparison with its normalization and compatibility is not supplied by any returned declaration as a one-line specialization.

Read the latest blueprint proof of thm-weil-pbc-finite-etale-lifting under sk-lem-pbc-p1-injective-fibre, and the chapter and unit records. This is subsidiary algebra in its existing lci-field-change dependency chain, not a replacement for the unit or chapter route. The current blueprint's rank-one discussion is not used in this split. The item's inherited source points to the displayed comparison in Stacks 00SI, which is precisely the calculation expanded here; Stacks 00SJ was also read as context. The additional locality and arbitrary-module fraction formulas are written out, so proof_origin is honestly marked agent.

## Not duplicates

No new node was created. Existing lem-weil-pbc-localization-tensor-over-base and lem-weil-pbc-module-base-change-transitive are reused. The principal-localization-only lem-weil-pbc-localization-module-tensor and lem-weil-pbc-localization-away-tensor-iso were read but not applied to prime localizations. The flat-map hypothesis in lem-weil-pbc-flat-local-ring-maps is unavailable here, so that node is not cited. Ring locality is proved directly from fractions, using the general ring localization universal property.

## Review by Q29

I read algebra.tex at 00SI (lemma-lci-field-change-local): its displayed chain compares the localized conormal fibres by extension of residue fields. I also read 00SJ (lemma-lci-field-change), 00CP (proposition-universal-property-localization), the prime-local residue-field paragraph in 07BH, 00CX (lemma-tensor-product), 00DK (lemma-tensor-localization), and 00D2 (lemma-tensor-with-bimodule), including the proofs of the latter three. No SGA source is used. There are no new nodes requiring a further source review.

Step 1 uses the exact fraction formula and uniqueness supplied by lem-weil-pbc-ring-localization-universal-property, and the maximal-ideal/residue-field description stated by def-weil-pbc-localization-at-prime. Its hypothesis is checked by f(A minus p) being contained in B minus q. I wrote the numerator membership check, which proves equality of the inverse-image maximal ideal, not merely containment. The residue quotient agrees with Frac(A/p) by the displayed fraction relation, so this is the field map the statement specifies.

Step 2 uses the statement of lem-weil-pbc-localization-tensor-over-base with both base and algebra C, first module C and second module P. It applies to arbitrary modules and arbitrary multiplicative subsets, so it really applies at a prime. The unit and symmetry formulas are proved from the universal property and generation clause of def-weil-pbc-module-tensor-product. The functor on localized maps is given in def-weil-pbc-module-localization. I added an explicit C_r-linearity check, since the cited localization-tensor node states A-linearity and the item requires linearity over the localized ring. The calculation also fixes the direction and generator formula of the equivalence.

Step 3 uses the full statement of lem-weil-pbc-module-base-change-transitive twice, for A to B to B_q and A to A_p to B_q. Step 1 supplies the latter ring map and its compatibility. The linear equivalence of step 2 may be tensored because the inverse tensors to an inverse, which follows on pure tensors from the stated tensor universal property. The composite j inverse after h gives the required direction of Phi, and both h and j are evaluated on the precise elements used in its formula.

Step 4 uses the same transitivity node for A_p to kappa(p) to kappa(q), and for A_p to B_q to kappa(q). Both towers commute because the residue map was induced by the local ring map in step 1. The composite defining Psi contains the actual tensor of Phi inverse. This proves the compatibility clause at construction time. The formula for alpha uses the multiplication formula actually present in the cited transitivity statement; no unstated naturality or comparison lemma is assumed.

Step 5 uses only tensor balancing from def-weil-pbc-module-tensor-product and the maps already constructed. I checked that s outside p implies f(s) outside q, hence its residue is nonzero. Moving the scalar 1/s from m/s to the final field factor gives exactly the denominator in the requested formula, after which beta inverse and Phi inverse give the stated numerator. This is an explicit calculation, not an appeal to unspecified transport.

Against delivery-errors B through E: every cited statement was opened and quoted, all non-elementary tools are actual cited nodes, every proof step has a source and a Boolean elementary flag, and proof_deps is the union of uses. No statement-only lemma was used for a claim absent from it, no duplicate or clause-restatement node was introduced, no self-citation or dependency back to the item was introduced, and all steps are below 2000 characters. The only elementary steps are the fraction/locality check and the final tensor-balancing calculation; the tensor-localization and base-change results themselves are cited in non-elementary steps.

Small cases checked by the same formulas: M=0 gives zero modules and unique isomorphisms; A=B and f=id gives the identity comparisons; a noninjective map Z to F_p with q=0 has contracted prime (p), a local map Z_(p) to F_p and denominator units exactly as required; with M=Z/p the proof still applies although M is not flat. Taking a field extension and both primes zero reduces Psi to ordinary scalar transitivity. If B is the zero ring there is no prime q, so there is no assertion to instantiate. No finiteness, flatness or injectivity is assumed or used.

## Unfinished work

None for this stage-1 split. Server dry run and direct delivery are the remaining operational checks.
