# Stage-1 report: lem-per-finite-formal-map-differential-cokernel

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-finite-formal-map-differential-cokernel.json`: existing statement, now split into six proof steps. Statement and statement dependencies unchanged. Retained provenance, prior Mathlib search records, and the complete blueprint ancestry. No new nodes and no new Mathlib leaves.
- `citations.json`: twelve verbatim statement citations, one for every step/node pair.
- `report.md`: this report. The sandbox also contains the source-text extraction, local JSON-writing script, and the search command's append-only log; these are working material.

## Attachments

None. Searches for the item id, its blueprint docstring tag, completed/continuous differential terminology, finite formal maps, and the Kähler differential notion under the read-only slopmaster2 project did not find a declaration proving this statement. Master is reference material only; no sorry-bearing master declaration was counted as a proof.

## WANTED

None. I read the supplied ILO PDF and local Stacks sources. No SGA source is used.

## Findings and corrections

The item was statement-only, with no proof and no completion dependency. Its statement is correct as written, including the supplied finite map (which need not be injective), the fixed residue-field section, and arbitrary characteristic. I supplied the proof and its actual dependencies; there is no statement dispute or change to the blueprint route.

ILO IV 1.2.5 (printed p. 49) recalls continuous derivations and completed differentials. IV 2.1.12 (printed pp. 52–53) identifies ordinary relative differentials for the finite map with their completion and displays the completed transitivity sequence. I expanded this argument using the universal property: explicitly construct the completed right arrow, quotient by the differentials of the parameters, and show the induced derivation kills every series by truncation. The proof is marked agent-written because it gives this direct algebraic verification rather than importing ILO's EGA completion-exactness theorem. Its general completion inputs are existing DAG statements for Stacks 05GG, 031D, and 00MA.

Whole-DAG statement/title searches found `lem-weil-pbc-module-completion-complete`, `lem-weil-pbc-finite-over-complete-ring`, and `lem-weil-pbc-finite-module-complete-over-complete-noetherian`. These supply exactly the needed generic completion facts. The first is a Mathlib leaf; the other two are declared as generic tool uses from another unit. I also inspected the existing ordinary first differential exact-sequence node; its ordinary assertion alone does not justify completing an infinite differential module, so the proof does not use it for that purpose. No new surrogate for a clause of the item was introduced.

The first exploratory Mathlib batch concerned exact limits of finite-dimensional vector spaces; its logs are retained but those results are not used. After finding the existing completion nodes I used the inherited item search questions, rerunning their exact queries with the required Q77 search command. Two LeanFinder phrasings, Loogle, LeanSearch and grep all returned successfully. The ordinary candidate `KaehlerDifferential.exact_mapBaseChange_map` was read in `Mathlib/RingTheory/Kaehler/Basic.lean:756`, together with `map_surjective` at line 713. It supplies ordinary transitivity, without completed differentials or the comparison proved here. The searches therefore do not turn this item into a Mathlib leaf. Blueprint searches for completed differentials, continuous derivations, differential, finite over complete, and formal parameters found no blueprint node stating this item.

## Unfinished work

None for this stage-1 split. No Lean was written or run. The split uses already-existing general completion statements rather than creating further nodes.

## Not duplicates

No new nodes. There are no new/existing same-tag pairs to distinguish.

## Review by Q77

I read the item, its chapter and unit records, the blueprint ancestor's current proof, and the ILO passages above. The item belongs below the existing Artin–Gabber duality/Cohen–Gabber ancestry, rather than being a key statement of the Fourier-perverse unit, so no chapter or unit realization record is changed. Its fixed finite formal map is preserved throughout.

Step 1 cites the Noetherian-ring definition for finite generation of the maximal ideal and the differential definition for symbols, additivity and Leibniz. I checked that the latter really states both the universal property and the explicit symbol quotient. The finite residue differential calculation uses the given coefficient section: choose residues of the finitely many coefficients and obtain an error in the square of the maximal ideal. Leibniz puts its differential in the maximal ideal times the differential module. No smoothness, reducedness, field perfection, or finite type over k is assumed. This is a written calculation, not an appeal to finiteness of ordinary absolute differentials.

Step 2 uses the **statement**, not the proof, of the module-completion node. Its clause (1) gives completeness and separatedness for an arbitrary module; clause (2) gives precisely the first-quotient identification and the specified projection. Its finite-generation hypothesis is on the ideal, established in Step 1, and not on the original differential module. The second cited statement explicitly says that **any** lifts of residue generators generate the module over a complete ring. I checked all three of its hypotheses: B is complete, the completed module is separated, and its first quotient has the finite generating family already computed. This also proves that the canonical map from ordinary to completed differentials is surjective, which is later used to test maps on actual differential symbols. The local Stacks source read was 05GG (`lemma-hathat-finitely-generated`, algebra.tex around 22645) and 031D (`lemma-finite-over-complete-ring`, around 22860); the tags were verified in tags/tags.

Step 3 uses the finite-module notion and the explicit universal differential definition. Differentiating an R-module expansion of an element of B shows that the chosen finite module generators' differentials generate the relative differential module. I then apply the finite-module-completeness statement with ring **B**, ideal its **maximal ideal**, and this finite relative module. That citation's displayed canonical map is exactly the map used here. Its hypotheses do not require proving any comparison of the R-adic and B-adic topologies. I read Stacks 00MA (`lemma-completion-tensor`, around 22901), part (3), and the cited node's statement, so completeness and separatedness follow with the required ideal.

Step 4 constructs the map at each quotient using the universal property, explicitly checks compatibility through B-linearity, and uses Step 3's canonical inverse-limit identification. Thus the right arrow is determined by universal derivations, not merely an arbitrarily chosen cokernel isomorphism. It kills each parameter differential. The module Q is a quotient of the finite completed module, so the images of that same finite family generate it; this is a direct finite-generation argument. The finite-module-completeness statement applies again to Q over the same complete Noetherian ring B and supplies the separatedness needed next. There is no unproved assertion that arbitrary completion is exact.

Step 5 uses the formal-series definition and differential rules already read. I checked the tail-ideal membership by grouping tail monomials according to finitely many degree-(m+1) divisors, giving actual series coefficients; it does not assume an analytic convergence theorem. Localness sends each T_i into the maximal ideal of B and therefore sends the whole tail ideal into its (m+1)st power. The explicit Leibniz estimate from Step 1 gives membership of the differential in the mth power times Q, and Step 4's separatedness makes it zero. This is the precise passage from killing the finitely many parameters to killing the entire formal base ring. It proves the claim in this step without a hidden continuity or completed-tensor comparison lemma.

Step 6 uses the stated bijection between module maps and derivations. Both proposed composites are checked on the actual universal differential generators. For Q this is legitimate because Step 2 proved the canonical map onto the completion is surjective; for the relative module, its symbol construction directly supplies the generating family. The inverse identities identify exactly the kernel with the indicated B-span, and the finite free map has that span as its image. Thus both the exactness clause and the normalization of the two arrows are checked.

I checked delivery-errors B–E against these files and the open sources: no new unsplit statements, missing new notions, duplicate or relabelled nodes, unavailable searches misreported as negative, uncited completion theorem, source-dependent meaning, circular inference, or changed hypotheses. Citations were copied verbatim from the existing node statements and their uses were checked above. The general lemmas are used as tools, not to alter the unit's route. Every proof step is shorter than 2000 characters; Steps 1, 5 and 6 are explicit elementary symbol/truncation/universal-property arguments. The non-elementary completion results in Steps 2–4 are cited nodes.

Small cases checked: e=0 gives R=k and, since B is finite over k, ordinary absolute differentials are finite and already complete, so the right arrow is an isomorphism. B=k, including arbitrary e with all parameters mapped to zero, gives the zero sequence. In characteristic p, R=k[[T]], B=k[[x]], T mapping to x^p has zero parameter differential and relative differential module B dx; the result gives the right isomorphism. For T mapping to x in B=k[[x]]/(x^2), the parameter differential spans the completed differential module and the relative module is zero, including characteristic 2. These check noninjective maps, ramification, and nilpotents without adding any reducedness assumption. Infinite or imperfect residue fields create no problem: only the given coefficient section, finite ideal generation, and the supplied module-finite map are used.
