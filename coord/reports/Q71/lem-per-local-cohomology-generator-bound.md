# Q71 stage-1 delivery

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-generator-bound.json`: item, split; no Mathlib match. Its mathematical statement is retained, with an explicit citation to the existing ideal-power torsion definition.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-cech-bound.json`: new statement-only node, unsplit; no Mathlib match. It states the Noetherian derived-torsion/extended-localization-complex comparison, not the generator inequality.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-local-cohomology-sum-spectral.json`: new statement-only node, unsplit; no Mathlib match. It states the convergent first-quadrant ideal-sum spectral sequence with its finite-filtration meaning, not the dimension inequality.
- `citations.json`: one verbatim statement quote for each node in each step's uses.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item and helper ids, localCohomology, local cohomology, derived torsion and the related spectral sequence found no project declaration that states the item or either new node. The existing Supports.lean concerns etale classes with supports, not these module torsion functors. No Lean was written or compiled.

## WANTED

None. All cited source passages are present in `literature/stacks-project/`.

## What was incomplete or corrected

The imported item had no proof. Its mathematical statement already has the necessary Noetherian and proper-sum hypotheses, and is retained. I added a definition citation, proof steps, proof dependencies and the split report, retaining the original creation record, Mathlib searches and blueprint ancestry.

During self-review I corrected my draft's confusion between closed-support local cohomology and right-derived ideal-power torsion. The arbitrary-ring closed-support computation of Tag 0A6R alone does not identify the latter: the source explicitly warns they differ for general rings. The Cech node now assumes Noetherianity and cites Tag 0956; the spectral-sequence node also assumes Noetherianity and uses the comparison in Tag 0955. I corrected the draft final step, which had shown only the weaker r+e bound, to apply the proved generator bound to J=(f_1,...,f_e) and then the proved proper-sum inequality. I replaced version-dependent numerical source locations with exact tags and labels.

The first delivery dry run rejected helper search records because the searches had been logged under the helper ids rather than the dispatched item directory. I reran them through msearch with the dispatched item argument, read the hits, added a grep in the correct `Algebra/Homology` directory and a valid `localCohomology` Loogle query, and used the actual log records as search results. The earlier wrongly prefixed grep directory gave zero hits; it is not relied on for absence. Searches in Mathlib's LocalCohomology.lean were followed by reading that file: it defines Ext-colimit local cohomology and radical comparisons and explicitly lists the derived-torsion/Cech comparisons as future work.

## Source error

The unrestricted source Tag 0ECP (lemma-cd-sum) is false with the definition's cd(A,A)=-1 convention: take A a nonzero field and I=J=A, obtaining -1 <= -2. The imported item already restricts to I+J != A, so no correction to its mathematical statement is required. This restriction also ensures the two summands have nonnegative finite bounds, as used in Step 3.

## Not duplicates

lem-per-local-cohomology-cech-bound vs lem-weil-pbc-ring-complex-cech-base-change: both sources mention 0A6R, but the existing node assumes augmented Cech models and proves a scalar-extension map is a quasi-isomorphism; it does not identify right-derived ideal-power torsion with the localization complex. The new node is the Noetherian torsion comparison of 0956 for arbitrary modules.

lem-per-local-cohomology-cech-bound vs lem-sbc-local-cohomology-derived-torsion: the existing node identifies the Ext colimit with derived torsion; the new node identifies the explicit finite localization complex with derived torsion. Neither gives the other's comparison as a one-line specialization.

lem-per-local-cohomology-sum-spectral vs lem-sbc-local-cohomology-derived-torsion: the existing node supplies an Ext-colimit identification, not a spectral sequence for I+J. The new node gives an E2 page and a convergent filtration for the sum.

lem-per-local-cohomology-cech-bound vs def-weil-pbc-extended-localization-cech: the existing definition constructs a localization complex and its maps on a ringed site. It does not assert that this complex computes the right derived functors of ideal-power torsion.

lem-per-local-cohomology-cech-bound vs lem-per-local-cohomology-generator-bound: the new node is a complex/cohomology comparison and contains no generator or sum dimension inequality. The item's argument counts its degrees to prove the bound.

lem-per-local-cohomology-sum-spectral vs lem-per-local-cohomology-generator-bound: the new node is a spectral sequence with a finite-filtration conclusion, without any cohomological-dimension inequality. The item supplies the vanishing rectangle and finite-filtration argument.

Whole-DAG searches for 0A6R, 0955, 0956, 0BJC and the local-cohomology/Cech concepts, plus blueprint_refs searches for those tags, local cohomology, derived torsion and Cech model, found no matching existing statement. Non-source occurrences of 0955/0956 were reviewer or commit identifiers. The existing extended-Cech reflector nodes concern derived completion via internal Hom, not ideal torsion.

## Review by Q71

I read local-cohomology.tex Tags 0DX7 (lemma-cd), 0DX8 (definition-cd), 0DX9 (lemma-bound-cd) and 0ECP (lemma-cd-sum), and dualizing.tex Tags 0A6R (lemma-local-cohomology-adjoint), 0955 (lemma-local-cohomology-noetherian), 0956 (lemma-compute-local-cohomology-noetherian) and 0BJC (lemma-local-cohomology-ss). The item follows the source's actual proof: extended Cech computation for generators and the support spectral sequence for sums. The chapter and unit route remain unchanged; the item's pre-existing ancestry places this commutative-algebra input beneath the complete-local connectedness input in the perverse-duality construction. This is not a unit's key node, so no unit file is changed.

For Step 1 I read the new Cech statement in full. It assumes exactly the Noetherianity available for A, introduces the generators and all localized modules and the alternating differential, identifies cohomology with derived ideal torsion, and includes the empty-list case. Its zero terms above r immediately imply vanishing for every M; the nonempty upward-closed set of integer bounds has a least member. This proves finite-bound existence as well as the generator upper bound, including for the later summand J. No unrecorded comparison with the non-Noetherian closed-support functor is used.

For Step 2 I read def-sbc-ideal-power-torsion-functor, whose statement gives precisely the torsion submodule and computation through injective resolutions. The kernel calculation explicitly explains H^0=Gamma; A/I is nonzero by properness and is killed by I. This rules out -1 and proves the lower bound using the preceding finite upper bound. The node is a definition, not cited as an unproved acyclicity theorem.

For Step 3 I read the new spectral statement and checked that its E2 order is H_I^p(H_J^q(M)), matching the proof. I,J are finitely generated, A is Noetherian, and M is a module in degree zero, so the source's bounded-below hypothesis is met. Properness of I+J implies properness of each summand and hence a,b >= 0. The all-modules quantifier in cd(A,I) applies to the inner cohomology module, so the claimed E2 rectangle is valid. Zero E2 terms stay zero as subquotients on every page. The node explicitly supplies a finite abutment filtration, so zero graded pieces force the abutment to be zero; convergence is not silently assumed.

Step 4 uses only the already established Steps 1 and 3: J is e-generated and proper, so cd(A,J)<=e, and substitution gives cd(A,I+J)<=cd(A,I)+e. It is an elementary deduction, not a new lemma or a direct restatement moved into a helper. Its empty uses list is intentional because it cites no additional node.

For every cited use I copied a verbatim statement into citations.json. proof_deps is the exact union of uses. Both new nodes contain statements only, have explicit objects and hypotheses, and inherit the full blueprint via list including the item. None has been split recursively; no new definition, hollow data, Lean file or SGA reference is introduced. All four proof steps are shorter than 2000 characters.

I checked A a field with I=0 (cd=0), the empty generator list r=0, e=0, I=0 or J=0 in the spectral sequence (identity torsion gives the same inequality), zero generators and nilpotent generators (zero localizations are permitted), and I+J=A (excluded). The helper assertions themselves also allow the zero ring without difficulty: every module and every displayed cohomology group is zero. These checks exposed the missing Noetherian qualifier in my initial helper draft and the insufficient r+e conclusion in the initial final step; both are corrected in the delivered files.

## What remains

No unfinished part of the item's split. The two new nodes are intentionally statement-only next-level items, with no Mathlib match. Final acceptance is the required delivery dry run and push.
