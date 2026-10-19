# Worker report: cor-sf-direct-image-ctf-nonproper — return L repair

## Files written

- `dag/nodes/sec-six-functors/cor-sf-direct-image-ctf-nonproper.json`: retain the reviewed statement and two-step proof; refresh the split report with this current-base review and blocker.
- `report.md`: replace accumulated historical reports with this fresh repair record.
- `citations.json`: retain the five quotations, independently checked against the current statements.

New nodes: 0. Mathlib leaves: 0. Old log and review files are historical evidence only.

## Attachments

None. I searched the read-only slopmaster2 SixFunctors source for the item and direct-image declarations and reread `WeilConjectures/SixFunctors/Etale/Derived/Stability/DirectImage.lean` lines 60–165. The generic bounded-constructibility theorem at line 81 and numerical Tor-amplitude theorem at line 96 contain `sorry`. The finite-coefficient theorem at line 114 supplies bounded constructibility only. The finite-Tor theorem at line 138 calls the sorried numerical theorem and asserts existence of an interval, rather than this exact interval. No finished declaration supplies every clause. Upstream master is reference material only.

## WANTED

None. The complete sources used are available under `/home/ubuntu/weil-launcher-nt/literature/`; no download was needed.

## Return L and repair

The return says: `NOT MERGED cor-sf-direct-image-ctf-nonproper: fix dag/units/sk-thm-sf-direct-image-tor-amplitude.json: not a file of the delivery (a fix only adds a NEW statement node; it never touches another node)`.

I reread the full immutable maintainer review and landing result in `/home/ubuntu/weil-launcher-nt/reviews/NK__cor-sf-direct-image-ctf-nonproper__106d37836022/`. The reviewer accepted the mathematics and the two generic tools, but required the own-unit realization. Landing refused because the attempted repair included the existing unit file, which is outside the delivery packet. I removed that out-of-scope file from the sandbox; the authoritative unit realization remains a maintainer-side metadata repair under `coord/dag-sync.md`.

The supported delivery command builds the delivery on the current origin in its temporary worktree. No direct git command was run in the shared repository, and no push was requested.

## Not duplicates

There are no new nodes or same-tag pairs. I repeated the whole-blueprint `direct image` search and searched the six-functor DAG for direct-image and Tor statements. The general N theorem is reused. The pro-etale and etale-origin corollaries have different domains and use this small-etale result; they do not supersede it. No elementary specialization or clause of this item is moved into a child.

## Review by NK

I read the stage-1 brief, worker role, stages/1-dag.md, the three levels in SETUP.md, delivery-errors B–E, GOAL.md, coord/STATE.md and coord/dag-sync.md. This remains stage 1: no Lean writing, compiler, Lake, build, delegation or push. The generic repair template's instruction to compile is superseded by the explicit prohibition on all compiles.

I opened the current item, its chapter and unit, and all fifteen distinct immediate dependency statements. Comparing those records with the immutable reviewed snapshot finds fourteen unchanged records; only `lem-sf-etale-direct-image-vanishing` differs, solely in `lean` and `reviewed_lean`. Its mathematical statement is unchanged and I reread its complete text. The shared item is still imported, so this split has not been superseded by a finished or reviewed split.

I read the complete archived item source and own-unit `_section.md` in `blueprint/master/blueprint/sec-six-functors/sk-thm-sf-direct-image-tor-amplitude/`; the complete general theorem in `sec-six-functors/sk-prop-sf-rf-shriek-preservation/thm-sf-direct-image-tor-amplitude.md`; the vanishing lemma and UDV definition in `sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/`; the Tor definition in `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-tor-amplitude.md`; and the flat-model source in `sec-smooth-purity/sk-lem-sf-flat-model/lem-sf-flat-model.md`. There are no new-node sources to certify.

The statement retains the global finite-field datum, ell different from p, n>=1, the exact finite DVR quotient A, algebraically closed k, finite-type X and Y, natural d with dim X<=d, separated finite-type f, bounded constructible small-etale module complex, integer endpoints, and both conclusions. The expanded coefficient data only spell out A. `def-weil-proper-morphism` defines separatedness by the closed diagonal; citing it adds no properness. The derived-category, sheaf and direct-image definitions explicitly cover ordinary constant-ring module sheaves. The constructibility and Tor definitions are the ones used here. No condensed, completed or pro-etale coefficient category is identified with this category.

Step 1 takes exactly the vanishing lemma's final global-stage UDV clause. Every hypothesis is supplied: the finite-field datum and finite coefficient stage, finite-type schemes and f, source dimension bound, and separatedness for the UDV convention. The UDV definition quantifies over every module sheaf and every r>2d, with bound independent of the sheaf. The geometric estimate is cited; substitution N=2d and nonnegativity are elementary. Both quoted statements literally say what the step uses.

Step 2 specializes the general theorem at N=2d. Its ground-characteristic condition is ell!=p; n>=1, coefficient stage, finite-type schemes, separated finite-type f and bounded constructible input all match. Step 1 supplies its uniform bound. Its statement supplies BOTH bounded constructibility and the interval [a,b+N]. The flat-model condition (i) and explicit small-etale clause use the same universal derived-tensor test as `def-kun-tor-amplitude`. This citation matches the predicate; it does not apply the ordered-interval existence equivalence when a>b or change sites. All three quoted statements give the facts used. Both substantive applications correctly have elementary=false.

The own-unit route is the flat model, truncation spectral sequence, constructibility, ordinary finite-constant projection and residue test. The general theorem's complete source follows exactly that route for arbitrary N, and the geometric lemma supplies 2d. These are precisely the two tools the item's original proof invokes. Their off-unit uses remain declared in split_report.tool_uses; no maintainer-owned tool field is edited. There is no compact-support projection substituted for Rf_* and no assumption that the residue module is perfect.

For delivery-errors B and D: no new unsplit node, duplicate, parent-clause child or Mathlib leaf is introduced. The item introduces its objects and preserves import flags and blueprint provenance. All eleven historical tool/query pairs are present in searches.jsonl; none was rerun or newly claimed in this repair. Invalid identifier and scoped searches remain inconclusive, and the failed LeanSearch service remains unavailable. No search was invented.

For C: I checked that the five (step,node) citation entries equal the step uses exactly and each quotation is a literal substring of the CURRENT cited statement; proof_deps is exactly their union. Neither step borrows a proof construction from a cited node. No unused dependency is inserted to satisfy a unit check.

For E: K=0 and an empty source give zero output; an empty target forces the source empty. For d=0 the identity of Spec k preserves a finite free module's singleton interval. Negative endpoints and a=b require no changed hypotheses. For a>b the universal tensor test with A_X makes K zero; no ordered flat-model equivalence is needed. The nonproper map G_m to Spec k remains allowed. At n=1 and n>1 the argument uses the same general theorem; it never requires the residue field over Z/ell^2 to have finite projective dimension. No statement dispute or weakening was needed.

## Remaining maintenance note

The attempted repair exposed a pre-existing unit reachability finding (`sk-thm-sf-direct-image-tor-amplitude` cites `sk-prop-sf-finiteness`, while the latter's realization is empty). `coord/dag-sync.md` reserves that authoritative unit metadata repair to maintenance. I did not edit the unit, another node, any tool, the shared project or the launcher; the delivery now contains only this item's node and report.

## Dry run

Command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NK cor-sf-direct-image-ctf-nonproper --no-push`.

After removing the out-of-scope unit file, the required dry run completed with exit status 0 and printed `OK (not pushed) deliver/NK/cor-sf-direct-image-ctf-nonproper ...: preflight passed`. The complete output is in `final-final-dryrun.log`; no delivery was pushed.


## Second reading by NK

- Item statement: checked hypothesis by hypothesis against archived master `sec-six-functors/sk-thm-sf-direct-image-tor-amplitude/cor-sf-direct-image-ctf-nonproper.md`, order 2191, and the own-unit `_section.md`, order 2190; PASS. The coefficient quotient, algebraically closed ground field, finite type, separation, dimension bound, small-etale category, arbitrary integer endpoints, bounded constructibility and exact output interval all agree. Expanded definitions do not add properness or change coefficient categories.
- Step 1: opened the complete current statements and archived sources of `lem-sf-etale-direct-image-vanishing` (1790) and `def-sf-uniform-direct-image-vanishing` (1788); PASS. The final global-stage clause applies directly with the present separated f and gives vanishing for every module sheaf and every r>2d. Nonnegativity of 2d is elementary; the geometric application is correctly non-elementary.
- Step 2: opened the complete current statements and archived sources of `thm-sf-direct-image-tor-amplitude` (2066), `lem-sf-flat-model` (1831), and `def-kun-tor-amplitude` (1686); PASS. Every hypothesis of the general theorem is supplied, N=2d, and its statement supplies both conclusions. The flat-model citation identifies its explicit small-etale tensor predicate only; no flat-model existence assertion with a<=b is applied to an unordered interval, and no proof-only construction is borrowed.
- New nodes: none; PASS B1-B7 and D1-D2 vacuously. No elementary fact, duplicate, parent clause, or missed leaf has been made a new node. I searched the whole blueprint for `direct image` and the two relevant DAG chapters for Tor/direct-image/UDV vocabulary; opened the pro-etale and etale-origin corollaries and `lem-coef-finite-direct-image`. Their domains or conclusions differ; the existing general-N theorem is the correct reusable tool.
- Definitions: opened all fifteen distinct immediate dependency statements; PASS. Checked the finite-type definition against Stacks `morphisms.tex`, `definition-finite-type` (01T1), separatedness against `schemes.tex`, `definition-separated` (01KK), dimension against `topology.tex`, `definition-Krull` (0055), and constructibility against `etale-cohomology.tex`, `definition-finite-locally-constant` (03RU) and `lemma-constructible-quasi-compact-quasi-separated` (095E). Ordinary constant-ring module sheaves and their derived direct image are explicitly supported by the cited definitions.
- Edge cases: PASS for K=0, empty X (dimension minus infinity), empty Y (forcing X empty), d=0 and the identity of Spec k, negative endpoints, a=b, and n=1. For a>b, testing the input Tor predicate with A_X makes K zero, so its direct image satisfies the asserted interval. For n>1 no perfectness of the residue module is assumed. The nonproper map G_m to Spec k with constant free coefficients has cohomology in degrees 0 and 1, within [0,2]. The source excludes n=0, and the split retains that exclusion.
- Citations and graph: PASS for the delivery. Independently verified all five verbatim quotations against current statements, exact equality of citation pairs with step uses, and equality of proof_deps with their union. No path through existing dependency records returns to this item. A full transitive read-only scan also encountered pre-existing missing ids, listed below; no immediate delivery dependency is missing.
- Attachment check: opened read-only slopmaster2 `SixFunctors/Etale/Derived/Stability/DirectImage.lean` lines 60-165 after name and concept searches; PASS for retaining a split. The numerical Tor theorem contains sorry; the proved finite-coefficient constructibility theorem covers only the first conclusion, and finite-Tor stability calls the numerical theorem and forgets the specified endpoints. No finished exact attachment was found. Upstream master is reference material only.
- Unit route: PASS mathematically against the complete archived unit and general-N theorem proofs. The existing general theorem follows the flat-model, truncation spectral sequence, constructibility, ordinary direct-image projection and residue-test route. Retain both declared tool uses for maintainer judgment. The missing own-unit realization remains the explicit maintainer metadata issue already reported above; no out-of-scope unit file is included.

Changes made: appended this independent second-reading section, with one verdict for each proof step and an explicit no-new-node verdict, and updated the item's split-report summary to identify this review. No mathematical repair was needed; the statement, two proof steps, five citations and historical search records remain as reviewed. The first worker's sections, including `## Review by NK`, are preserved.

Additional maintenance finding from the transitive dependency scan (outside this item's writable scope): existing reachable records refer to missing ids `0`, `def-pc-quasi-coherent-sheaf`, `def-pc-standard-flat-counit-presentation-on-open`, `def-sc-module-cup-derived-class-comparison-data`, `def-weil-pbc-etale-abelian-sheaves`, `def-weil-pbc-etale-morphism`, `def-weil-pbc-ideal-module-product-stalk`, `def-weil-pbc-regular-scheme`, `lem-pc-affine-derived-pullback-tensor-qcoh`, `lem-sc-supported-qcoh-triangulated`, and `lem-weil-pbc-category-colimit`. This split introduces none of these references; maintenance should repair their owning records.

Second-reader dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py NK cor-sf-direct-image-ctf-nonproper --no-push` exited 0 and printed `OK (not pushed) deliver/NK/cor-sf-direct-image-ctf-nonproper at dcedbf93ae: preflight passed`. The normal delivery command is the final authorized step.
