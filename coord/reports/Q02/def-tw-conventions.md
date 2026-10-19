# Stage-1 report: def-tw-conventions

## Files written

- `dag/nodes/sec-six-functors/def-tw-conventions.json`: definition, no new auxiliary nodes, Mathlib search verdict no match.
- `citations.json`: empty because the item is a definition with no proof steps.
- `report.md`.

## Attachments

None. I searched both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `/home/ubuntu/weil-newtargets-master/WeilConjectures` for the item id, the blueprint tag, and the weight/cohomology terminology; there is no exact finished declaration to attach.

## WANTED

None.

## Source error

The imported statement ended with the ill-formed phrase “the compactly supported cohomology of 02.” The source markdown is absent from the shared checkout but I located and read the complete archived original at `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-six-functors/sk-rem-sf-pf-done/def-tw-conventions.md`; it has exactly this unresolved phrase. I checked the corresponding existing conventions: `def-weil-pbc-qbar-category` defines the geometric coefficient category, `def-weil-pbc-scheme-conventions` supplies the separated finite-type scheme convention, and `def-weil-ordinary-compact-cohomology` defines the notation `H_c^i(Y,\Lambda)`. The intended meaning is therefore compactly supported cohomology of the geometric base change with constant `\overline{\mathbf Q}_\ell` coefficients. The imported text also used `\overline{\mathbf Q}_\ell` without fixing `\ell` or defining `X_{\overline k}`; I repaired both omissions explicitly. This is a statement correction required by the brief's statement-dispute rule, not a weakening of the convention.

## Review by Q02

I read the item node, its chapter `sec-six-functors.json`, and its unit `sk-rem-sf-pf-done.json`. I opened the complete statements of all four dependencies. `def-weil-pbc-qbar-category` supplies the `\overline{\mathbf Q}_\ell` coefficient derived category on a noetherian scheme with `\ell` invertible; `def-weil-pbc-scheme-conventions` supplies the meaning of separated and finite type; `def-weil-finite-field-fiber` supplies the finite-field, coefficient-prime and geometric-base-change data (with its letters renamed explicitly); and `def-weil-ordinary-compact-cohomology` supplies the compact-support notation as the cohomology of the compact-support direct image of the constant coefficient object. These statements say exactly what the repaired definition takes from them. Since the item has no proof, there are no proof steps or node quotes, and `citations.json` is correctly empty.

I checked edge cases in the wording: fixing `\ell\neq p` makes the coefficient category applicable, and defining `X_{\overline k}` removes the ambiguity between `X` over `k` and its geometric base change. The Mathlib searches were run with LeanFinder, Loogle (twice with two phrasings), and Mathlib grep; they found only unrelated Witt-vector/condensed infrastructure and the narrower `Scheme.EllAdicCohomology`, which lacks compact support and the requested coefficient category. No new node was justified. The node is marked `split`, retains the two original dependencies, adds the existing compact-support definition, and records the repaired blueprint paragraph.

## What remains

Nothing unfinished in this split; the second reader should verify the source-error repair before delivery. This worker does not push.

## STATEMENT-DISPUTED

The original statement does not bind the coefficient prime or exclude $\ell=p$, although its cited coefficient category requires $\ell$ invertible on the scheme. For the explicit case $X=\operatorname{Spec}\mathbf F_p$ and $\ell=p$, multiplication by $\ell$ is zero in the residue field, so that cited category does not apply. This is a type/domain failure, not a failure of a purported theorem. I repaired it by making explicit the existing global convention of `def-weil-finite-field-fiber` (its final paragraphs fix a prime $\ell\neq p$); the finite field and geometric base change are explicitly linked to that same node. The statement now introduces $p,r,\ell$, both chosen algebraic closures, the base-change scheme and every integer degree. The item is not the unit's key theorem, so no unit realization fields change.

## Final source and search check

I read `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:59–83`: `ellAdicSheaf` uses continuous maps to $\mathbf Z_\ell$, and `EllAdicCohomology` at line 75 takes its ordinary sheaf cohomology in nonnegative degrees. It has neither the $\overline{\mathbf Q}_\ell$ coefficient category nor compact supports, so it is not an exact match or a one-line specialization. The two initial Loogle queries had unknown identifiers; these are recorded as invalid queries, and I reran valid quoted-name searches for `"EllAdicCohomology"` and `"compactlySupported"`, inspecting the ordinary integral-cohomology and compactly supported continuous-function hits. LeanSearch returned Internal Server Error and is recorded as unavailable. Every query in the node now copies the literal query text from `searches.jsonl`, including the grep pattern without an invented directory suffix.

Blueprint searches for `Base conventions` and `compactly supported cohomology` found the item itself, the reused cohomology definition, and unrelated cohomology results; no other node states this complete convention, so `same_as=[]`. No new nodes were created, so the B1–B9 new-node and duplicate-pair requirements have no new-node cases. C1–C8 and D1–D5 have no proof-step cases: this is purely a definition referencing existing ingredients, and it carries no hidden theorem assertion. E1–E6 were checked against the coefficient-prime/domain failure above, including the empty scheme (the notation remains defined and makes no nonvanishing assertion) and $X=\operatorname{Spec}k$ (the geometric base change is the geometric point). No algebraic-closure coefficient comparison with the archived master's condensed module category is asserted.

## Dry run

The first captured attempt timed out after 600 seconds during concurrent launcher contention. The second captured attempt completed and printed `OK (not pushed) deliver/Q02/def-tw-conventions at 4f91b9e491: preflight passed`. After the source-location correction, exact search-log normalization and explicit finite-field dependency, the final dry run is recorded in `dry-run-final.log`.


## Earlier second reading (a previous round; superseded)

- Item `def-tw-conventions`: compared every clause with the complete archived `sec-six-functors/sk-rem-sf-pf-done/def-tw-conventions.md` (order 2104), its unit and chapter; PASS. This source is a blueprint definition, not a Stacks-tagged statement. The prime power, finite field, algebraic closure, separated finite-type scheme, geometric coefficient category and compact-support notation are preserved. The archive really ends in the unresolved text “cohomology of 02”.
- Finite-field clause / `def-weil-finite-field-fiber`: read the current statement and its archived order-411 definition; PASS. Renaming `(a,k_0,k)` to `(r,k,\overline k)` gives exactly the fields in this item. The archive itself fixes the global coefficient convention `\ell\ne p`, so making that condition explicit restores an inherited assumption. At `X=Spec F_p`, `\ell=p` is outside the cited coefficient-category domain, confirming the recorded STATEMENT-DISPUTED diagnosis.
- Scheme clause / `def-weil-pbc-scheme-conventions`: read the full statement; PASS. It explicitly supplies separated and finite-type morphisms, schemes and fibre products; there is no inference of smoothness, properness or geometric connectedness. Base change of the given finite-type scheme is finite type over `\overline k`, hence Noetherian and finite-dimensional, and `\ell\ne p` gives invertibility, as required for the cited category. These are applicability checks, not additional hypotheses imposed on `X`.
- Coefficient-category clause / `def-weil-pbc-qbar-category`: read the complete current statement and archived order-1311 definition; PASS. Its category is the finite-stage pair category, without adjoining a Karoubi envelope. This item names that category and does not substitute a discrete constant-sheaf model or assert a new comparison theorem.
- Cohomology clause / `def-weil-ordinary-compact-cohomology`: read its complete statement and archived order-1510 definition; PASS. Substitute `Y=X_{\overline k}` and `\Lambda=\overline{\mathbf Q}_\ell` in its displayed abbreviation. Its `\Lambda_Y` is the coefficient object obtained by completion and scalar extension, precisely the object named here. I also read `def-weil-algebraically-closed-coefficients`, which explicitly identifies its coefficient category with the same finite-stage pair construction, and `def-weil-finite-coefficient-point`, which supplies evaluation over the algebraically closed base.
- Proof steps: NONE; verified `proof=[]`, `proof_deps=[]`, `proof_origin=null`. This is a definition, not an assertion with a proof moved into its dependencies. `citations.json=[]` correctly records no proof-step citations; C1–C4 and E5 have no omitted steps to repair.
- New nodes: NONE; verified that the only sandbox node is the existing item. B1–B7 and the elementary/duplicate/restatement tests have no new-node cases. Whole-blueprint searches `Base conventions` and `compactly supported cohomology` return the item, the reused cohomology definition and unrelated results; no auxiliary node is needed, and `same_as=[]` is correct.
- Small cases: PASS for `X=\varnothing` and `X=Spec k`, whose geometric base changes are respectively empty and `Spec \overline k`; the notation makes no extra nonvanishing assertion. Degrees `i=0,1` and negative `i` are covered by the cited integer-indexed definition. `r=1` gives `F_p`; `r=0` would give a one-element “field” and is correctly excluded by the prime-power convention. No finite-coefficient level `n` is introduced in this item.
- Existing Lean / Mathlib: PASS, no exact whole-item attachment or leaf. Read slopmaster2 `SixFunctors/ProEtale/Derived/LowerShriek.lean:223–252`: `compactlySupportedCohomology` is a general functor for an abelian coefficient category and a compactifiable morphism, not this finite-stage `Qbar_l` convention. Read Mathlib `AlgebraicGeometry/Sites/ElladicCohomology.lean:59–85`: its coefficient sheaf is continuous `Z_l`-valued maps and its cohomology is ordinary and natural-degree-indexed. The independent semantic search for “Derived sections with proper support of the constant l-adic rational sheaf on a variety over an algebraic closure of a finite field” returned local-section algebraic-geometry lemmas, grep `compactSupport|cohomologyWithCompact|EllAdicCohomology` returned those ordinary integral-cohomology declarations, and Loogle `"cohomology"` returned Hom-complex cohomology classes. I inspected the returned types; none states the complete convention.

Changes made in this second reading:

- Added the three independent, actually executed searches to `mathlib_searches`, preserving their exact queries and the actual logged results. They confirm the existing no-match decision.
- Appended this clause-by-clause second reading, including explicit dependency applicability and small-case checks. Preserved `## Review by Q02` and the worker's other sections.
- No mathematical statement, source reference, dependency, proof or citation repair was necessary after independently checking the worker's source-error correction. No new nodes or Mathlib leaves were added.

Second-reader dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q02 def-tw-conventions --no-push` completed successfully with `OK (not pushed) deliver/Q02/def-tw-conventions at b1d85f0165: preflight passed`. No validation failure required a repair.


## Repair rereading by Q02 — 2026-10-16

The reissued return names `eral-admissibility`, cites head `363f9299c1d9502ba465d1b90e9abb8e86743678`, and ends with `--verdict PASS`. It contains no numbered objections about `def-tw-conventions`. Consequently there are no numbered points to repair from that text; applying its discussion of base-change and Tor arguments to this definition would address a different item. I independently reread this item's delivery and made the following concrete clarification rather than merely rebasing it.

I reopened the archived original `sec-six-functors/sk-rem-sf-pf-done/def-tw-conventions.md` (order 2104), the current chapter and unit records, all four current dependency statements, and their four archived markdown originals (orders 1311, 2, 1510, 411). The original still ends in the unresolved words “cohomology of 02”. Its prime-power field, algebraic closure and separated finite-type scheme are preserved. The existing finite-field convention explicitly fixes the coefficient prime away from $p$, and renaming $(a,k_0,k)$ to $(r,k,overline k)$ makes its geometric fiber exactly the one here. The explicit prime condition repairs a domain omission; it imposes no new assumption beyond that global convention.

The coefficient-category statement defines the finite-stage pair category. The cohomology statement expressly defines $(overline{mathbf Q}_ell)_Y$ through its completed integral coefficient object and scalar extension, before abbreviating $H_c^i(Y,overline{mathbf Q}_ell)$ by cohomology of that object. I added one sentence to the item explicitly binding its coefficient object to that construction. This closes the possible ambiguity in the phrase “constant coefficient object”; it does not identify the pair category with the archived master's condensed category. Substitution of $Y=X_{overline k}$ uses the same algebraic closure and prime. The separated finite-type hypothesis is precisely the cohomology convention's scheme hypothesis. Finite type over the algebraically closed field supplies the Noetherian finite-dimensional setting of the pair-category definition; the coefficient prime is invertible because it differs from the field characteristic. No smoothness, properness, or connectedness is assumed.

For the B checks, there are zero new nodes and zero Mathlib leaves, so no unsplit-node proof, duplicate pair, Stacks-tag source, or leaf declaration is claimed. The item is a self-contained TeX definition, retains its blueprint ancestry and all import fields, and explicitly cites every ingredient it uses. Its direct source is an archived blueprint definition, not a Stacks lemma. Whole-blueprint searches for `Base conventions` and `compactly supported cohomology` again found only this convention and distinct cohomology results/definitions. For C and D, there are no proof steps: `proof=[]`, `proof_deps=[]`, `proof_origin=null` and `citations.json=[]`. The added sentence is a reference to an already defined object, not a theorem moved into an auxiliary node. No off-unit proof route is used; the unit's projection-formula remark and chapter route are untouched.

For E, I checked $r=1$, excluded $r=0$, and checked $ell=p$ on $operatorname{Spec}mathbf F_p$ against the invertibility condition. For $X=arnothing$ and $X=operatorname{Spec}k$, the displayed base changes give the empty scheme and $operatorname{Spec}overline k$ respectively. The notation applies in every integer degree and does not assert nonvanishing or finiteness. These remain the same objects and domains as the two coefficient definitions; no transport lemma is silently asserted.

I searched both project source trees and the upstream-name table for the item id and title, with no whole-item declaration found. I also reopened slopmaster2 `SixFunctors/ProEtale/Derived/LowerShriek.lean:223–252`: its general compact-support functor takes an abelian coefficient category and a compactification and does not state this finite-stage coefficient convention. The new logged Mathlib grep `EllAdicCohomology|compactlySupportedCohomology` in `AlgebraicGeometry` returned only `ElladicCohomology.lean:28,75,78,83`; reading lines 59–85 confirms ordinary integral cohomology in natural degrees, not this convention. Previous semantic and Loogle queries remain exactly as logged, including invalid queries and the unavailable LeanSearch service; no unexecuted query was added.

Validation for this repair is the required stage-1 `deliver.py Q02 def-tw-conventions --no-push`; its current output is captured in `dry-run-repair.log`. No Lean file was written, no compiler or Lake command was run, and nothing was pushed. The second reader should use the clarified coefficient-object sentence when checking the statement against the existing cohomology definition.


Repair dry run passed: `OK (not pushed) deliver/Q02/def-tw-conventions at ee1c0b6a64: preflight passed`, captured in `dry-run-repair.log`. The final run after this report addition is captured in `dry-run-repair-final.log`.

Maintenance observation from the broader source-only scan: existing shared dependencies have dangling references (for example `lem-weil-pbc-filtered-colimit-iso-presieve-representation` cites the absent `lem-weil-pbc-category-colimit`) and existing cycles (for example `lem-sp-grothendieck-edge-maps` occurs in a cycle through the CE-resolution comparison lemmas). The scan traverses every dependency even below closed or Mathlib nodes, so this is not a claim that any finished proof is invalid. The cohomology dependency makes some of these existing branches reachable from this item. None of those internal edges was edited here, and no dependency returns to `def-tw-conventions`; the required preflight compares the global baseline and accepted the delivery. I report the shared defects here for maintenance rather than modifying other items or suppressing the observations.

## Second reading by Q02

- Item statement: checked every clause against the archived blueprint definition `def-tw-conventions` (order 2104); the source's unresolved “cohomology of 02” was repaired by the displayed compact-support notation and explicit coefficient object.
- Finite-field data: checked against `def-weil-finite-field-fiber`; renaming the finite-field letters and retaining the global condition $\ell\ne p$ is correct, including the $r=1$ case.
- Scheme hypothesis and base change: checked against `def-weil-pbc-scheme-conventions` and the fibre definition; separated finite type over $k$ and $X_{\overline k}=X\times_k\overline k$ are correctly stated, with no added smoothness or properness.
- Coefficient category: checked against `def-weil-pbc-qbar-category`; the finite-stage $\overline{\mathbf Q}_\ell$ category is referenced without asserting an unproved comparison.
- Compact-support notation: checked against `def-weil-ordinary-compact-cohomology`; substitution $Y=X_{\overline k}$ and $\Lambda=\overline{\mathbf Q}_\ell$ gives exactly the displayed $H_c^i$ abbreviation and scalar-extended coefficient object.
- Proof steps: none (`proof=[]`, `proof_deps=[]`), so there are no uncited facts or elementary-step judgments; `citations.json` is correctly empty.
- New nodes: none; the item is the sole node, so B1–B7, duplicate-node, and Mathlib-leaf checks have no auxiliary cases. Existing-node and Mathlib searches were reviewed in the recorded logs.
- Edge cases: checked $X=\varnothing$, $X=\operatorname{Spec}k$, $r=1$, negative and zero cohomological degrees, and excluded $\ell=p$ on $\operatorname{Spec}\mathbf F_p$; all are handled by the stated domains.

Changes made: added this required second-reader section with clause-by-clause source and dependency checks. No node, statement, dependency, proof, or citation changes were needed beyond the worker's documented repair of the malformed source phrase and missing explicit coefficient-prime/object conventions. The required dry run passes with `deliver.py Q02 def-tw-conventions --no-push`.
