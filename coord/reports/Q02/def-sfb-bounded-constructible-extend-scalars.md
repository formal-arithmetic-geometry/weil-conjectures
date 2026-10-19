# Stage-1 report: def-sfb-bounded-constructible-extend-scalars

## Files written

- `dag/nodes/sec-proetale-coefficients/def-sfb-bounded-constructible-extend-scalars.json`: existing definition node, corrected and marked split; no new nodes and no Mathlib leaves.
- `citations.json`: empty because this is a definition node with no proof-step list.
- `report.md`: this report.

## Attachments

No attachment: neither `AlgebraicGeometry.ProEtale.boundedConstructibleExtendScalars` nor `AlgebraicGeometry.ProEtale.boundedConstructibleExtendScalarsCompatibility` occurs in the read-only slopmaster2 `WeilConjectures/` source. The archived upstream source has these names only as sorry declarations, so it is not evidence of completion.

## WANTED

None.

## What was wrong or incomplete

The imported statement followed blueprint node 1649 but left `\ell`, `E`, `\cO_{E,X}`, `E_X`, and `\varphi` implicit after saying only “for a scheme $X$”. It also cited only the preservation lemma although its meaning uses the coefficient morphism, derived extension-of-scalars definition, and bounded-constructible subcategories. I made the prime, finite extension, coefficient morphism, ambient derived categories, and all four existing statement dependencies explicit. The two blueprint clauses remain unchanged in content: restriction of $L(\operatorname{Ext}_\varphi)$ and its canonical inclusion compatibility. No smaller auxiliary node is warranted; the compatibility is the canonical lift isomorphism attached to the full-subcategory restriction.

## What could not be finished

Nothing. No Lean files were written and no compiler, Lake, or build tool was run.

## Review by Q02

I read the current item source `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-sfb-rationalization-comparison/def-sfb-bounded-constructible-extend-scalars.md`, its parent unit record `dag/units/sk-thm-sfb-rationalization-comparison.json`, and the chapter record. I compared the two defining clauses with the archived upstream source `CategoryTheory/ModuleObjects/EllAdicRationalization.lean` (lines 127–146 in `/home/ubuntu/weil-newtargets-master`) and verified that the corresponding slopmaster2 source contains no declarations. I opened each cited existing node: `def-sfb-integers-to-subfield` supplies $\varphi:\cO_{E,X}\to E_X$; `sk-def-sfb-bounded-constructible` supplies the two full subcategories; `sk-def-sfb-derived-extension-of-scalars` supplies $L(\operatorname{Ext}_\varphi)$; and `lem-sfb-extend-scalars-bounded-constructible` states preservation of bounded constructibility. Since this node is a definition, it has no proof steps and therefore no node citations to quote; `citations.json` is consequently empty. I checked the edge case that the construction is meaningful only after specifying a prime and finite coefficient extension, which is why those hypotheses were added. I searched the whole blueprint and DAG for duplicate statements and found none. The Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch, each with a second phrasing) returned only generic scalar-extension or derived-category APIs and no project-specific declaration; all eight exact queries and their results are recorded in `mathlib_searches`.


## Second reading by Q02

- Item statement, coefficient hypotheses: checked current main-20261015 node 1649 and parent unit step 2 against archived upstream `WeilConjectures/CategoryTheory/ModuleObjects/EllAdicRationalization.lean:20–38,89,118–142`; PASS. The prime, finite subextension inside the algebraic closure, arbitrary scheme, two full subcategories and direction of the compatibility isomorphism agree. No Noetherian or invertibility-on-X hypothesis is required here.
- Defining clause 1 (restriction): opened `def-sfb-integers-to-subfield`, `sk-def-sfb-bounded-constructible`, `sk-def-sfb-derived-extension-of-scalars` and `lem-sfb-extend-scalars-bounded-constructible`; PASS. Their statements give exactly the coefficient morphism, ambient categories, derived functor and objectwise preservation used. Now the statement explicitly sends K to T(K) with the preservation witness and u to T(u); identity/composition laws are those of T. No proof steps are required for this definition (standing stage-1 brief §2).
- Defining clause 2 (compatibility): checked upstream lines 138–142 and Mathlib `CategoryTheory/ObjectProperty/FullSubcategory.lean:153–171`; PASS. Both composites have the same objects T(K) and maps T(u); the specified components are identities, whose naturality equation is T(u) = T(u), and their inverses are identities. This is the elementary full-subcategory construction, so no auxiliary lemma is created.
- Edge cases: zero complex maps to zero by derived tensor; its compatibility component is the identity. For X empty both module categories are zero categories and the same construction applies. For X the spectrum of a field and E = Q_l, no extra geometric assumption enters. A complex in degree 0 or 1 uses the same objectwise preservation statement; no numerical bound, rank, or stratum is added. PASS.
- New nodes and Mathlib leaves: none; B1–B7 and per-new-node checks are vacuous. Repeated whole-blueprint search `blueprint_refs.py search 'extension of scalars'` and DAG keyword searches; opened `pur713-def-rationalization`, which defines the ambient unbounded functor rather than its bounded-constructible restriction. The existing preservation lemma is the prerequisite, not a duplicate of the defined functor. No new node is needed.
- Independent Mathlib searches: ran a full-subcategory phrasing in LeanFinder, the exact generic `CategoryTheory.ObjectProperty.liftCompιIso` query in Loogle, and grep `def lift|liftCompιIso` in `CategoryTheory/ObjectProperty`. Read the hits at lines 159–165. Generic `lift` requires precisely the coefficient functor and preservation witness supplied by the existing project nodes; it does not remove those dependencies or supply a finished project declaration. The two earlier Loogle unknown-identifier responses are invalid queries, not absence evidence; their verdicts were repaired.
- Lean source audit: repeated name/concept searches in read-only slopmaster2; no boundedConstructibleExtendScalars declarations occur there. Correction to the first worker's Attachments paragraph: archived master lines 129–142 are explicit definitions, not sorry declarations; they depend on the sorried preservation lemma at lines 118–124 (and inherited framework). This still provides no finished slopmaster2 attachment. The first worker's sections are preserved above.
- Citation/form audit: all four statement dependency nodes were opened; each defines or states the notion used. Added the missing inline derived-extension citation. The definition has no proof-step citations, so citations.json remains the correct empty list. TeX is encoded once; source remains the exact current blueprint path and node. No Stacks tag or SGA source is involved.

Changes: added the inline derived-extension reference and explicit object, morphism and identity-component construction; corrected invalid-query verdicts and recorded three independently run searches; corrected the upstream-sorry description in this second reading. No statement hypothesis or conclusion changed in this second reading; no new nodes or Mathlib leaves.

Delivery command note: the brief's trailing `.` is rejected by the installed deliver.py argument parser (usage only, no work performed). Its documented equivalent is used: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q02 def-sfb-bounded-constructible-extend-scalars --no-push`, then the same command without `--no-push`.

Dry run: documented command returned `OK (not pushed)` at `327669ef52`; preflight passed, including delivery shape, split review and global DAG cycle checks.
