# Q44 finite-proper-localizing pipeline repair

Recorded 2026-10-21T07:24:07Z. This is an item-record repair, not a new mathematical delivery.

## Cause

The human's bulk re-split note measured the old proof at 15,969 characters.
Commit d17261b201 reopened the note after Q60's reviewed split 3c3f045a56
landed at 2026-10-21T03:25:59Z with four direct new helpers. The server
preflight computes max(1, ceil(15969/3000) - 1) = 5 and counts only new
directly cited helpers. It therefore refuses the repaired package with
zero added helpers plus four previously landed direct helpers.

The independent review NT-cc-Q60-90c338b01 recorded a complete mapping of
all 17 old steps to the five-step, 2,609-character assembly, the four
helpers, and the existing sk-thm-properbasechange. The later independent
Q44 return explicitly found that no genuine fifth item-level argument
remains. The rejected bounded-below/total-exchange node was introduced
only to satisfy that count. Restoring step 4 and dropping it gives the
mathematics already present on sheaf-dag, so repeated re-delivery cannot
resolve this contradictory record.

The retained sandbox agrees with the live statement, statement dependencies,
five proof steps, proof dependencies and eleven tool uses; its split_report
is the only differing item field. Repeated worker logs show the sole refusal
is the five-helper count. This is not a provider failure.

## Existing completed work

The accepted Q60 split cites:

- lem-sfb-finite-proper-geometric-cd-bound
- lem-sfb-finite-classical-localizing
- lem-sfb-finite-proper-classical-truncation
- lem-sfb-finite-proper-classical-coproducts

All four are now split and reviewed. The truncation helper cites the split,
reviewed lem-sfb-finite-proper-classical-neighborhood-vanishing, landed in
f0ac738014. The coproduct helper has also been decomposed further. Reusing
the existing sk-thm-properbasechange for old step 14 is required by both
independent reviews; creating an artificial fifth direct helper repeats C5/D1.

## Record correction

Resolved coord/repair-notes/det-ctf-finite-proper-localizing.json with the accepted split and this
evidence, preserving its original note and reason as history. Removed only
this item's open return from coord/returns/Q44.md, preserving its full text
below. Removed only Q44's stale claim for this item. Appended a supersession
entry to coord/deliveries.log. Archived the rejected branch at
refs/superseded/Q44/det-ctf-finite-proper-localizing/4980cb54a197d3f7228edad0612e68a10f3a5fda and deleted deliver/Q44/det-ctf-finite-proper-localizing only if it still pointed to
4980cb54a197d3f7228edad0612e68a10f3a5fda.

Every existing changed file has an adjacent .maint-Q44-finite-proper-localizing-20261021.bak copy. The rejected
Git ref is additionally saved in coord/maintenance/Q44-det-ctf-finite-proper-localizing-20261021.md.maint-Q44-finite-proper-localizing-20261021.ref.bak.

The live node SHA-256 before this repair is
adee1861874e7785b645d2f8ca9e240274559b7fefed5ff6f2ac1a2bc6a2953d.
No DAG node, Lean file, target, launcher code, review service, landing tool,
preflight rule, concurrency setting, or worker process was changed.

## Next worker

This item has completed stage 1; do not dispatch or re-deliver it merely to
satisfy the old count. Use the accepted Q60 split and continue genuine open
helper/module tasks through the normal queue. Do not restore
lem-sfb-proetale-bounded-below-total-exchange or replace step 4's correct
unit--square--counit sentence. No item mathematics or Lean compilation was
needed for this record repair.

## Archived independent return (verbatim)

## det-ctf-finite-proper-localizing (2026-10-21 06:37 UTC, branch head 4980cb54a1)

C5/D1 (unneeded new node) and a misstated citation in step 4. The statement and stmt_deps are byte-identical to the side-live item, which was merged at 03:25 from the Q60 4-node re-split. The only change is in step 4: the correct sentence 'This theorem's exchange is the same unit--square--counit mate' is replaced by a citation of the new node lem-sfb-proetale-bounded-below-total-exchange, which identifies a bounded-below mate β^+ (built from R^+u_* and the D^+ adjunction) with the total ambient mate β^∞. The node is true: the total adjunction restricts along j with the c comparisons. The item never needs it. sk-thm-properbasechange is already a statement about the ambient exchange. Its stmt_deps are def-weil-pbc-ambient-ringed-exchange, def-weil-pbc-proetale-operations (total K-injective Ru_*) and def-weil-pbc-bounded-derived-subcategories, with no R^+. Its proof step 5 concludes via naturality of the ambient exchange. Its Lean isIso_classicalProEtaleExchange_of_isProper is the proEtaleAmbientRingedExchange applied to IsGE K inside the total proEtaleDerivedCategory. The report says the node carries old step 14. It does not: in the Q117 17-step proof, old step 14's identification is the étale→pro-étale transport (lem-weil-pbc-transport-identifies-exchange) plus the classical equivalence and étale PBC, i.e. exactly the proof of sk-thm-properbasechange, with no D^+-vs-D comparison. The fifth node therefore carries no argument of the old proof and only pads the reopen count. A FIX that drops it and restores the sentence is a no-op against the merged item. Steps 1–3 and 5 and the 11 tool_uses are unchanged and still correct (re-read). No SGA citation. Maintainer note: every argument of the 15,969-character proof is already spread over the 4 merged helpers (the truncation helper is now split further: neighborhood-vanishing) and the reviewed sk-thm-properbasechange. A genuine fifth item-level node does not exist. Please waive the ≥5 count for this item or close the reopen rather than ask for another re-delivery.

