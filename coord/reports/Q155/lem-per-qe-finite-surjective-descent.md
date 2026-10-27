# Q155 stage-1 delivery: lem-per-qe-finite-surjective-descent

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-qe-finite-surjective-descent.json: item, statement retained, five proof steps, status split.
- dag/nodes/sec-deligne-laumon-a1/lem-per-regular-map-finite-surjective-detection.json: new statement-only lemma, Greco Proposition 1.2 for geometric regularity; Mathlib verdict no match, status unsplit.
- citations.json: verbatim statement excerpts for every proof-step dependency (the complete statement is used as the excerpt).
- report.md, searches.jsonl and research/search0.txt through research/search9.txt: report and actual search evidence.

There is one new node and zero new Mathlib leaves. No unit realization fields require changing: this item is an auxiliary input, not the statement of its unit. No Lean file was written or compiled.

## Attachments

None. Searched lean/WeilConjectures/ for the exact blueprint tag, quasi-excellence and Greco, and inspected the regular-map/G-ring source. The only quasi-excellence occurrence there is background prose in Derived/Stability.lean. No declaration states this item. Sheaf's existing quasi-excellence definitions and other theorems do not provide an upstream attachment. The imported item has no finished Lean audit.

## Literature wanted

WANTED: Silvio Greco, Two theorems on excellent rings, Nagoya Math. J. 60 (1976), 139–149, DOI 10.1017/S0027763000017190, Propositions 1.2–1.3, Corollary 2.4 and Theorem 3.1, for lem-per-qe-finite-surjective-descent and lem-per-regular-map-finite-surjective-detection.

WANTED: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber), Theorem 5.1 Step 1 (1-3), printed p.8, https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf, for lem-per-qe-finite-surjective-descent (the inherited invocation).

Neither document is present under this clone's literature/. I did not download files. I read the primary Kurano–Shimomoto PDF online and Greco's publisher PDF as indexed at https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf after the publisher PDF endpoint timed out. The latter reproduces the journal's printed pages and DOI. The assembly proof is marked agent in accordance with the missing-local-document rule; its local supporting sources are the Stacks .tex files identified below. The new lemma identifies Greco's proposition precisely and remains statement-only.

## Findings and corrections

The imported statement is correct. Greco Theorem 3.1(i) has precisely the finite and surjective-on-prime-spectra hypotheses; no injectivity, flatness of A to B, characteristic-zero assumption or universal catenarity is needed. Universal catenarity belongs only to the separate assertion about excellence. The inherited source invokes this result but supplies no proof; I supplied the finite-completion proof and the J-2 proof rather than creating another node restating finite descent of quasi-excellence.

The current blueprint is literature/blueprint/latest (main-20261024). I read the current chapter/unit route and the ancestor lem-per-artin-gabber-affine-curve proof. The item's existing provenance chain records the regular-model/purity completion subargument that needs this descent. This delivery fills that auxiliary input and does not change the unit's perverse/Fourier argument or chapter. There is no released repair note for this item. I retained all original metadata and searches, adding this group's actual searches.

Before writing the new lemma I searched all DAG nodes by quasi-excellence, G-rings, J-2, Greco, finite surjectivity, regular maps and the relevant Stacks tags. I ran blueprint_refs.py ancestor for the item and search for quasi-excellent, G-ring, J-2, regular ring map, P-homomorphism, finite.*regular and finite surjective. No blueprint node states the new lemma or the item. Existing nodes supplied the completion decomposition and all the regular-locus inputs. I read the statements of all cited nodes, not their proofs as substitute interfaces. The new node has the exact ancestor and via chain and a specific from.place; same_as is empty.

The new lemma's Mathlib searches are search0–search4, and the item's searches are search5–search9, each actually run through msearch.py and retained with its output. All services returned results. Search0 and search3 returned regular-sequence base change and flat-base-change results; these concern a different property from regular ring homomorphisms. Search4 returned residue-field/fibre finiteness. Search5 and search8 returned quasi-finite algebras and Noetherian finite-type algebras. Search9 returned descent frameworks whose type requires the missing descent property as an input. I read Mathlib/RingTheory/Regular/Flat.lean, RingHom/Flat.lean, QuasiFinite/Basic.lean and AlgebraicGeometry/Morphisms/Descent.lean to rule out those candidates. In particular the semantic descriptions of quasi-finite results sometimes incorrectly gloss quasi-finite as module finite; the actual source defines finite-dimensional fibres, not quasi-excellence. Loogle found no GeometricallyRegular or Excellent declaration; the source grep found no geometric-regularity notion. No candidate states the new lemma or specializes to it in one line.

## Unfinished work

No part of this one-level split remains unfinished. The new generic regular-map lemma is intentionally unsplit for a later worker. Bibliographic integration of the two missing papers is requested above. Formalization and proof compilation are outside this assignment.

## Not duplicates

lem-per-regular-map-finite-surjective-detection vs lem-weil-pbc-regular-base-change: the existing node proves ascent along finite-type base change from a regular map; the new node detects regularity of an already flat map from regularity after a finite spectral cover, which need not be flat.

lem-per-regular-map-finite-surjective-detection vs lem-weil-pbc-regular-permanence: the existing node descends regularity along a faithfully flat map on the target ring of a compositional tower; the new lemma changes the source ring by a potentially nonflat finite cover. Its hypothesis is regularity of the tensor base change, not of a composite.

lem-per-regular-map-finite-surjective-detection vs lem-per-qe-finite-surjective-descent: the new lemma concerns a supplied flat homomorphism and its individual geometric fibres; it says nothing about local completion maps or openness of regular loci. The item's proof establishes these separately using the completion product and the domain descent argument.

## Review by Q155

I checked delivery-errors B–E against the files and their sources. The new statement introduces R, Lambda, R-prime, both ring maps and the tensor-product map, with all Noetherian, flatness, module-finiteness and spectral-surjectivity hypotheses explicit. Its notions are covered by its five statement dependencies. It has no proof, proof sketch or proof dependency. Its source is Greco Proposition 1.2 on printed p.140 with P geometrically regular, rather than Theorem 3.1 relabelled. This more general detection result is a non-elementary ingredient; the rest of the item's work remains in the item.

For step 1 I read def-exc-excellent-ring and Stacks more-algebra.tex definition-excellent (07QT). Its statement gives both G-ring and J-2. I checked algebra.tex Noetherian-permanence (00FN), completion-Noetherian-Noetherian (0316) and completion-faithfully-flat (00MC) against the corresponding four cited nodes. They give exactly the localization/completion Noetherianity, finite-type algebra Noetherianity and flat completion map required. Module generators remain generators after tensoring by the displayed elementary expansion; hence C and D meet all subsequent Noetherian hypotheses. No flatness of the original finite map is asserted.

For step 2 I read morphisms.tex base-change-surjective (01S1), schemes.tex fibre-product-affine-schemes/fibre-product-affines (01I4/01JQ), algebra.tex completion-finite-extension (07N9), and more-algebra.tex regular-local (07C0). The respective nodes explicitly give arbitrary base-change surjectivity, the affine tensor model with projections, the finite product with compatibility of completion maps, and the localization criterion for regular maps. I checked that the product factors are completed B_q, with q lying over p, not completions of B localized only at p. The product localizations select one factor via orthogonal idempotents; localization then identifies the source with the relevant localization of B_q. This routine identification is written out, not promoted to a node. The definition node def-weil-pbc-g-ring supplies regularity of B_q to its completion at every prime q.

For step 3 the new detection lemma is applied to R to its completion and the finite covering algebra C, not to A to B as a flat map. The flatness was proved in step 1, and finiteness and spectrum surjectivity in steps 1–2. I wrote both directions of the tensor associativity identification, which preserves the structural map. The resulting regularity at each p is exactly the universal quantifier in def-weil-pbc-g-ring. Greco Proposition 1.3 uses this same completion/base-change argument.

For step 4 I checked Greco Corollary 2.4 on p.142 and local Stacks J-0-goes-down (07PA). The quoted node lem-exc-j0-finite-type-domain-descent requires an injective finite-type map of domains, not merely a dominant arbitrary ring map. Choosing a prime e above t makes T/t to E/e injective and both rings domains. The same tensor generator calculation supplies finite type on both sides. B's J-2 condition applies to the quotient F because F is finite type over B. Its generic local ring is a field and is regular by the zero-dimensional definition in def-weil-regular-scheme, so its open regular locus is nonempty. Thus every hypothesis of the cited J-0 descent lemma holds.

For step 5 I read more-algebra.tex intersection-regular-with-closed (07P9) and J-2 (07PC). The former node gives J-1 for T from J-0 of every prime quotient T/t; the latter existing node lem-per-j2-finite-algebra-criterion gives J-2 of A from J-1 for every finite A-algebra T. Neither node is confused with its definition or silently used in the opposite direction. Finally def-exc-excellent-ring joins the established predicates. citations.json contains a verbatim statement for each of these applications.

I tested the statement and new lemma on identity maps, a field with a finite field extension, diagonal maps into a finite product, nilpotent quotients and zero rings. Noninjective finite covers are allowed. A to the zero ring satisfies spectral surjectivity only when A has empty spectrum, so there is no spurious deduction for a nonzero A. For A zero the quantifiers over primes and the J-2 test have the correct vacuous meaning. The formal-fibre argument does not replace module finiteness with finite type; the J-2 argument uses only the weaker finiteness it actually needs. No source error or statement dispute was found. Every proof step is below 2000 characters; none hides an uncited general theorem. Off-unit commutative-algebra tools are declared in split_report.tool_uses with their purpose.

Validation: server checks and delivery preflight are recorded after completion below.

Local evidence check: both JSON node files parse, all 21 step/dependency pairs have verbatim quotes, proof_deps equals the union of uses, and all five searches recorded for the new node occur in searches.jsonl. The five proof steps have 718, 1240, 653, 1275 and 383 characters.

## Earlier validation attempt (preserved history)

The earlier worker was blocked by validation infrastructure, not by a reported split diagnostic. The required `deliver.py Q155 lem-per-qe-finite-surjective-descent --no-push` invocation was admitted to server preflight after 3453 seconds in the queue. Its SSH/server preflight timed out after 720 seconds; the launcher then automatically invoked its nocheckout fallback, which also timed out after 600 seconds. The invocation exited 1 without OK or any preflight/check_dag/review_split findings. The separate earlier srvcheck review_split invocation likewise timed out on the server after 720 seconds and in the automatic fallback after 600 seconds, exiting 1. Both tool sessions have exited. No push was attempted. The prepared split, source/search evidence and citations remain in this sandbox for a later retry; no launcher tool was edited or bypassed.

## Resumed validation, 2026-10-24

Retained both node files unchanged after comparing the live item and current blueprint with the preserved work. Re-read the five proof steps and every cited statement, the relevant local Stacks completion/local-regularity/J-0/J-2 lemmas, and the preserved output of all ten searches. The existing project Lean still has no declaration stating this item. Rechecked all 21 citation pairs verbatim against current statements, the proof-dependency union, and the five new-node search records against searches.jsonl. Re-read Greco Proposition 1.2 and the finite-completion proof, and the Kurano–Shimomoto invocation online. No new mathematical defect or changed hypothesis was found, and no repeated Mathlib searches were needed.

The required dry run completed successfully: `OK (not pushed) deliver/Q155/lem-per-qe-finite-surjective-descent at b8d10105626: preflight passed`. The former server timeout did not recur. Updating this report is the only change made in the resumed attempt; a final dry run and direct delivery follow this update.
