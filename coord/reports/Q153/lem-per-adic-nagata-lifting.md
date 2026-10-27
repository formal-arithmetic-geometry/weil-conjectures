# Stage-1 report: lem-per-adic-nagata-lifting

Group Q153, 2026-10-24. Direct delivery; only the assigned sandbox was written. No Lean was written and no compiler, Lake, local DAG checker or git command was run.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-nagata-lifting.json: item, split, original statement preserved; four-step maximal-bad-prime argument.
- dag/nodes/sec-deligne-laumon-a1/lem-per-japanese-quotients-noetherian-normalization.json: new statement-only lemma, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-noetherian-normalization-finite.json: new statement-only lemma, no Mathlib match.
- citations.json: exact statement quotations for every step/node citation.

Two new nodes, zero Mathlib leaves. The report and search evidence remain in the sandbox. No unit realization fields require changes, since the item is not the unit's key statement.

## Attachments

None. Searches by the exact item id and by Marot in lean/WeilConjectures returned no declaration. The concept search found NagataOfCompleteLocal.isNagataRing_of_complete_local and the existing Japanese-domain and Tate lemmas. The former requires a local ring and completion at its maximal ideal, whereas this item allows arbitrary complete pairs; the Tate lemma requires a normal domain and a prime principal ideal. Neither states the item. The imported statement has no Lean declaration to reconcile.

## Sources and WANTED

WANTED: Jean Marot, Sur les anneaux universellement japonais, Bulletin de la SMF 103 (1975), pp.103-111, DOI 10.24033/bsmf.1795, Lemma 1.2, Proposition 2.1 and Proposition 2.3, for this item and its two new nodes. Read the primary scan online at https://www.numdam.org/item/10.24033/bsmf.1795.pdf, especially printed pp.104-107; no archival copy was found in literature. The brief forbids writing literature, so the request is recorded here. proof_origin.by is agent, as required when the archival document is missing, although the assembly follows that source rather than memory.

I also read the relevant Kurano–Shimomoto Theorem 5.1 Step 1 (1-3), printed p.8, online: it invokes Marot's lifting theorem and does not prove it. Thus a proof consisting only of that invocation would not split this item. The new proof follows the invoked theorem back to Marot's Proposition 2.3. No SGA source is used. The current latest blueprint Artin–Gabber proof and the unit/chapter records were read. The old from/via chain names a distant completion auxiliary argument which the current blueprint text does not explicitly retain. I preserved the item's provenance and described the exact auxiliary input in each new from.place; I did not invent a new direct claim in the current blueprint or change the route.

The Stacks sources read were algebra.tex, lemma-quasi-finite-over-nagata, Tag 032T, and lemma-when-finite-module-complete-over-complete-ring / lemma-completion-tensor, Tags 031B / 00MA. The tags table confirms Tag 0334 for proposition-nagata-universally-japanese. The existing nodes give the generic permanence facts used by the assembly.

## What was wrong or changed

No statement dispute: the imported lifting statement agrees with Marot. The imported item had no proof. I supplied the argument instead of creating a replacement node asserting the same lifting theorem. The ideal need not be principal and the ring need not be local or a Q-algebra. Neither of those hypotheses was added. A first draft's source-place strings incorrectly paired 032S with quasi-finite Nagata permanence and 0335 with universal Japanese equivalence; inspection of tags/tags corrected these to 032T and 0334 before delivery.

## New lemma arguments retained for the next worker

The Japanese-quotients lemma is a specialization of Marot Lemma 1.2, not of the lifting theorem. Every associated prime of K/R is nonzero: an element represented by a fraction has a nonzero denominator annihilating its class. Consequently the hypothesis on all nonzero prime quotients supplies the Japanese hypothesis in Lemma 1.2. That lemma uses finiteness of normalization residue quotients from Lemma 1.1 and Mori's Noetherianity criterion for a Krull ring. Its conclusion is Noetherianity as a ring, not finiteness as an R-module; the latter is not claimed here. A future split must expose those inputs, rather than confuse ring-Noetherianity with module-Noetherianity.

The adic finiteness lemma is the application of Marot Proposition 2.1 to a normalization T already known to be Noetherian. Noetherianity gives a finitely generated radical of JT and finitely many minimal primes over JT, i.e. both conditions in Proposition 2.1. The Nagata quotient is universally Japanese by Stacks 0334. In that proposition's proof, Lemma 1.1 makes the normalization quotients by the minimal primes finite over R, the injection of T/rad(JT) into their finite product makes T/rad(JT) finite, and the finitely generated radical filtration makes T/JT finite. Lemma 1.3 supplies J-adic separatedness of T; the complete-base finiteness criterion then gives finiteness of T over R. The statement does not assume T complete or finite: those assumptions would trivialize or corrupt the result. These are future proof inputs, not hidden claims used without nodes in the item's assembly.

## Search evidence and Not duplicates

I searched the whole DAG by Marot, Japanese, Nagata, normalization/Noetherianity and adic finiteness concepts; searched the whole blueprint with tools/blueprint_refs.py for Nagata, Japanese, normalization, Marot, noetherian normalization and Nagata lifting; and searched project RingTheory sources. Neither normalization criterion occurs in the existing DAG or current blueprint. The blueprint ancestor command gives lem-per-artin-gabber-affine-curve. Both new nodes have its reference with the item prepended to via; same_as is empty.

The required leanfinder, loogle, grep and leansearch commands ran for each new node and the item, with a second leanfinder phrasing for each. Raw outputs are in search-*.txt and search-results.json; searches.jsonl is the command's log. Read the hits and Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean, including the ambient hypotheses before IsIntegralClosure.isNoetherianRing and IsIntegralClosure.finite. Both require normality of the base and separability of the extension. Neither criterion here assumes those. The other hits are completion, flatness, quotient or almost-integral-closure facts. All services answered; none was logged unavailable.

## Not duplicates

The dry run flagged the secondary 0334 citation shared by these existing nodes; I opened all twelve statements and compared them:

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-adjoin-quotient-surjective: the existing node is a surjectivity statement for an adjoined-generator quotient, with no normalization or adic finiteness conclusion.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-algebraic-monogenic-nagata-domain-n2: the existing node is N-2 ascent for an algebraic monogenic extension of a base already Nagata; our base is not assumed Nagata and our normalization need not be monogenic.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-finite-away-maximal-localization: the existing node is localizes an already finite map; our lemma establishes finiteness of a normalization not assumed finite.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-associated-contraction: the existing node is contracts an associated prime for a principal quotient of a monogenic algebra over a normal domain, without an adic finiteness conclusion.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-associated-localization: the existing node is identifies certain associated-prime localizations with height-one localizations; our conclusion is global module finiteness of a normalization.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-finite-split-algebra: the existing node is constructs a finite split-polynomial cover of a monogenic algebra over a normal Nagata domain; our base is not assumed normal or Nagata.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-generator-in-maximal-unramified: the existing node is gives analytic unramifiedness at selected maximal ideals of a monogenic algebra; our lemma gives normalization finiteness for a complete pair.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-maximal-finite-cover-core: the existing node is constructs an auxiliary finite cover of a monogenic localization with specified local models; our normalization is fixed in an arbitrary finite extension.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-maximal-finite-cover: the existing node is assumes a universal local analytic-unramifiedness calculation and constructs a cover; our lemma assumes Noetherianity of a specified normalization and proves it finite.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-nagata-domain-n2: the existing node is N-2 ascent for a monogenic extension of an already Nagata domain, whereas our base has only a Nagata quotient and the normalization is arbitrary.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-principal-localization-model: the existing node is constructs a monogenic model after inverting a nonzero base element, with neither complete-pair hypotheses nor normalization finiteness.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-monogenic-principal-quotient-conditions: the existing node is gives height, regularity and analytic unramifiedness for associated-prime quotients; our conclusion concerns global module finiteness of a normalization.


lem-per-japanese-quotients-noetherian-normalization vs lem-per-adic-nagata-lifting: no complete pair or Nagata closed fibre is assumed, and the conclusion is only ring-Noetherianity of each normalization, not the Nagata property of R.

lem-per-adic-noetherian-normalization-finite vs lem-per-adic-nagata-lifting: fixes one finite extension and assumes its normalization is Noetherian; concludes module finiteness for that normalization, not the assertion for all prime quotients without this extra hypothesis.

lem-per-japanese-quotients-noetherian-normalization vs lem-weil-pbc-tate-n2-complete-principal: the former has no normality, prime principal divisor or completion hypothesis and only concludes ring-Noetherianity, while Tate gives N-2 under its different hypotheses.

lem-per-adic-noetherian-normalization-finite vs lem-weil-pbc-finite-over-complete-ring: the existing result is a module criterion requiring separatedness and a finite reduction; the new normalization lemma proves the conclusion from ring-Noetherianity and a Nagata closed fibre without assuming either of those module properties.

No existing node has the new nodes' Marot source place. Their secondary Stacks 0334 pointer concerns an equivalence of Nagata and universally Japanese, not either normalization criterion.

## Review by Q153

I read delivery-errors B through E and reviewed the concrete assertions, rather than treating a citation as a proof. Marot Proposition 2.3 on printed p.107 is the source for the item. For the first new node I read Lemma 1.2 on pp.104-105 and checked that the all-nonzero-primes hypothesis really implies its associated-prime hypothesis, including the field case. For the second I read both directions of Proposition 2.1 on p.106 and checked exactly how a Noetherian normalization supplies its two finiteness hypotheses. I did not infer module finiteness from ring-Noetherianity alone.

Step 1 uses def-weil-pbc-nagata-ring for the precise prime-quotient definition, and def-weil-pbc-noetherian-ring for finite generation of ideals. The chain-union argument explicitly supplies the maximal bad prime, so no unmentioned induction theorem is being applied. Quotient ideals correspond to containing ideals; this proves quotient Noetherianity directly. The prime quotient B is a nonzero domain, and larger primes are exactly its nonzero primes. Step 1 is elementary relative to the stated definitions.

Step 2 uses lem-weil-pbc-finite-module-complete-over-complete-noetherian, whose statement gives bijectivity of the actual inverse-limit map for a finite module, and lem-weil-pbc-finite-over-nagata-nagata, whose last sentence explicitly gives every quotient Nagata. I opened both nodes. B is a cyclic A-module; A is the given Noetherian complete ring; I^nB is exactly J^n, so the module conclusion is the required ring completeness and includes separatedness. B/J is the displayed quotient of A/I. This is a generic commutative algebra tool use from the other unit, declared in split_report.tool_uses. The completeness node is already Lean-closed. The proof also shows J proper, which the next criterion requires.

Step 3 cites the two new statements verbatim in citations.json. The first requires only the domain B, its Noetherianity, its Japanese nonzero prime quotients, and a finite extension of its fraction field, all explicitly supplied in steps 1-3. It gives precisely ring-Noetherianity of T. The second requires that conclusion as an additional hypothesis, plus the proper complete ideal and Nagata quotient supplied by step 2. It gives precisely finiteness as a B-module. No normality of B, separability or characteristic restriction was smuggled into either application.

Step 4 uses def-weil-pbc-japanese-domain to quantify over every finite field extension and def-weil-pbc-nagata-ring to conclude from all prime quotients. The contradiction and final quantifier closure are elementary. For each step every non-elementary invoked fact is a cited statement; none is borrowed from the proof of a definition. Every citation quote is copied directly from the cited statement, including the two new files. No new node has a proof sketch in its statement, a proof dependency, or an inline proof.

I tested I=0 (the conclusion is already the hypothesis), the zero ring (no primes, vacuous Nagata prime condition), I=A (completeness forces the zero ring), a prime containing I (then J=0 and the normalization criterion remains valid), and field quotients (the first criterion has an empty nonzero-prime condition). The new nodes allow inseparable finite extensions and nonnormal bases, as the source requires. Every proof step is shorter than 2000 characters; the entire assembly is shorter than 3000. I corrected the Stacks tag mismatches mentioned above. The two auxiliary assertions are substantive normalization lemmas with distinct hypotheses and conclusions, rather than elementary consequences or relabelled clauses of the item. No unresolved mathematical objection remains.

## Unfinished

The two new nodes are deliberately unsplit, as required for a one-level stage-1 delivery. No part of the item's assembly is left open. The retry of the required dry run passed; delivery is proceeding through the authorized direct-delivery tool.

## Delivery validation and earlier tool failure

The first dry run exited with duplicate-source-tag diagnostics. I read all twelve listed nodes, added one comparison per pair under Not duplicates, and reran only after that invocation exited. The second dry run was admitted to remote preflight slot 14, then exited 1: srvpreflight.py SSH invocation of tools/preflight_delivery.py timed out after 720 seconds; its automatic nocheckout.py fallback also timed out after 600 seconds. No preflight/check_dag/review_split verdict was returned. No tool was patched, no extra checker was run directly, and nothing was pushed. The completed sandbox split and all search/citation evidence are retained for retry.

The resumed Q153 worker retained the earlier split, citations and logged searches, compared the item with the current unsplit repository node, reread the current latest blueprint and Marot Lemma 1.2 / Propositions 2.1 and 2.3, inspected the cited node statements and Mathlib candidate hypotheses, and verified all eight citation quotes against the current statements. No mathematical correction was needed. The required retry ran as one invocation throughout its server admission wait and exited 0: `OK (not pushed) deliver/Q153/lem-per-adic-nagata-lifting at 06853b5ff8a: preflight passed`. The earlier timeout above is historical, not an outstanding validation failure.
