# Q90 stage-1 delivery

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-g-ring-quasi-excellent-closed-fibre.json: item split into seven proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-g-ring-alteration-closed-fibre-neighbourhood.json: new statement-only lemma, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for each node cited in each numbered step.
- searches.jsonl: actual msearch.py search log, including two semantic phrasings for the item and for the new node.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag and the quasi-excellence/G-ring concepts found no declaration stating the item or the new alteration assertion. The existing G-ring results and regular local algebra infrastructure do not state this theorem. No Lean files were written and no compilation was run.

## WANTED

WANTED: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber), https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf, Theorem 4.1 and Lemmas 4.4–4.5, printed pp.4–7, for both delivered nodes. I read the paper online, but the read-only literature directory has no archival copy; bibliographic integration is requested. The proof_origin is agent because this copy is not under literature/. The proof follows the paper rather than a substitute route.

## Findings

The item is correct as imported, including the absence of universal catenarity, characteristic, dimension and completeness assumptions. Its empty proof needed the entire Theorem 4.1 argument. There is an existing duplicate statement, lem-per-qe-jacobson-g-ring-criterion; I have not changed it or cited it as a proof. The maintainer can consolidate these two theorem nodes after independently reviewing this delivery.

The existing alteration-neighbourhood lemma cannot be applied here as stated: it assumes excellence of B_q, whereas the source needs only the G-ring condition there. A semilocal G-ring is quasi-excellent, but need not be universally catenary; thus replacing the missing hypothesis by an assertion of excellence would be unjustified. The new node uses a global G-ring B and an arbitrary prime, which specializes Lemma 4.4 without a universal catenarity assertion.

## Not duplicates

lem-per-g-ring-alteration-closed-fibre-neighbourhood vs lem-per-qe-alteration-regular-neighbourhood: the existing statement assumes excellent B_q and quasi-excellent B/J; the new statement assumes global G-ring B and only J-2 for B/J. A general G-ring localization is not assumed universally catenary, so the existing statement does not supply the needed conclusion.

lem-per-g-ring-alteration-closed-fibre-neighbourhood vs lem-per-local-alteration-diagram-spreading: spreading takes an already specified local alteration diagram as input; the new lemma produces such a diagram with ambient regularity over the entire indicated closed fibre.

lem-per-g-ring-alteration-closed-fibre-neighbourhood vs lem-per-j2-closed-fibre-regular-locus: that node gives relative openness of the ambient regular locus, not existence of alteration covers.

lem-per-g-ring-alteration-closed-fibre-neighbourhood vs lem-per-qe-weak-uniformization-cover: weak uniformization assumes a quasi-excellent base and gives globally regular charts; the new lemma starts with a G-ring and a J-2 quotient and gives regularity over that quotient after shrinking around any prime.

lem-per-g-ring-alteration-closed-fibre-neighbourhood vs lem-per-g-ring-quasi-excellent-closed-fibre: the new node does not conclude quasi-excellence or J-2, imposes no Jacobson condition, and gives alteration data. The item's finite-domain reduction, flat-open construction and specialization/descent argument remain in its seven steps.

lem-per-g-ring-alteration-closed-fibre-neighbourhood vs lem-per-qe-jacobson-g-ring-criterion: the latter restates Theorem 4.1 and gives no alteration data; it is not used to prove the item.

Whole-DAG searches by Lemma 4.4/4.5, Theorem 4.1, J-2, G-ring, alteration covering and weak uniformization were read. Blueprint searches for quasi-excellent, G-ring, alteration and regular closed fibre returned no equivalent imported node; same_as is therefore empty. The latest blueprint snapshot ef6f9619fdbffa59e88528fb56483d76c70258c8 and the ancestor's Step 3 were read. The new node belongs to the existing quasi-excellence branch below that step, not a new chapter or unit route.

## Review by Q90

I read Theorem 4.1 on printed p.4 and its complete proof on pp.6–7, Lemma 4.4 on pp.5–6, the two-point instance of Lemma 4.5 on p.6, and the alteration covering definition on p.3. I compared the new node with the actual hypotheses of Lemma 4.4: localization of a G-ring remains a G-ring (Stacks 07PV proof), and only J-2 for B/J is required. The finite proper witness and maps from its open cover are part of the covering definition, not a presumed surjectivity of a single chart. An integral proper witness can be obtained by retaining an irreducible dominating component: its proper image is closed and contains the generic point, hence equals the integral base. No purity, SGA, or characteristic-zero resolution theorem is introduced.

Step 1 uses the exact statements of lem-exc-regular-locus-open-from-prime-quotients (Stacks 07P9) and lem-per-j2-finite-algebra-criterion (07PC). The first requires all prime quotients to have regular opens, so I apply the domain argument to every C/P, not merely to minimal primes. I added lem-weil-pbc-finite-algebra-noetherian to ensure C is Noetherian before applying it. Quasi-excellence is assembled from the given G-ring hypothesis and the J-2 conclusion via def-exc-excellent-ring. I read these statements in full and the corresponding Stacks definitions/lemmas.

Step 2 uses the finite-type G-ring permanence node precisely for finite-type A to B. Module generators are also algebra generators. J-2 of B/J follows by explicitly composing finite generating lists over A/I; no general stability lemma is silently used. For the Jacobson claim I avoided an unrecorded integrality theorem: B/m is a finite A-module, and if I acts nontrivially on this field it acts surjectively, contradicting the exact statement of lem-weil-pbc-nakayama-jacobson. The relevant definitions and all these cited statements were opened. This avoids assuming that a finite-type algebra over a Jacobson-radical pair again has a Jacobson-radical ideal, which would be false without finiteness as a module.

Step 3 invokes the new node with precisely B a Noetherian G-domain and B/J J-2, as Step 2 supplies. It uses both its regularity clause and its proper-witness data, not an unstated property. The finite basic-open subcover is proved by the finite expression for 1 in the generated unit ideal, so it needs no hidden compactness lemma.

Step 4 uses the actual finite-type and quasi-compact hypotheses of lem-sbc-generic-flatness (Stacks 052A). The base B[1/b_j] is a nonzero domain, since b_j is outside a prime. I used the basic-open-basis statement of lem-weil-pbc-spec-localization-away-basic-open to replace each flat open by a principal one, then multiplied numerators in the domain to get one nonzero c. The resulting flat open need not meet every closed point. Only its generalization to a maximal point is used later.

Step 5 proves the needed two-point case of Lemma 4.5 directly. The only cited nontrivial statement is pqf-lem-proper-closed-map, whose statement says the map is closed; I read its current blueprint statement and proof. Surjectivity comes from the new node's explicit witness. Continuity and closedness give equality of the image of the point closure with the target point closure. An open containing the specialized witness point contains its generalization. These are elementary topological consequences, which is why this step is marked elementary despite its length; no chain-lifting lemma is hidden.

Step 6 uses the exact ambient local regularity clause of the new node, not regularity of the closed subscheme. A common affine neighbourhood of x_2 contains x_1; lem-weil-pbc-affine-open-stalk-localization gives both stalks as prime localizations of the same coordinate ring. I wrote out the further-localization identification by its denominators, then used lem-weil-pbc-regular-local-localization (0AFS). This checks the direction of specialization and localization carefully.

Step 7 unfolds def-weil-flat-morphism to obtain a flat local stalk homomorphism. The source B_p is Noetherian by lem-weil-pbc-localization-noetherian; the regular local target is already Noetherian by the regular-local definition. Thus lem-weil-pbc-flat-under-regular (00OF) applies with every hypothesis present. The affine base stalk is identified by the same affine-stalk node. The zero prime lies in D(c), giving nonemptiness. I read the cited local descent statement and its Stacks source.

I checked delivery-errors B–E: the new node contains a complete statement only, no proof or disguised proof; every notion has a definition or an explicit expansion; all search records are actual logged calls; every use has a verbatim citation; the new lemma is neither a theorem clause nor an elementary step; and no claim needs a source hypothesis absent from the current objects. No step exceeds 2000 characters. For small cases, I checked A=0 (empty spectra), I=0 (the same argument remains valid), B a field, nilpotent I, and J=B in the auxiliary lemma (the closed-fibre condition is vacuous and no Jacobson assumption is asserted there). The main Jacobson assumption excludes J=B for nonzero finite domain B by the Nakayama argument. The zero-dimensional/local cases do not force a positive-dimensional or nonempty closed-fibre assumption on the auxiliary node. Eight general algebra/geometry tool uses are declared in split_report; they do not replace the unit route.

The new-node searches returned ordinary quasi-finite, smooth/etale locus, Noetherian affine-cover and generic scheme-cover results. These do not state alteration regularity or specialize to it in one line. Loogle found no IsGRing, and the grep for alteration/uniformization/quasi-excellence returned no declarations. The item's separate searches likewise returned ordinary radical and smooth-locus facts, not Theorem 4.1. All services answered, and both semantic phrasings were read.

## Unfinished work

The new alteration-neighbourhood lemma is intentionally unsplit, for the next stage-1 item. No other mathematical gap is left in this assembly proof. The duplicate item statement and archival literature integration are for the maintainer, as this worker may not edit other nodes or literature/.

## Earlier delivery tool failure (resolved on resumption)

The required `deliver.py Q90 lem-per-g-ring-quasi-excellent-closed-fibre --no-push` invocation exited 1 without producing mathematical/check diagnostics. After waiting in the shared queue, srvpreflight.py admitted slot 9. Its SSH preflight timed out after 720 seconds. The tool then automatically attempted its nocheckout.py fallback, which also timed out after 600 seconds and raised subprocess.TimeoutExpired. The dry-run candidate commit printed in the traceback is fc2618ef35e8728aea100e199006627c95090ce3, based on b13a5e912820e76286761d578d07033ea43d73bc. This is not a successful dry run and is not a delivered commit. No push was attempted. The original invocation has exited; no second invocation is active. All split, report, citation and search files remain in this sandbox. Launcher scripts were not edited or bypassed.

## Resumption review by Q90 (2026-10-24)

The required first dry run on the retained files exited successfully: `OK (not pushed) deliver/Q90/lem-per-g-ring-quasi-excellent-closed-fibre at 4875b1fdc75: preflight passed`. The earlier timeout above is historical and no longer blocks this delivery.

I compared the sandbox item against the current live item: only proof, proof dependencies, proof origin, searches, status, blueprint provenance and split report differ. The statement is identical; no repair note reopens or alters it, and the live node remains unsplit. I retained the entire proof, new statement, citations and logged searches. The latest blueprint is still ef6f9619fdbffa59e88528fb56483d76c70258c8. I reopened its ancestor node, the chapter and unit records, and the present project Lean search results: none states the item or auxiliary lemma as a finished declaration.

I reread the online Kurano–Shimomoto PDF, Definition 3.2, Theorem 4.1, Lemma 4.4 and Lemma 4.5 with the seven proof steps open. I reopened every statement cited in those steps and verified all 20 citation quotes against the current statements. In particular, Step 1 checks every prime quotient, as the current Stacks 07P9 statement requires; Step 2 needs only the J-2 clause of the quotient hypothesis; Steps 5–6 keep the specialization direction correct; and Step 7 has both local Noetherian hypotheses for 00OF. I also read the local Stacks statements 07P9, 07PC, 0AFS and 00OF. The alteration lemma requires regular ambient stalks, exactly as (4.2) states. The stronger excellence hypothesis of the existing alteration-neighbourhood node is still present, so that node remains inapplicable and the distinction in Not duplicates remains substantive. The existing identical Theorem 4.1 node is reported for later consolidation, not used as a circular proof.

No mathematical or node-file correction was needed. The only resumption edit is this report update recording that the previous infrastructure failure has cleared. A final dry run and direct delivery follow.
