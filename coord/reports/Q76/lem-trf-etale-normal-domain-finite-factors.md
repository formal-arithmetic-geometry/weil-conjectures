# Worker report: lem-trf-etale-normal-domain-finite-factors

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-normal-domain-finite-factors.json`: existing statement node, now split; Mathlib search found no exact declaration. Nine proof steps, no new nodes, zero new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for all 14 node citations in the proof.
- `report.md`: this report. `searches.jsonl` is the search command's own log, preserved without editing.

## Attachments

None. I searched the item tag and normal/etale/factor terminology under the project `WeilConjectures/` source, also checked the upstream reference. No project declaration gives every clause. The nearby `AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk` requires a separably closed function field and does not state this arbitrary-normal-domain finite-factor result. No attachment is claimed from Mathlib.

## WANTED

None. All source texts needed are available locally.

## Errors and changes

The statement is correct and unchanged: no statement dispute. The imported node had no proof. Its source accurately describes an auxiliary consequence, rather than asserting that Tag 030C itself proves finite minimal primes for etale algebras. I supplied that missing argument: finite presentation makes the localization over the fraction field finite type and hence Noetherian; flat going-down and the localization-prime correspondence inject the minimal primes of B into its finitely many minimal primes. I explicitly give the A-algebra structures on the domain factors instead of silently upgrading a ring isomorphism.

The old Q67 search records are retained, including their exact queries, results and digests. Two no-hit verdicts had copied wording about a henselization theorem; I corrected only that explanatory wording. Five additional searches were actually run through msearch and their actual result records are included. The returned field-product declarations in `Mathlib/RingTheory/Etale/Field.lean` were read: the ambient variables include `[Field K]`. They handle the field-base case and cannot give a one-line specialization for a general normal domain. The second phrasing returned smooth finite-type descent, finite integral closure and finite-normal-closure results, not the requested finite-factor theorem. Loogle and the RingTheory grep returned no hits. No unavailable service was recorded as a negative search.

## Unfinished work

None in this stage-1 split. No Lean files were written and no compiler, Lake, local DAG checker or build was run.

## Not duplicates

No new nodes. Searching the DAG by Tag 030C and by normal-domain/product/etale terminology found the general existing `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`, which is reused. The narrower domain-decomposition node need not be duplicated. The existing `lem-fin-etale-normal-components` assumes a Noetherian base and is not a substitute here. Whole-blueprint searches for the finite-product normal-domain etale statement and for 030C found no equivalent blueprint statement. The item's existing ancestry to `lem-trf-local-term-locality` and its complete via chain are preserved.

## Review by Q76

I read Stacks Algebra Tag 030C (`lemma-characterize-reduced-ring-normal`) and its proof, not merely its title. It requires reducedness and finitely many minimal primes; normality alone is insufficient for applying it. The item's stronger application is justified using Tag 033C (`lemma-normal-goes-up`, including its non-Noetherian case), Tag 00GY (`lemma-localize-normal-domain`), Tag 00HS (`lemma-flat-going-down`), Tag 00E3 (`lemma-spec-localization`), Tag 00FN (`lemma-Noetherian-permanence`) and Tag 00FR (`lemma-Noetherian-irreducible-components`). I also read Morphisms Tag 01TQ (`lemma-locally-finite-presentation-characterize`) and Schemes Tags 01HV (`lemma-spec-sheaves`) and 01I2 (`lemma-category-affine-schemes`). There are no new statements whose sources require a separate audit.

Step 1 is the zero-ring case, with the unique A-algebra isomorphism to the empty product. It is elementary and prevents exclusion of an expressly allowed case.

For Step 2 I opened all four cited nodes. `lem-weil-pbc-localization-normal-domain` explicitly includes localization at every prime, so it makes the given normal domain A a normal ring under `def-weil-pbc-normal-ring`. `lem-weil-pbc-etale-over-normal-ring-normal` assumes exactly the etale spectrum morphism and a normal ring, with no Noetherian requirement. It therefore supplies B's normality. The last sentence of `lem-weil-pbc-prime-localizations-jointly-injective` explicitly says reducedness of all prime localizations implies reducedness of the ring. Each localization here is a domain by the definition of normal ring, and its reducedness follows by cancellation. I did not use a definition node in place of the reducedness-detection theorem.

For Step 3, the cited etale definition includes local finite presentation. The affine-opens lemma says finite presentation for every pair of affine opens, so the entire spectra qualify. I added `lem-weil-pbc-spec-map-global-sections` because its statement identifies the induced ring map with A -> B, including naturality; no unproved global-sections comparison is hidden. A finite presentation exhibits finitely many algebra generators directly.

Step 4 is an elementary fraction calculation using the full fraction construction in `def-weil-pbc-module-localization`: it constructs the K-action rather than assuming an identification with a tensor-product generic fibre. For b/t with b=P(b_i), each coefficient a is replaced by a/t, which is a legitimate element of K because t comes from a nonzero element of A. The localization equivalence relation gives independence of representatives. Thus the same finite list generates C over K. No etale-field decomposition or localization/base-change theorem is being smuggled into this step.

For Step 5 I read the statements of both existing Noetherian lemmas. The finite-type-algebra lemma requires a Noetherian base, supplied here by the elementary two-ideal argument for the field K, not by any condition on A. Its conclusion supplies precisely the Noetherian hypothesis for the finite-minimal-prime lemma applied to C.

For Step 6 the etale-algebra-flat node states flatness as an A-module for the spectrum hypothesis we have. The going-down node explicitly lifts any chain of primes under a specified prime upstairs. I use the chain (0) contained in q intersect A, with (0) prime because A is a domain. Minimality of q forces equality with its lifted subprime, proving contraction (0), hence avoidance of W. Faithful flatness is not assumed.

For Step 7 I read clause (1) of `lem-weil-pbc-localization-prime-residue-field-iso` in full. It covers arbitrary multiplicative subsets and explicitly supplies both extension and contraction inverse identities. The node for only prime/principal localizations would not suffice, so I use this general node. Contracting a smaller prime below qC gives a prime contained in q; its equality with q and the inverse identity prove minimality upstairs. Contraction recovers q, so the map on minimal primes is injective. This verifies exactly the finiteness hypothesis needed in Step 8.

For Step 8 the existing total-fractions criterion explicitly states the three-way equivalence and the finite product of normal domains. B is reduced, normal and has finitely many minimal primes by the earlier steps, so implication (1) to (3) applies verbatim. This is an existing general tool, not a newly created restatement of the item. In Step 9 the coordinate definition of A -> B_j and the displayed equality of structure maps show both directions of the ring equivalence respect A. This elementary transport preserves all domain and normality assertions.

Against delivery-errors B: there are no new nodes, inherited statement notions and blueprint references remain valid, the statement's TeX was preserved, exact logged searches are recorded, and no unsupported Mathlib match or attachment was asserted. Against C: every non-elementary ingredient above has a node citation whose statement was read; the complete quotes are in citations.json. The three non-Mathlib off-unit ring-theoretic tools are declared in split_report.tool_uses with their precise uses; they establish this historical auxiliary and replace no current unit proof step. Against D: the proof carries the finiteness and algebra-structure arguments itself, without making a new clause node or hiding an argument in a cited proof. Against E: I checked domains rather than merely reduced rings are used when (0) must be prime; arbitrary localization rather than only principal localization is used; and Noetherianity is imposed only on C. Edge cases checked were B=0, B=A, B=A times A, and B=A_f (f nonzero), all consistent with the conclusion, and a non-Noetherian normal-domain A does not invalidate any cited hypothesis. No proof step exceeds 2000 characters (the largest is under 600), and the elementary ones have their calculations written out. No external return entry was supplied for this first delivery; the substantive correction during self-review was adding the explicit Spec/global-sections naturality citation.
