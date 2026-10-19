## Files written

- dag/nodes/sec-trace-formula/lem-trf-integration-as-pushforward.json — statement, split; no Mathlib match. Rebased the retained split onto the current shared item record and clarified step 2. The statement is unchanged.
- citations.json — ten verbatim statement excerpts, covering every step/node citation; refreshed all three excerpts from def-trf-borel-moore-pushforward.
- report.md — current repair and source revalidation, replacing the previous report's historical validation and handoff instructions.

New nodes: none. Mathlib leaves: none. The existing Mathlib search records and searches.jsonl are retained unchanged; this repair invents no search records.

## Attachments

None. I repeated the exact-id search throughout WeilConjectures in the read-only slopmaster2 source; no exact blueprint tag was found. Searches for borelMoorePushforward and integral found Correspondence.lean:874–952, which I read. AlgebraicGeometry.ProEtale.GeometricOperations.integral (947) defines integration as pushforward followed by dualizingBase; it does not prove the comparison with the independently specified three-arrow cohomology definition used by this item. borelMoorePushforward_id (901) is the identity-morphism assertion, not the structure-map assertion. The trace-class results apply to particular sections, not every section. These do not provide an attachment for the complete item. No upstream sorry declaration was treated as a finished proof.

## WANTED

None. No SGA source is used.

## Faults found and corrections

The return in coord/returns/NK.md identifies delivered head 023b6a4293 and rejects the landing because def-trf-dualizing-complex changed after review. I continued from the retained sandbox, not from a replacement imported proof. Its dualizing citation had already been refreshed by the previous repair attempt and is still an exact excerpt of the current statement. I reread that expanded statement rather than treating the retained repair as accepted. It specifies the same formula, constructible exceptional inverse image, small pro-etale ambient derived category and bounded constructible finite-Tor domain; its additional evaluation and morphism-action clauses are unused here.

Comparing every retained citation with the current DAG exposed three further stale excerpts: def-trf-borel-moore-pushforward now explicitly sources the proper comparison to prop-functor-package, clause (3), and expands the ordinary adjunction and site conventions. I refreshed its excerpts in steps 1, 2 and 3. Step 2 now explicitly selects the comparison specified in that current definition. I also reread the current admissibility statement: its exceptional composition is the adjunction conjugate of compact-support composition under the composite adjunction. The retained proof and quote already use that current formulation and remain valid.

I rebased the sandbox item by starting with the current shared node record and retaining the owned split fields, so current import, blueprint and audit metadata survive. The delivery tool independently rebases those fields onto current origin/newtargets-dag before server preflight. No git command was run directly in the shared repository, and nothing there was written. This is a repaired proof/citation package, not an unchanged re-push.

## Source error

The blueprint proof invokes an equivalence RΓ(s,-):D(s,A) → D(A) on the entire ambient pro-etale derived category. The split does not need that overbroad claim: step 3 uses functoriality on the displayed composite and the End(A_s)=A identification already stipulated in the item. Sheaves on a pro-etale point have a richer ambient category than discrete modules. No item hypothesis or conclusion was weakened.

The source's bare assertion that exceptional composition with an identity is the identity also needed an explicit justification. Step 1 retains the compact-support identity law, the admissibility statement specifying its conjugate, and the Hom-bijection argument proving the required normalization.

## Not duplicates

No new nodes were created. The retained DAG/blueprint search evidence is preserved in the split history; I repeated blueprint_refs search 'integration pushforward' (zero matches). The unit sk-d-integral adopts integration as structure pushforward, while this item compares its expanded cohomology formula with that convention. The normalization, substitution and naturality calculations are steps, not separate lemmas or clauses moved into new nodes.

## Review by NK

I read delivery-errors B–E in full, the chapter sec-trace-formula and unit sk-d-integral records, and the current main-20261015 item statement, both paragraphs of its proof, and the unit source. The statement agrees hypothesis by hypothesis: finite coefficient stage A=A_{E,n}, proper separated finite-type T, exceptionally admissible structure map, point normalization, arbitrary Borel–Moore section, and equality in A. The unit route remains integration by structure pushforward; no replacement route or new unit is introduced.

For step 1 I reread all six cited current statements. def-trf-borel-moore-pushforward supplies the inverse dualizing-composition isomorphism in its defining composite. thm-trf-dualizing-complex-composition supplies Ra^!ω_s → ω_T at d=a, X=s. def-trf-dualizing-complex supplies ω_T=Ra^!A_s with the specified constructible functor; I compared it with main-20261015 sec-six-functors/sk-thm-sf-kunneth-verdier/def-trf-dualizing-complex.md. thm-sf-comp-composition explicitly supplies the identity law for compact-support composition, and def-trf-admissibility supplies its adjunction conjugate. I read their main-20261015 sources under sec-six-functors-basics/sk-thm-sf-comp-composition and sk-def-sf-admissible, including the latter's blueprint_update. The elementary calculation then applies the adjunction Hom bijection to c∘u and u, and takes u=1; it does not assume an ambient right adjoint.

The sixth citation, sk-thm-pe-constructible-comparison, supplies the bounded constructible equivalence giving etale-origin witnesses. I read its current blueprint _section.md and Stacks proetale.tex, lemma-compare-constructible (Tag 09AK) and lemma-compare-constructible-derived (Tag 09AL). T and s are quasi-compact quasi-separated, A is discrete Noetherian, and A_s is free rank one in degree zero. Exceptional admissibility puts ω_T in D^b_ctf. Thus the compact-support identity law is used within its etale-origin domain, and every test object in the mate argument lies in the restricted adjunction domain. The composition and constructible-comparison tool uses remain declared in split_report.tool_uses.

For step 2 I read the entire current pushforward and integration statements and their main-20261015 definition sources. At h=a and T'=s, properness and exceptional admissibility are exactly the item's hypotheses. The inverse c becomes the identity by step 1. The remaining composite is ε∘σ_ω∘Ra_*α∘η. The revised pushforward definition expressly selects the proper comparison from clause (3) of the functor package; I opened that current package statement and checked its proper-comparison clause and finite-stage D^b_ctf domain. This is the comparison already specified in the two definitions, not a new comparison chosen for the proof. The package itself is not added as a dependency: the argument uses the map specified by the cited definition, not an additional package clause.

For step 3 I checked the current pushforward comparison and each integration arrow against the second blueprint proof paragraph. The explicit naturality equation σ_ω∘Ra_*α=Ra_!α∘σ_A is the naturality square of that specified comparison. Inserting it into step 2 makes the first, middle and last arrows the integration formula. Applying RΓ preserves composition; the stipulated endomorphism identification reads both sides as the same scalar. No fullness, faithfulness or equivalence of the whole ambient point category is used.

Every citation excerpt is a literal substring of the current cited statement, and the ten citation pairs equal the uses pairs exactly. proof_deps is precisely the union of the uses lists. B: no new nodes, hidden proof sketches, unsupported Mathlib leaves or missing object introductions were added. C: all substantive inputs are cited statements; no argument is borrowed from a cited proof. D: the steps carry the normalization and naturality argument themselves. E: the constructible, finite-Tor and etale-origin restrictions are checked above. For α=0 both composites vanish; for T=s they reduce to the identity-normalized formula; for empty T they factor through zero. The argument covers n=1 and every allowed n≥1 and requires no smoothness, reducedness, connectedness or nonemptiness. No new statement needs a separate small-case audit.

## Unfinished work

No mathematical step remains open at this split level. This repair is for handoff to a fresh second reader; it does not claim a new independent review or authorize a push. Required validation: python3 /home/ubuntu/weil-launcher-nt/deliver.py NK lem-trf-integration-as-pushforward --no-push. No Lean compiler, Lake command or local DAG/preflight tool is run.


## Second reading by NK

- Item statement: compared every hypothesis and the equality with main-20261015 `lem-trf-integration-as-pushforward.md`; proper separated finite type, finite stage n≥1, exceptional admissibility, point normalization and arbitrary section all agree. PASS, unchanged.
- Step 1: opened all eight cited statements; checked the canonical composition against the admissibility definition and the identity law against `thm-sf-comp-composition.md`. Checked etale-origin witnesses against `sk-thm-pe-constructible-comparison/_section.md` and Stacks proetale.tex, `lemma-compare-constructible` (09AK) and `lemma-compare-constructible-derived` (09AL). The bounded constructible finite-Tor test objects lie in the restricted domain. Added explicit identity-adjunction conventions and the conjugacy equation; injectivity with M=Ra^!A_s and u=1 proves c=1. PASS after clarification.
- Step 2: compared both complete current definitions with their main-20261015 sources and clause (3) of the current functor package. At h=a the inverse composition is identity; the same proper comparison gives ε∘σ_ω∘Ra_*α∘η. PASS, unchanged.
- Step 3: checked the naturality equation against the specified natural comparison and each of the integration definition's three arrows. Applying RΓ preserves composition and the item's stipulated endomorphism identification yields the equality in A. No equivalence of the ambient pro-etale point category is needed. PASS, unchanged.
- New nodes: none; no duplicate, elementary stand-alone lemma, Mathlib leaf, or restatement is introduced. Searched the DAG for integration/pushforward and reread slopmaster2 Correspondence.lean:874–952: its integral definition does not prove the comparison with the independent cohomology formula. PASS.
- Small cases: α=0 gives zero on both sides; for empty T every map factors through zero; T=s uses the canonical identity adjunction; n=1 is covered without a field-only argument, while n=0 is outside the stated n≥1 coefficient convention. PASS.
- Citations and form: each of the twelve step/node pairs has one literal statement quote, checked against the read-only current DAG; proof_deps equals the union of uses. No new node requires B1–B7 repair. PASS.

Changes: made the identity-adjunction convention explicit in step 1, citing the existing composite-adjunction and conjugate definitions, and wrote Φ_M(c∘u)=Φ_M(u) rather than leaving its normalization implicit. Added the two exact citation quotes and proof dependencies. Recorded three genuinely executed independent Mathlib searches with their results; the Loogle result identifies the elementary identity-mate lemmas in Mates.lean, read at lines 319–322 and 534–545, so no new lemma node is warranted. No statement, unit route, or other proof step changed. The first worker's report and `## Review by NK` remain above.

Validation: required `deliver.py NK lem-trf-integration-as-pushforward --no-push` completed successfully: `OK (not pushed) deliver/NK/lem-trf-integration-as-pushforward at 5b1621bf03: preflight passed`. Server preflight performed the required checks; no local preflight, DAG checker, Lean compiler, Lake command, or direct git command was run. The earlier handoff note is superseded by this independent second reading and successful dry run.
