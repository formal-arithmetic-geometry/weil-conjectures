# Stage-1 report: lem-sfb-finite-normalization-local-dvr

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-normalization-local-dvr.json: statement, split; retained the full statement, statement dependencies, source, provenance, old searches and blueprint ancestry; wrote four proof steps and appended actual Q82 searches. Mathlib does not state the complete item under its hypotheses.
- citations.json: seven entries quoting the statements used by the four steps verbatim.
- report.md: this report. No new nodes; no new Mathlib leaves.

## Attachments

None for this item. Searched the whole live WeilConjectures source for the item id, and the relevant RingTheory sources for integral closure, DVRs and Krull–Akizuki. The existing krullAkizukiNoetherian declaration gives only the Noetherian clause; the dominating-DVR declarations do not give the normalization construction or its every-prime and contraction clauses. Mathlib's normalization theorem requires a normal base and separability, so is not an exact theorem for this item. The live library, not an older upstream checkout, was used throughout.

## WANTED

None. All needed Stacks source is present in literature/stacks-project/algebra.tex.

## Audit and changes

The statement is correct, including inseparable extensions and nonnormal D. Nothing in its mathematical statement or statement dependencies changed. In particular the word “finite” in the title refers to the field extension: no module-finiteness of C over D is asserted or used. Such finiteness would need extra hypotheses. Its existing source correctly names 09IG (lemma-integral-closure-Dedekind); 034X is the different lemma characterizing Dedekind domains.

The item initially had no proof. Reused lem-sc-integral-closure-dedekind-surjective-fibres, which states the normalization theorem without locality and includes finite-fibre and residue-field conclusions not needed here. Reused the finite-extension normal/fraction-field leaf separately because the 09IG node does not explicitly state that L is the fraction field. Reused the existing lying-over, Dedekind-localization-DVR, normal-localization, prime-localization definition and maximal-ideal-contraction nodes. Created no new nodes and no restatements of clauses of this item.

Read the chapter and unit records and the latest blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md, especially clause (3). The inherited ancestry records the boundary-DVR algebra prerequisite of the alteration route. This split stays below that prerequisite and follows 00PH. It does not change the unit or chapter route. The generic 09IG normalization theorem is declared in split_report.tool_uses because its existing node is filed in a different unit. The other external facts are Mathlib leaves. Whole-DAG title/statement searches and whole-blueprint searches for integral closure, lying over and normal local rings exposed the reusable nodes. The item's inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor reports; that existing ancestry is retained, with its precise nonempty place and same_as = [].

Mathlib searches were executed only by the mandated msearch.py command. The searches.jsonl answers were read. The second phrasing explicitly asks about Krull–Akizuki without normality or separability; its normalization hits were checked against IntegralClosure.lean:147–174,220–237, where separability and normality/Dedekind hypotheses exclude an exact match. Dvr.lean:127–137 proves just the existing DVR-localization leaf. Prior searches on the item remain untouched. No compiler, Lake, Lean editing or repository git command was used.

## Not duplicates

No new nodes. The existing normalization theorem is more general than the normalization clause, the fraction-field theorem supplies a separate explicit conclusion, and the existing localization lemmas supply the remaining construction. No replacement or duplicate node was created.

## Review by Q82

I read Tag 00PH (algebra-lemma-exists-dvr), its final proof paragraph, and Tag 09IG (algebra-lemma-integral-closure-Dedekind) with its proof. The former explicitly uses Krull–Akizuki, lying over and localization; the latter packages the general Noetherian normal dimension-one normalization input. I also read 00PG, 00GQ, 00OK, 00PD, 034X and 00GY in algebra.tex. There are no new nodes requiring separate source review.

For step 1 I opened lem-sc-integral-closure-dedekind-surjective-fibres and lem-weil-pbc-integral-closure-finite-extension-normal and checked their complete statements. The first gives exactly Noetherianity, normality and dimension one for the integral closure in any finite extension; the second explicitly identifies the given L as fraction field. All hypotheses are those of D,K,L in this item. I deliberately did not infer that field identification from the 09IG node alone, or apply Mathlib's separable normalization theorem.

For step 2 I opened pqf-lem-lying-over: it assumes only an injective integral map and gives a prime contracting to each prescribed prime. D embeds in C and every element of C is integral over D by the integral-closure definition. For every prime over m_D, a nonzero d in m_D remains nonzero in C; maximality follows from the impossible length-two chain (0) strictly below q strictly below a larger maximal ideal in a dimension-one domain. This explains the universal “every such prime”, not only the chosen one. No reverse maximal-contraction assertion is used.

For step 3 I opened lem-sc-dedekind-localization-dvr and lem-weil-pbc-localization-normal-domain. The former defines its Dedekind hypothesis explicitly as Noetherian normal dimension one, which step 1 provides, and requires a maximal ideal, proved in step 2. The latter explicitly gives both the injective fraction map and equality of fraction fields. Its multiplicative set is the complement of q, which contains no zero. Fractions represent every localization element, so the image has exactly the stated form; d/1 checks inclusion of D. No nontrivial localization theorem is hidden in the image check.

For step 4 I opened def-weil-pbc-localization-at-prime, which explicitly states locality and maximal ideal qA, and lem-trf-localization-maximal-contraction, which explicitly states the contraction equality. Composing preimages gives the equality over D. This step is elementary relative to those cited statements. citations.json copies the statement text for every cited node in every step, without adapting quotes to a desired inference.

I checked B–E of delivery-errors.md against the files: no new definitions, unsourced sublemma, clause restatement, weakened hypotheses, proof-of-a-cited-node dependency, or source substitution. All step sources give tags and TeX labels. All proof dependencies are exactly the union of uses. Each step is under 600 characters, so none hides a long auxiliary lemma. The nonzero, local dimension-one hypotheses exclude a field D; the identity extension L=K is allowed; multiple primes over the closed point are handled individually; purely inseparable finite extensions are allowed by both normalization inputs. Ramified examples such as D = Z localized at a prime are consistent with the image and contraction assertions, which do not assert that the maximal ideal of A is generated by m_D.

## Unfinished work

None in this one-level stage-1 split. Existing dependencies remain the project's existing nodes; no Lean proof is claimed by this delivery.
