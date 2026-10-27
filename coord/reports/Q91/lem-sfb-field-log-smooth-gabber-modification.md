# Stage-1 report: lem-sfb-field-log-smooth-gabber-modification

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-log-smooth-gabber-modification.json: existing statement, now split in seven steps; no Mathlib match. The statement and statement dependencies are unchanged.
- citations.json: every proof-step citation, with an exact complete statement copied from its node.
- searches.jsonl: actual search-command log; four search kinds plus a second semantic phrasing were run and their hits read. Ordinary smoothness/etaleness, rational maps, normalization and Proj valuative criteria do not supply logarithmic modification. There are no new nodes and no Mathlib leaves.
- report.md: this report. write_split.py is a sandbox-only preparation script, not a project change.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, id, logSmooth/log_smooth/veryTame/very_tame and Gabber/log-regular terminology found no theorem giving this assertion. Existing Gabber declarations concern henselian étale cohomology or Artin vanishing, not logarithmic modifications.

## Wanted literature

WANTED: Rydh, Existence and properties of geometric quotients, arXiv:0708.3333v2, Theorem 4.4, Proposition 4.7 and Remark 4.9, for the existing tool lem-per-projective-finite-group-quotient used by this item. The PDF is not in literature/. Its existing node already records this; I checked the online original without downloading or writing a literature file. The present split uses that node's complete statement as a tool, not an unrecorded direct citation.

WANTED: Kato, Logarithmic structures of Fontaine--Illusie, Theorem 3.5, for the existing chart criterion def-per-fs-log-smooth-etale. This is already recorded by that node. I read the local criterion and its applications in ILO X 1.2 and 1.7--1.8 instead; there is no new unsplit claim concerning this reference.

## Errors and corrections

No statement dispute. ILO X 1.1 is exactly the intended logarithmic theorem over the fixed trivial log field. It does not assert that the modification itself is log smooth, and I have not used that false assertion: the composite to the field is proved log smooth in the chart checks. No regular/SNC conclusion is substituted for this item.

The proof was empty. It is now the absolute four-stage construction plus the relative checks in X 1.3--1.8. I did not create a field restatement of the existing absolute or toric lemmas, nor misuse the existing trait-only lem-per-gabber-log-smooth-equivariant-modification. Those would duplicate inputs or apply the wrong base hypotheses.

The inherited blueprint.from.node is null: blueprint_refs.py ancestor returns None for this chain. I retained that result and the explicit inherited ancestry. The newest blueprint is literature/blueprint/latest (main-20261023-1620). I read its direct-images statement and proof: proof (3) reduces through proper and open direct images. This item supplies geometry beneath the added tame-boundary generator proof. Searches for very tame, log smooth, Gabber, modification and quotient found no blueprint statement of this field theorem; same_as is empty. No chapter/unit fields or route were changed. Every off-unit geometry theorem is declared as a generic tool in split_report.tool_uses.

## Unfinished work

None within the requested one-level split. Existing theorem inputs remain the responsibility of their own nodes. No Lean was written or compiled, no git command was run, and all writes were inside this sandbox.

## Not duplicates

No new nodes were created. The trait-only relative theorem is not cited as a field theorem. Existing absolute modification, two local chart constructions, quotient theorem and log calculus are reused directly.

## Review by Q91

I read ILO Exposé X Theorem 1.1 (printed pp.135--136), the proof's preparation and preliminary stages (1.2--1.3, pp.136--140), the fixed-locus calculation (1.4--1.7, pp.141--146), and the retained-boundary quotient calculation (1.8, pp.146--148). I also read VI 3.1--3.5 (pp.73--75) for very tameness and the invariant quotient, VIII 1.1 and its warning example (pp.85--86), and Stacks 07QW and 07QU in more-algebra.tex for excellence. I read every statement cited in the seven proof steps and all statement-definition dependencies. There are no new nodes needing an additional source check.

Step 1 uses exactly the excellent-field conclusion of lem-exc-fields-excellent and the locally finite-type stability and quasi-compact Noetherian conclusion of lem-per-quasi-excellent-finite-type-stability. X is finite type and hence quasi-compact. lem-trf-projective-bundle-separated states separatedness for the required projective space. The remaining diagonal calculation, field log-regularity, and subgroup-order divisibility are written out. The trivial base has no boundary, so the map of pairs imposes no extra condition; no perfectness is assumed.

Step 2 uses the full stated four-stage construction of lem-per-gabber-absolute-equivariant-modification. It applies to integral, separated, Noetherian qe fs log regular X with tame generically free action, all checked in Step 1. Its last paragraph explicitly gives finite-projective-space projectivity and quasi-projectivity over the affine Noetherian field base. Its statement supplies the exact boundary and strict-local meaning of very tame. Density of the unchanged free/triviality open follows from integrality, not from an unstated resolution property.

Step 3 uses the same node's specification that the first two stages are saturated log blowup towers, and the stated log-etale and composition assertions of lem-per-log-smooth-composition-strict-base-change. It establishes the initial induction hypothesis for the third stage, rather than assuming preservation through all blowups.

Step 4 uses the actual statement of lem-per-gabber-fixed-locus-log-chart: the two covering chart monoids, smooth polynomial variables, and blowup/strict-transform comparison are all in that statement. The regular G-strict boundary and tame action are in force from Step 3 and the absolute procedure. Since the base log structure is trivial, choose its sharp chart Q=0 even after strict étale localization; the completions of both displayed chart monoids are free abelian. The zero kernel and zero torsion give precisely the hypotheses of def-per-fs-log-smooth-etale. The cited log calculus supplies strict base-change stability and locality. The finite procedure and its output conditions come from the absolute construction, not a new hidden termination claim.

Step 5 uses lem-per-projective-finite-group-quotient exactly for finite categorical geometric quotient existence, integral quasi-projective finite-type quotient and the invariant structure sheaf. The base Spec F is affine Noetherian and thus satisfies its base assumptions. The finite map's invariant affine preimages show admissibility. Generic freeness survives on the equivariantly unchanged dense open. lem-per-very-tame-log-quotient then applies: its statement says fs log regular invariant direct-image log structure, log etale Kummer projection, and factorization over the fixed base. I did not infer the log theorem merely from the ordinary quotient definition.

Step 6 uses lem-per-gabber-abelian-stage-toric-chart, whose hypotheses are precisely the output conditions of the third stage checked above. Its statement describes the quotient of the *chosen fourth stage*, including the retained boundary, strict base changes and étale comparisons, and the affine-space comparison of dimension b-c. With Q=0, R'=Z^a+N^c has torsion-free group completion, so the chart criterion proves the actual quotient morphism to the original field is log smooth. This is a chart argument rather than a citation of a new node restating the desired log-smoothness clause. Composition with the already obtained log etale p gives the assertion for X'.

Step 7 checks the extra boundary clauses. The Kummer maps of characteristic monoids are injective and have positive multiples in the image, as the cited quotient node explicitly states. A sharp fs monoid has no nonzero torsion: saturation puts both signs of a torsion element in it, and sharpness kills that unit. This proves equality of triviality loci. Orbit fibres and invariance of B' identify the image boundary. lem-trf-log-regular-divisorial-structure explicitly states openness/density of the triviality locus and equality with the divisorial structure, so it supplies exactly the final identification and closedness; I removed an unnecessary appeal to a separate finite-closed-map fact. The invariant direct-image log structure is therefore the exact divisorial structure asked for, not an unspecified log structure on P.

I checked small cases: trivial G allows the identity; empty B with a nonfree tame action introduces the exceptional boundary (the scalar involution on A^2 from VIII 1.2 illustrates why h itself need not be log smooth); a free action introduces no extra nonfree boundary; rank-zero Q and c=0 give ordinary smooth charts; no positive-characteristic step uses perfectness. All seven steps are under 2000 characters and none hides a new lemma: the substantive chart and gluing results are existing cited nodes. The new-node checklist B is vacuous; C1/C4 are addressed by opening the statements and copying their exact text to citations.json; C6 and the remaining DAG/schema checks are deferred to the required server dry run. D1/D2 are avoided by reusing existing strictly smaller construction tools and performing the relative calculation in the item's proof. There is no SGA citation or detour through purity or duality.
