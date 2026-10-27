# Q158 stage-1 delivery: lem-per-characteristic-zero-dedekind-excellent

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-characteristic-zero-dedekind-excellent.json`: existing statement, now split in seven steps. The statement and its four statement dependencies are unchanged. Mathlib verdict: no excellence theorem; the semantic hits only supply Dedekind definitions and localization facts.
- `citations.json`: 19 citations, one for every `(step, node)` use, with verbatim statements retaining their hypotheses.
- `searches.jsonl`: actual msearch results, including fresh searches for the item and candidate lower-level facts. `write_split.py` is the sandbox-only preparation script, not a delivery node.
- New nodes: **0**. New Mathlib leaves: **0**.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id, characteristic-zero excellence, and Dedekind/excellence terminology, and read `RingTheory/Excellent.lean` and the characteristic-zero DVR completion declaration. The project defines excellence and proves its finite-type permanence; the DVR completion declaration supplies one G-ring input, not all clauses of this item. There is no exact project attachment.

## WANTED

None. All needed source passages are present in the local Stacks sources.

## What was wrong or incomplete

The live item was statement-only. Its statement is correct, including fields and mixed-characteristic DVRs: it assumes characteristic zero for the fraction field, not for the residue field. Nothing is STATEMENT-DISPUTED, and no statement change is proposed.

Stacks 07QW assembles G-ring, J-2 and universal-catenarity results. Its 07PX proof calls the Dedekind G-ring argument immediate, while 07PJ explicitly writes out only its Nagata-dimension-one case and leaves the Dedekind characteristic-zero case to the same 07PC criterion. I supplied the missing case analysis in the item itself. I did not create a node restating either the G-ring clause or the J-2 clause of the item.

I read the current blueprint at `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/`, including `_section.md` and the ancestor's proof. The item has a recorded indirect origin through the excellent trait needed by the log-alteration argument. That provenance is retained precisely as recorded, including the warning that it does not restore the ancestor's discarded proof. The algebraic split stays below that existing dependency; it changes no unit or chapter. The chapter/unit records were read but not edited.

## What could not be finished

Nothing in the one-level stage-1 split. The reused non-Mathlib algebraic tools remain the responsibility of their existing nodes.

## Search results and node reuse

All new searches used the prescribed `msearch.py Q158 lem-per-characteristic-zero-dedekind-excellent` command. For the item I ran two semantic phrasings, Loogle on `"Excellent", "IsDedekindDomain"`, the RingTheory grep `IsExcellent|ExcellentRing|excellent|catenary`, and LeanSearch on characteristic-zero Dedekind excellence. Loogle and grep returned no hits; the semantic services returned Dedekind definitions and DVR-localization declarations, not excellence. Earlier Q108 searches were retained as history rather than represented as my own calls.

While checking lower-level inputs, Loogle found `instIsRegularRingOfIsDedekindDomain` in `Mathlib/RingTheory/RegularLocalRing/Defs.lean:120`. I read lines 90–130, as well as the Dedekind predicates and PID instance in `DedekindDomain/Basic.lean`. The instance's proof uses exactly the zero-prime/field and nonzero-prime/DVR cases written here. There is no need to introduce another leaf: regularity of a DVR follows in a few lines from the existing dimension-one node and the principal-maximal-ideal definition. A proposed PID-normality helper was also discarded after the whole-DAG search found the existing `lem-weil-pbc-pid-noetherian-normal`. Semantic output that describes `IsDedekindDomainDvr` as saying the ring itself is a DVR was not trusted: that predicate concerns its nonzero prime localizations.

Whole-DAG and whole-blueprint searches used Dedekind, excellent, catenary, J-2, regular ring, integrally closed, and Stacks 07QW. The exact existing tools were opened before being cited. `blueprint_refs.py ancestor` confirmed `lem-per-artin-gabber-affine-curve`; the item's non-unspecified provenance remains, and `same_as` is empty.

## Not duplicates

No new nodes. Existing nodes are reused for Dedekind localization, DVR dimension, PID normality and Noetherianity, field regularity, characteristic-zero purely inseparable extensions, regularity of DVR completion, universal catenarity, and the J-2 residue-field criterion. In particular there is no duplicate of the existing 07PX DVR completion theorem or 07PC J-2 criterion.

## Review by Q158

I read the item's Stacks source `more-algebra.tex`, Tag 07QW (`proposition-ubiquity-excellent`), its cited Tag 07PX (`proposition-ubiquity-G-ring`) and Tag 07PJ (`proposition-ubiquity-J-2`), and the actual condition (4) of Tag 07PC (`lemma-J-2`). I also read Algebra Tag 034X (`lemma-characterize-Dedekind`) and Tag 00PD (`lemma-characterize-dvr`), including the equivalence of the principal, regular-local and normal-local descriptions. There are no new nodes needing separate source reviews.

For step 1, I opened `lem-sc-dedekind-localization-dvr`. Its statement really assumes dimension exactly one and a maximal ideal; it is not a field-inclusive localization statement. I therefore first prove dimension one whenever a nonzero prime is being considered, check that the prime is maximal by the item's hypothesis, and treat the zero prime separately as the fraction field. The dimension and localization definition nodes say exactly what the chain argument and the formula for localized fractions require. This also verifies that every nonzero localization has the original characteristic-zero fraction field K, a hypothesis needed later.

For step 2, I read the statements of `def-sc-discrete-valuation-ring`, `lem-sc-dvr-dimension-one`, `def-weil-regular-scheme`, and `lem-weil-pbc-field-regular-ring`. The DVR definition gives a principal maximal ideal and the equivalent Noetherian local form; the dimension node says exactly dimension one. Regular locality is therefore an application of the definition of regular local ring, not an uncited theorem. The field node supplies the zero-prime case. This step is marked elementary because all its content after the cited facts is the one-generator/dimension-one comparison.

For step 3, I opened `lem-trf-regular-ring-universally-catenary`; its statement requires Noetherianity and regular locality at every prime and concludes universal catenarity. Step 2 gives those hypotheses. This agrees with the regular-ring consequence in 07QW's proof, sourced there from Algebra 00NM/00NQ. No finite-dimensionality assumption is silently added to this general tool.

For step 4, I opened `lem-weil-pbc-dvr-completion-regular`, not merely its generic-fibre helper. The cited statement gives the entire regular completion map under precisely the Noetherian-local-DVR and characteristic-zero fraction-field hypotheses verified in steps 1–2. The G-ring definition quantifies over all primes and includes the completion and regular-map definitions. The field case is written out: completion at zero is constant, the identity tensor functor is flat, and its finite field base changes are regular fields by the cited field node. I therefore use the definition directly, without introducing a G-ring theorem duplicating one of the item's clauses.

For step 5, I opened the full statement of `lem-exc-j2-residue-field-criterion`. It asks for finite A-subalgebras B inside the specified L, fractions exhausting L, and a nonempty regular open, for every prime and every finite purely inseparable extension. At zero, the existing purely-inseparable definition explicitly says the characteristic-zero extension is trivial; B=A has fraction field L, is generated by 1 over itself, and has its whole spectrum regular. At a nonzero prime, maximality is available, so the residue field is A/p; B=L has a finite basis over A/p, whose coefficients lift to A. Thus finiteness as an A-module is proved rather than inferred from a mere finite-type assertion. A field is its own fraction field and has its whole one-point spectrum regular by the cited field node. The criterion's conclusion is exactly J-2. No assertion that mixed-characteristic residue fields are perfect is used.

For step 6, I read `def-exc-excellent-ring`; its four conditions are exactly those now obtained, so assembly is elementary. For step 7, I read `lem-weil-pbc-pid-noetherian-normal`, which really gives both Noetherianity and integral closedness for a PID, and `lem-sc-dvr-dimension-one`. Along with the local principal-domain definition of a DVR these yield the exact original hypotheses. A nonzero prime strictly below the unique maximal ideal would make a length-two chain from zero, contradicting dimension one, so the maximal-prime condition is checked explicitly.

I tested the argument on A=Q, a mixed-characteristic DVR such as Z localized at (p), its complete version Z_p, and the nonlocal Dedekind example Z. For a field only the zero-prime case occurs. In the mixed-characteristic cases the potentially imperfect positive-characteristic closed residue field causes no problem because any specified finite purely inseparable L is itself the finite regular model. The regularity argument does not require henselianity, completeness, finite type over Z, or perfection of a residue field. A characteristic-p Dedekind domain is outside the statement: the B=A choice at its generic point would fail for a nontrivial purely inseparable fraction-field extension, so that hypothesis has not been lost.

I checked delivery-errors B–E against these actual files: there are no new unsplit proof sketches, missing definition nodes, duplicate nodes, clause-restatement helpers, source-only citations, circular steps, or uncited non-elementary implications. Every use has a verbatim quote in `citations.json`, and the proof dependency list is their exact union. All steps are shorter than 2000 characters. The three off-unit theorem uses (regular-ring catenarity, DVR completion regularity, J-2 criterion) are declared in `split_report.tool_uses`: each is a generic commutative-algebra tool explicitly used by the Stacks route, and none replaces the current perverse-unit argument.
