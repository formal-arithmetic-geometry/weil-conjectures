# Stage-1 report: lem-exc-punctured-curve-branches

## Files written

All paths below are relative to this sandbox. All five node files are in `dag/nodes/sec-smooth-purity/`.

- `lem-exc-punctured-curve-branches.json`: statement unchanged; eight proof steps, audited statement dependencies and exact citation ledger; status split.
- `def-exc-excellent-ring.json`: definition, unsplit; no Mathlib match. Defines quasi-excellence, excellence, J-2 and universal catenarity, using the existing G-ring definition.
- `lem-exc-quasi-excellent-nagata.json`: statement only, unsplit; no Mathlib match. Stacks 07QV.
- `lem-exc-finite-type-localization-excellent.json`: statement only, unsplit; no Mathlib match. Stacks 07QU.
- `lem-exc-local-curve-principal-total-fractions.json`: statement only, unsplit; no Mathlib match. Stacks 0C3R, a commutative-algebra parameter/localization lemma.
- `citations.json`: one verbatim statement quotation per node used in each numbered proof step.

`searches.jsonl` is the actual msearch log. `search_results.json` preserves all output for the four new nodes; `search_plan.json` and the two Python scripts are sandbox-only working material and are not delivery nodes. No Lean was written or compiled. No library proof is claimed complete by this stage-1 split. Four new support nodes remain to be split; no new Mathlib leaves.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, punctured spectra, branches, excellent rings and normalization did not find a project declaration giving all clauses. The upstream master checkout was not treated as proof evidence.

## Wanted literature

WANTED: `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-exc-punctured-curve-branches.md`, proof paragraphs 1--3, for lem-exc-punctured-curve-branches. The local blueprint directory is absent; the complete imported statement and proof are preserved in its original node, and the chapter and unit records were read.

WANTED: `literature/stacks-project/more-algebra.tex`, 07QT (definition-excellent), 07P7 (definition-J), and `algebra.tex`, 00NI (definition-catenary), 00NL (definition-universally-catenary), for def-exc-excellent-ring.

WANTED: `literature/stacks-project/more-algebra.tex`, 07QV (lemma-quasi-excellent-nagata), for lem-exc-quasi-excellent-nagata.

WANTED: `literature/stacks-project/more-algebra.tex`, 07QU (lemma-finite-type-over-excellent), for lem-exc-finite-type-localization-excellent.

WANTED: `literature/stacks-project/varieties.tex`, 0C3R (lemma-pre-pre-delta-invariant), for lem-exc-local-curve-principal-total-fractions.

WANTED: `literature/stacks-project/varieties.tex`, 0C3S and 09N2, `algebra.tex`, 04GH and 00PD, and `schemes.tex`, 01I3, for verification of lem-exc-punctured-curve-branches.

These files are absent on this machine. I read the official Stacks HTML pages online, without installing or downloading literature into the project. The source labels were checked against the upstream tags/tags mapping. The constructed proof is marked `proof_origin.by = agent`, as required when its local literature files are missing. Official pages read: https://stacks.math.columbia.edu/tag/07QT, https://stacks.math.columbia.edu/tag/07P7, https://stacks.math.columbia.edu/tag/00NI, https://stacks.math.columbia.edu/tag/00NL, https://stacks.math.columbia.edu/tag/07QU, https://stacks.math.columbia.edu/tag/07QV, https://stacks.math.columbia.edu/tag/0C3R, https://stacks.math.columbia.edu/tag/0C3S, https://stacks.math.columbia.edu/tag/09N2, https://stacks.math.columbia.edu/tag/04GH, https://stacks.math.columbia.edu/tag/00PD. 01I3 is also independently backed by the existing Mathlib leaf's open-immersion statement.

## Corrections to the imported proof

There is no statement dispute: the reduced, excellent, dimension-exactly-one and algebraically closed residue-field hypotheses suffice. The characteristic assumption is preserved although the algebraic proof works in any characteristic.

The imported reference to `lemma-weil-pbc-finite-stalk-formula` did not state finite-algebra decomposition, henselianity of the local factors, or finite residue extensions. It is removed from proof_deps. The exact existing statement `lem-weil-pbc-finite-over-henselian-local-product` supplies all those assertions. The old convention-collection node `def-weil-pbc-scheme-conventions` does not supply localization and normalization theorems; it too is removed from proof_deps.

The finiteness assertion is obtained componentwise from Nagata and N-2 as actually defined by the existing nodes, rather than hidden in a reference to 0C3S. The existing semilocal normalization theorem supplies normality, Noetherianity, dimension and fraction field, instead of unquoted dimension-preservation assertions. The one-dimensional normal-domain DVR criterion is reused, not recreated.

I initially considered a citation to the basic-open homeomorphism node; its statement concerns only topology. The final step instead cites the scheme open-immersion leaf and the finite affine coproduct leaf, so the conclusion is an isomorphism of schemes over Spec R. In the new excellence definition I replaced a loose saturated-chain formulation with an explicit finite bound on all chain lengths, and corrected preliminary tag guesses against the actual tag index before finalizing the nodes.

The chapter and unit records are unchanged. The item's imported normalization/local-branch route is retained; tool uses only supply generic commutative algebra already implicit in that route. The item is not the unit key node, so no unit realization record is delivered.

## Not duplicates

The full DAG was searched by concepts and Stacks tags, and `tools/blueprint_refs.py search` was run for excellent, quasi-excellent, catenary, Nagata, normalization, DVR, total ring of fractions and principal localization. The ancestor command returns the item itself with no via nodes.

- def-exc-excellent-ring vs def-weil-pbc-g-ring: excellence additionally requires J-2 and universal catenarity; the existing G-ring definition supplies only the geometrically regular formal-fibre condition and is cited rather than copied.
- lem-exc-quasi-excellent-nagata vs def-weil-pbc-nagata-ring: the latter defines Nagata; it does not assert that quasi-excellence implies it.
- lem-exc-finite-type-localization-excellent vs lem-weil-pbc-nagata-localization: preservation of Nagata under localization is weaker than preservation of excellence for finite type algebras and their localizations.
- lem-exc-local-curve-principal-total-fractions vs lem-weil-pbc-reduced-noetherian-total-ring-fractions: the existing theorem decomposes the total fraction ring, but does not construct a parameter f with R_f equal to that ring. Both statements are used, without duplicating the decomposition.
- lem-exc-local-curve-principal-total-fractions vs lem-sc-local-domain-dim-one-principal-localization-fraction-field: the existing theorem assumes a domain and a chosen nonzero f; the new theorem permits several minimal primes and supplies f and its maximal-ideal radical. It is not a specialization of the domain result.
- lem-exc-local-curve-principal-total-fractions vs lem-exc-punctured-curve-branches: the new statement is only a parameter and localization theorem for reduced Noetherian local rings. It neither constructs DVR models nor asserts excellence, henselianity, residue-field equality, or a scheme coproduct. The item's steps derive those additional assertions from several independent existing statements.

- def-exc-excellent-ring vs lem-exc-field-algebra-strict-henselization-excellent: the existing statement proves excellence for localizations, strict henselizations, and quotients of finite-type field algebras; it expands excellence inline but does not define quasi-excellence, the hypothesis of the Nagata theorem. The new statement-only definition supplies both predicates with their general Noetherian, G-ring, J-2, and catenary meanings and no strict-henselization permanence assertion.
- lem-exc-finite-type-localization-excellent vs lem-exc-field-algebra-strict-henselization-excellent: the existing theorem only treats a localization of a finite-type field algebra, its strict henselization, and quotients of that strict henselization. The new 07QU theorem handles finite-type algebras over every excellent base ring, including the given arbitrary excellent local ring R; the existing theorem cannot be applied to that R.

## Review by NU

I read the imported item in full, the chapter and unit records, the three-level contract in SETUP, and delivery-errors B--E. I compared the original normalization argument with the official Stacks 0C3S and its preceding parameter lemma 0C3R. I also read 09N2 for the domain normalizations, 04GH for finite henselian algebras, and 00PD for the DVR criterion. The four new nodes have source statements only, not hidden proof sketches: 07QT with 07P7/00NI/00NL defines the added notion; 07QV is the Nagata input; 07QU supplies excellence of the finite algebras; 0C3R supplies the parameter with total-fraction localization. These are general inputs strictly below the item, not new names for its conclusion.

Step 1 uses the branch definition for its actual product construction, the excellence definition for Noetherianity, the finite-minimal-primes statement for finiteness of its index set, and the dimension definition. The local quotient has exactly the two primes p_a and m/p_a: inverse image gives the correspondence, and a third prime would violate dimension one. The quotient is Noetherian by the ascending-chain condition. This checks every hypothesis of the semilocal normalization statement used later.

Step 2 uses the new quasi-excellent-to-Nagata theorem and then the exact clauses of the existing Nagata and Japanese-domain definitions: each domain quotient is N-2, and the identity extension K_a/K_a gives finite integral closure. The finite-module definition justifies lifting quotient coefficients and the coordinate spanning family for the product. No excellence-of-normalization theorem is silently assumed.

Step 3 uses only `lem-sc-semilocal-dim-one-normalization`. I checked its whole statement: it explicitly gives a Noetherian integrally closed domain of dimension one and the same fraction field, rather than merely defining normalization. Its hypotheses were all established in step 1. This is a generic tool use from a different unit, recorded in split_report.

Step 4 uses the exact finite-henselian-product statement, not the proof of the imported sheaf-stalk node. Finite generation from step 2 and henselianity from the original strict henselian hypothesis are in force. The domain idempotent equation rules out more than one nonzero factor, and a nonzero domain rules out the empty product. The cited statement also supplies a local R-map and a finite residue extension. Algebraic closedness, stronger here than separable closedness, makes every minimal polynomial linear, proving that the structural residue map is an isomorphism. Thus both strict henselianity and the claimed same residue field are justified. I kept the distinction between algebraically closed and merely separably closed residue fields; no purely inseparable extension was discarded under a weaker hypothesis.

Step 5 uses the actual statement of `lem-sc-normal-dim1-dvr`. Dimension is exactly one, as supplied by step 3, not merely at most one, so no field factor is incorrectly called a DVR. This too is recorded as a generic tool use.

Step 6 derives finite type directly from finite module generators and then applies the new 07QU statement with the trivial localization. The algebra structure is the given R-map. Thus no hypothesis about essentially finite type or regularity is introduced.

Step 7 uses the full new parameter statement, including reducedness and dimension exactly one, and the existing total-fraction decomposition statement, whose hypotheses are reducedness and Noetherianity. The latter says p_a R_{p_a}=0 and that each localization is a field; the quotient/fraction-field identification is written out in the step. Its kernel argument is in the right direction, and its maps all agree with the R-structure maps. The total-fraction decomposition is recorded in split_report.tool_uses as a generic tool from sk-thm-p1; the item keeps its own local-curve argument. The fields are consequently the fraction fields of the actual N_a factors of B(R), not merely an unrelated family of fields.

Step 8 uses the existing open-immersion leaf, whose statement includes image D(f), and the existing finite affine coproduct leaf, whose statement specifies the coprojections as Spec of the ring projections. They supply a scheme isomorphism with the required maps. The finite index hypothesis was established in step 1. Whole statements in citations.json are verbatim quotes, and every non-elementary step input is a node actually present in the DAG or this sandbox. The proof union is exactly proof_deps; no source tag is used as a substitute for a node.

For small cases I checked a single complete branch k[[t]], the nodal complete local ring k[[x,y]]/(xy), and the cusp k[[t^2,t^3]], with algebraically closed k of characteristic p. They respectively give one DVR, two DVRs, and a finite normalization into k[[t]]. At the node one must take a parameter such as x+y, not x: x vanishes on a minimal prime, illustrating why the parameter condition is retained. The field and zero-ring cases are excluded by dimension exactly one for the local-curve statement, while the generic excellence localization statement allows S containing zero and hence the zero ring. A finite algebra over a field can have several local factors, so I used the domain argument rather than incorrectly claiming all finite algebras over a henselian ring are local. I also checked that no f in the maximal ideal can be a unit in its local DVR branch.

Mathlib semantic searches were run twice with distinct phrasings for every new node, plus Loogle, source grep and LeanSearch through msearch. LeanSearch returned HTTP Internal Server Error in every query and is recorded unavailable. LeanFinder returns ordinary Noetherian-local properties, smooth loci, finite type localization, and the domain-only dimension-one parameter criterion; none supplies excellence or the full reduced-ring parameter existence theorem. I read the relevant candidate source statements, including KrullDimension/LocalRing.lean:20, LocalProperties/Semilocal.lean:97, Smooth/Locus.lean and RingHom/EssFiniteType.lean:49, and rejected these as matches for the stated reasons. No leaf is invented and no unrun search is recorded.

## Unfinished work and validation

The four new nodes are deliberately unsplit, in accordance with the one-level delivery rule. There is no unresolved mathematical gap in the item's proof given their statements and the cited existing nodes. The required delivery dry run is the final validation; its result will be recorded below. This worker does not push or deliver.

## Second reading by NU

I independently reread the imported item, every new node, every cited node statement, and the Stacks pages for 0C3R, 0C3S, 07QT, 07P7, 07QV, 07QU, 00PD, 04GH, 09N2, 00NI, and 00NL. The source pages agree with the imported hypotheses and clauses: reduced one-dimensional Noetherian local input for 0C3R/0C3S, quasi-excellent/Nagata and finite-type excellence for 07QV/07QU, and the normal one-dimensional local DVR criterion for 00PD.

- Step 1: checked the quotient-by-minimal-prime construction against 0C3R and the statements of `def-exc-local-curve-branches`, `def-exc-excellent-ring`, `lem-weil-pbc-noetherian-finitely-many-minimal-primes`, and `def-weil-pbc-krull-dimension-ring`; the prime correspondence, Noetherian quotient, and exact dimension-one argument are present.
- Step 2: checked 07QV and the Nagata/N-2/Japanese statements; taking the identity fraction-field extension gives finite normalization, and the finite-index product generator argument is explicit.
- Step 3: checked 09N2 through the exact statement of `lem-sc-semilocal-dim-one-normalization`; all semilocal, Noetherian, domain, dimension, and fraction-field hypotheses are supplied.
- Step 4: checked 04GH and the henselian terminology; the domain idempotent argument forces one factor, and finite residue extensions of the algebraically closed residue field are proved trivial before strict henselianity is invoked.
- Step 5: checked 00PD; the conclusion has dimension exactly one and is a Noetherian normal local domain, so the field exception cannot occur.
- Step 6: checked 07QU; finite module generators give finite type, and the trivial localization gives excellence of each normalization factor.
- Step 7: checked 0C3R and the full statement of `lem-weil-pbc-reduced-noetherian-total-ring-fractions`; the kernel/surjectivity comparison identifies each minimal-prime localization with the corresponding fraction field, and the maps are tracked over $R$.
- Step 8: checked 01I3 as represented by `lem-weil-pbc-principal-localization-open-immersion` and the finite affine coproduct statement; the conclusion is an isomorphism of schemes over `Spec R` with the stated coprojections.

- `def-exc-excellent-ring`: checked B1--B7, including the expanded J-2 and catenary definitions against 07QT, 07P7, 00NI, and 00NL; verdict correct and self-contained.
- `lem-exc-quasi-excellent-nagata`: checked the exact 07QV statement and its definition dependencies; verdict correct and strictly below the item.
- `lem-exc-finite-type-localization-excellent`: checked the exact 07QU statement, finite-type and localization notions, and the $S=\{1\}$ specialization; verdict correct.
- `lem-exc-local-curve-principal-total-fractions`: checked the reduced local-curve assertion against 0C3R, including the nonzerodivisor, radical, and total-fraction localization clauses; verdict correct.

The three small cases from the first review were rechecked: $k[[t]]$ gives one branch, $k[[x,y]]/(xy)$ gives two branches with a parameter such as $x+y$, and $k[[t^2,t^3]]$ gives one finite normalization branch. The zero ring and dimension-zero cases are outside the item's exact dimension-one hypotheses; the finite-product and identity-localization edge cases were checked in steps 2, 4, 6, and 8.

No change to the item's mathematical statement was needed. I retained the worker's four support nodes; the worker's report already records the removal of the inapplicable finite-stalk citation and the replacement by the exact finite-henselian-product statement. I added this source-by-source second-reading record and confirmed that `citations.json` quotes the complete statement of every cited node.

Changes made by the second reader:

- Step 1 now proves quotient Noetherianity directly by lifting an ideal and projecting its finite generating family; this uses the cited Noetherian definition without silently passing through its ascending-chain equivalence.
- Step 7 now gives the formula on $r/f^n$ and the fraction-field comparison on $x/y$, citing the localization definition. Step 8 explicitly cites affine-spectrum functoriality. These replace an unsupported shorthand about compatibility by the maps themselves.
- The parameter node spells out “nonzerodivisor” and the ideal radical inline, and citations.json was regenerated for the actual 21 citations, including the two added definition citations.
- I ran separate msearch LeanFinder queries for every new node (more general algebraic vocabulary), plus `IsExcellent|IsQuasiExcellent|IsCatenary|IsNagata|IsJapanese` by source grep and `"nonZeroDivisors", "Away"` in Loogle. The latter two returned zero hits. The new semantic results are preserved verbatim as msearch log records in each node. `IsIntegralClosure.finite` was inspected in `Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`: it requires integrally closedness and separability, which do not establish quasi-excellent implies Nagata. The returned dimension-one parameter criterion in `KrullDimension/LocalRing.lean:20` assumes a domain and does not give the reduced multi-branch parameter theorem.
- Full-DAG searches by the actual new tags returned no theorem stating either required general input. `blueprint_refs.py search` independently found only this item and `lem-exc-dvr-galois` for excellence, no catenary or total-fraction blueprint theorem; the ancestor is this item. The existing prime-avoidance node was also read: it only chooses an element outside the minimal primes, and does not supply the radical and total-fraction localization clauses. Thus the parameter node retains non-elementary content and is not an elementary wrapper.
- The local `literature/stacks-project` directory remains absent. For this second reading only, I fetched the official Stacks repository's `algebra.tex`, `more-algebra.tex`, `varieties.tex`, `schemes.tex`, and tag index into the sandbox's `source-reading/`, and opened every cited source label there. Labels and statements agree with the worker's sources; the report's earlier WANTED section remains a record of what was available to the first worker. The existing normalization node's source record says algebra.tex for 09N2, while its actual label is in varieties.tex; the delivery's step 3 uses the correct file.

- The excellence definition's source now explicitly names `definition-catenary` (00NI) and `definition-universally-catenary` (00NL) in algebra.tex, replacing the earlier claim that their labels had been verified without writing the labels.

- A further independent parameter search, “Localization away from a regular element in a ring of dimension at most one is a field or a product of fields”, returned dimension-preservation for domain localizations and the reduced-local-zero-dimensional field criterion; neither states the reduced-ring parameter theorem. Its full output is retained in the new node.

- The first completed delivery dry run returned a shared-tag report requirement for `lem-exc-field-algebra-strict-henselization-excellent` (07QT/07QU). I opened that node and added both explicit distinctions under Not duplicates. It cannot supply quasi-excellence or finite-type permanence over an arbitrary excellent local base; no node was removed.

Validation: the required delivery dry run completed successfully: `OK (not pushed) deliver/NU/lem-exc-punctured-curve-branches at cef9e57903: preflight passed`. The delivery script's CLI accepts the group, item, and `--no-push` without the prose sentence's trailing period. No Lean source was written or compiled.
