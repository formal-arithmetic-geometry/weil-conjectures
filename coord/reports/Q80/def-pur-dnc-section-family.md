## Files written

- `dag/nodes/sec-smooth-purity/def-pur-dnc-section-family.json`: definition, split; statement unchanged; eight proof steps, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-pur-dnc-affine-blowup-complement.json`: statement-only affine blow-up/strict-transform chart lemma; Mathlib searches found no match.
- `dag/nodes/sec-smooth-purity/lem-pur-dnc-etale-rees-chart.json`: statement-only étale Rees-chart base-change lemma; Mathlib searches found no match.
- `citations.json`: 37 step/node entries with verbatim quotations from every cited statement.

## Attachments

None. The slopmaster2 `DeformationToNormalConeData` declaration carries abstract data and its existence theorem has `sorry`; `purityDncFamily` is a record-level definition with an `existing: false` audit and does not state the actual blow-up, strict-transform complement, or derived Picard family. No declaration under `WeilConjectures/` states this item exactly with a finished proof.

## WANTED

WANTED: none.

## What was repaired

The item statement and hypotheses agree with the current main-20261015 definition and the reviewed `def-pur-section-invariant` and `def-pur-conventions` statements. The earlier split was returned because proof steps 1 (2927 characters) and 4 (2083 characters) hid independent lemmas. I kept their route and replaced each with short applications of a new statement-only node. Step 1 now separates the global finite-presentation/closure setup from the affine chart lemma. Step 4 now cites the étale Rees-chart lemma for the flat tensor calculation and retains a separate short coverage argument for the zero fibre and punctured chart. No source statement was weakened or changed.

I searched the whole DAG and blueprint before creating either node. The affine helper is distinct from `pur9-def-deformation-space` because it is a local blow-up calculation for an arbitrary finitely generated ideal and explicitly computes the strict-transform complement; `pur9-def-deformation-space` is a definition of a relative extended-Rees object. The étale helper is distinct from `lem-pur-noetherian-etale-section-specialization` because it is only the local affine algebra/isomorphism and smooth chart conclusion, with no Noetherian global family, fibres, dualizing complexes, or normalized comparison. No new node restates the full item or a standalone item clause.

The item’s existing Mathlib searches were retained and the two new nodes were each searched with LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` using their own ids. LeanFinder/LeanSearch returned only generic Proj, Rees, flatness, étale, or smooth-base-change declarations; grep found ordinary `reesAlgebra` and generic flat/smooth files but no extended-Rees deformation theorem; Loogle returned no usable match (the first query reported the unknown identifier `ReesAlgebra`). These are recorded in each node’s `mathlib_searches` and corresponding `searches.jsonl`.

## Review by Q80

I read the current item, `sec-smooth-purity` chapter, `sk-def-purity-conv` unit, the current and master blueprint copies, and every statement cited by the eight final proof steps. I also read the Stacks passages used by the affine calculation (divisors.tex Tags 01OG, 0804, 080D) and checked that the current source path is the main-20261015 definition. The slopmaster2 source was inspected for the candidate declarations and for `sorry`; no finished attachment exists.

Step 1 uses the global blow-up and strict-transform definitions, their gluing/local-model statements, Noetherian finite-type and finite-generation facts, the closed-immersion ideal sheaf, finite-presentation and affine permanence, scheme conventions, and the schematic-closure/kernel statements. Those statements provide exactly the global reduction and centre hypotheses claimed in the shortened text. The new `lem-pur-dnc-affine-blowup-complement` statement introduces its own ring, ideal, affine scheme, blow-up centre and charts. It states the t-chart, each f_i-chart, the strict-transform equation v=0, and the overlap/complement identification used by step 2. Its statement is strictly local and does not define the whole deformation family.

Step 3 is the Laurent-coefficient augmentation. I rechecked that every element of `R[t,I/t]` has the stated finite Laurent form, that terms with negative exponent have coefficients in the required ideal power, and that mixed products vanish after reduction modulo I. The affine-spectrum and surjective-ring-map criteria cited there give the closed section and its identity with the projection; localization makes the maps glue. This remains elementary after the chart lemma is extracted.

Step 4 uses the étale local normal form, affine-target and affine-permanence criteria, the separated étale section/clopen statement, and the closed-immersion and diagonal definitions. I checked the order of hypotheses: the initial affine coordinate map is shown separated before the clopen-section result is applied; translation sends the section to zero; removing the other clopen component makes the inverse-image ideal equal to the actual section ideal `(x_i)R`; affine refinements and principal base shrinks preserve these properties.

Steps 5 and 6 use the new `lem-pur-dnc-etale-rees-chart` statement and the existing smooth base-change/affine-locality and finite-type/separatedness statements. The new node introduces A, C, R, I, E and D and states exactly the canonical tensor identification, the substitution `x_i=t u_i`, étaleness of the chart map, and smoothness of its affine-line projection. Its hidden algebra is the flat-tensor injection and distinct Laurent monomial argument from the blueprint clause; it is left as a statement-only child as required by stage 1. Step 7 then checks finite generators, affine separatedness, the separated finite-type product projection, the diagonal factorization, and finite type over k. The zero-fibre coverage in step 6 is the elementary identity `f=t(f/t)` together with the new chart conclusion, while the punctured part is the cited smooth base-change statement.

Step 8 applies the full current `def-pur-section-invariant` and `def-pur-conventions` statements. I verified that steps 1–7 provide a smooth, separated, finite-type morphism between finite-type k-schemes and a closed section satisfying the identity. The section-invariant statement supplies the actual derived pullback and tensor-invertible finite-Tor object; conventions supply the coefficient units and uniform integral conditions. No orientation, twist comparison, or abstract DNC datum is introduced.

I checked delivery-errors B–E: both new nodes are self-contained statement-only leaves with no proof sketch; all notions used in their statements have statement dependencies; their Mathlib searches are real and recorded; no duplicate or clause-restatement is claimed; every non-elementary input in each final step is a cited node whose statement supplies the quoted fact; no cycle is introduced; and the two formerly long steps are now below 2000 characters. Small cases checked include `I=0` (identity section), `I=R` on a component disjoint from the section, d=0 and d=1 affine-space zero sections, nilpotent rings, empty schemes, and varying local dimensions. The chart and augmentation formulas remain valid in all of them. No Lean was written, compiled, or modified.


## Continuation repair and final cross-check

The retained sandbox already contained the requested two-node extraction; I compared it with the current shared repository, where the returned six-step proof is still present. The item statement and the complete `lean` record are byte-for-byte unchanged as JSON values. The retained repair is substantive: former step 1's affine strict-transform computation is now the statement of `lem-pur-dnc-affine-blowup-complement`, applied in step 2; former step 4's flat tensor/coordinate calculation is now the statement of `lem-pur-dnc-etale-rees-chart`, applied in step 5. Both children remain unsplit and carry no proof. The other arguments retain the returned proof's route. All eight steps are below 2000 characters.

The first dry run of this continuation rejected three recorded search queries because they differed from searches.jsonl. I read that retained log and corrected the node records to the exact previously run queries and actual results, including Loogle's unknown-identifier response. The retained LeanFinder and LeanSearch queries give the two semantic phrasings, so an invalid Loogle name is not treated as evidence of mathematical absence. Ordinary `reesAlgebra` in Mathlib/RingTheory/ReesAlgebra.lean defines a subalgebra of polynomials and finite generation, not either extended-Rees identification. The original logged searches and citations were retained.

I reread divisors.tex, definition-blow-up and lemma-blowing-up-affine (0804), and definition-strict-transform (080D), and the current blueprint definition and geometry clause (2). In the new affine helper I corrected the reversed spectrum containment: it is the algebra R[t,I/t] that embeds in Laurent polynomials; Spec of that algebra is the complement chart. This changes no assertion of the item. For a zero divisor f_i the chart algebra C sits inside R localized at f_i, so multiplication by f_i is injective on C and the closure kernel is still (v). If I is nilpotent those f_i charts are empty; if I=0 the t-chart is the whole original affine scheme and the strict transform is empty. If I=R the complement is precisely the punctured original affine scheme. These cases confirm the arbitrary-ring hypothesis in the new child. The étale helper uses flatness, not regularity or a domain hypothesis: tensor preserves the inclusion E into Laurent polynomials, and its image is exactly D. The distinct Laurent monomial argument works over the zero ring and rings with nilpotents; d=0 is the polynomial extension R[t].

I opened every statement cited in the final proof again. Steps 1 and 2 use the global gluing/local-model definitions and the affine helper exactly for the global-to-local reduction and complement identification; step 1 now explicitly supplies the elementary Noetherian-field argument. Step 3 uses only the contravariant Spec and affine quotient criterion after its explicit Laurent augmentation calculation. Step 4 applies the separated étale section theorem only after verifying separatedness of the affine coordinate map, then removes the other clopen component before identifying the section ideal. Step 5 uses exactly the tensor identification and smooth projection stated by the new étale helper. Step 6 uses its smooth charts at t=0 and the existing smooth base-change clause on the punctured line. Step 7 uses affine permanence, finite algebra generators, separated finite-type base change, and the displayed diagonal argument. Step 8 uses the full section-invariant statement, which supplies invertibility, and the coefficient conventions only for their coefficient domains. I corrected the internal step references and the earlier report's stale step numbering; the final citation numbering already matches all eight steps and each quote was checked against its cited statement.

## Not duplicates

lem-pur-dnc-affine-blowup-complement vs pur9-def-deformation-space: the latter defines a relative extended-Rees spectrum for a smooth section; the new statement proves the local blow-up/strict-transform complement identification for an arbitrary finitely generated ideal.

lem-pur-dnc-affine-blowup-complement vs lemma-nagata-strict-transform-chart-closed: the latter gives a closed immersion from a torsion quotient chart; it does not compute the strict transform as v=0 for the centre (I,t), or its complement as the t-chart.

lem-pur-dnc-affine-blowup-complement vs prop-nagata-strict-transform-chart-iso: the latter identifies an already constructed strict-transform comparison with a blow-up chart of the transformed subscheme; it does not identify the ambient complement with an extended-Rees chart.

lem-pur-dnc-etale-rees-chart vs lemma-nagata-flat-pullback-rees: the latter identifies an ordinary graded Rees-algebra pullback; the new statement identifies the extended-Rees subalgebra in Laurent polynomials with a polynomial étale base change and states the resulting smooth projection.

lem-pur-dnc-etale-rees-chart vs lem-pur-noetherian-etale-section-specialization: the latter assumes Noetherian global schemes, a regular section, compactifiability and finite étale coefficients and concludes global geometry plus normalized derived comparisons. It neither states the arbitrary-ring affine tensor identification nor can be applied here without additional hypotheses and global DNC data.

## Unfinished work

None in this one-level repair. The two new lemma statements join the stage-1 queue for their own splits. No Lean was written or compiled.

The next preflight required inline notion citations in both new statements. I added precisely the existing affine-spectrum, blow-up, strict-transform, closed-immersion, étale, affine-space and smoothness definitions, and trimmed each new node’s statement dependencies to the notions its statement actually uses. The two children remain statement-only; the extracted argument is documented above rather than inserted as their proof. I refreshed their verbatim citation quotes.
