# Q160: repair of lem-trf-proper-integral-curve-ample-degree

## Files written

- dag/nodes/sec-trace-formula/lem-trf-proper-integral-curve-ample-degree.json: unchanged statement; repaired split, five steps and 2486 proof-text characters.
- dag/nodes/sec-trace-formula/lem-trf-positive-degree-affine-section.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-affine-section-ideal-twist-h1-vanishing.json: statement, unsplit; no Mathlib match.
- citations.json: a literal statement quotation for every citation of every current parent step.
- report.md: report, repair accounting, mathematical review and full retained argument.

Two new nodes, zero Mathlib leaves. Both new nodes have empty proof and proof_deps and null proof_origin. They inherit the chapter, unit and blueprint ancestry. No Lean source or unit record was changed.

## Attachments

None. The exact blueprint-id search of lean/WeilConjectures returned no declaration. The project's Sheaf.AlgebraicGeometry.ProperIntegralCurveAmpleDegree declaration proper_integral_curve_isAmple_iff_degree_pos has its entire proof sorry. The current upstream AlgebraicGeometry.Scheme.isAmple_iff_degree_pos at lean/WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1656 is in the Curve section whose context at lines 249-250 assumes SmoothOfRelativeDimension 1; it also explicitly assumes GlobalSectionsBijective k X and uses relative very-ampleness. It cannot attach to the arbitrary proper integral curve and absolute ampleness statement. The related isAmple_of_degree_pos at line 1634 has the same obstacle. Searches of the Ample and cohomology sources do not state either new lemma.

## WANTED

None: varieties.tex and coherent.tex are available locally.

## Resumed landing repair (2026-10-23)

I resumed the retained Q160 work after the provider interruption. The previous dry-run process had exited and its durable receipt recorded head 629825ae6b4; I checked that no delivery process for this item remained before invoking another dry run. The fresh current-server run exited 0 and printed OK (not pushed) at 6a62bf2244c. That is validation only; the final delivery still follows a fresh dry run after this report update.

The return asks for promotion onto the current live DAG, with changed cited nodes re-read and the split adjusted. Comparing the current read-clone parent with the sandbox shows differences only in proof, proof_deps and split_report. The repair's substantive current-DAG adjustment remains Step 1's reuse of lem-trf-proper-field-invertible-coherent instead of rederiving its conclusion from older inputs. I re-read that statement: a field, a proper scheme and an invertible module suffice for Noetherianity and coherence, and these hypotheses hold here without using dimension or integrality. I also re-read every current parent citation and both new statements' definition dependencies. All 16 quote records cover exactly the current step uses and are verbatim substrings. The unchanged tensor-additivity statement applies to dimension at most one; the unchanged section-positivity statement gives strict positivity for a nonzero section whose locus is proper; the unchanged ideal-twist criterion allows a different positive exponent for each ideal. No changed hypothesis requires a further route change.

I read Stacks varieties.tex lemma-ample-curve (0B5X) in full and coherent.tex lemma-coherent-support-dimension-0 (0B3J), lemma-section-affine-open-kills-classes (01XR), and lemma-vanshing-gives-ample (0B5U). Their fixed-section multiplication, zero-dimensional cokernel, class-annihilation and positive-exponent quantifiers match the two extracted statements and the final assembly. I reopened the project's theorem, whose proof is sorry, and the upstream RiemannRoch Curve context and ampleness criterion: the upstream result assumes smooth relative dimension one and GlobalSectionsBijective, so still cannot attach. The old argument is retained below without loss. The parent has five steps totaling 2486 characters; the largest is 692, so no step exceeds 2000.

The repeated whole-DAG 0B5X search found five further nodes carrying that tag in proof/search context; I opened their full statements and added the pairwise explanations below. Filtration multiplicities, closed-point witnesses, closed-subscheme tests, and Euler differences neither construct the prescribed affine-locus section nor establish ideal-twist H1 vanishing. The whole-blueprint searches for affine section and ideal twist yielded no equivalent statement, and the ancestor remains lem-trf-local-term-locality. Both proposed new ids are still absent live. I read the retained actual Mathlib responses and search log rather than repeating unchanged search questions. The two statement-only nodes and their logged searches are retained unchanged.

Small-case checks remain valid: O(d) on the projective line supplies a section only in the positive-degree case; the constant section of O has full, nonaffine locus and does not satisfy the second lemma's affine-locus hypothesis; the zero ideal and a zero initial H1 allow E=1; nonrational closed points retain residue-field degrees; and singular integral curves have the domain stalks used by the retained argument. No statement correction or additional source is needed. This report update supersedes the historical counts and pre-substitution Step 1 descriptions below, while retaining them as the requested history.

## Renewed current-DAG repair (2026-10-22)

The first dry run of this resumed repair exited successfully at 12d8fa4c526. I then made a further substantive adjustment against the current DAG rather than re-pushing that head unchanged. Current node lem-trf-proper-field-invertible-coherent states exactly the proper-field Noetherianity and coherence preparation that the retained Step 1 previously derived from finite-type-over-Noetherian and coherent-ft-locnoeth. I read its complete statement and source record (Stacks 01XZ and 01T6), checked its hypotheses field/proper/invertible against this item, and checked its transitive statement/proof dependencies: none reaches this parent. Step 1 now cites this same-unit lemma directly; the finite-type-over-Noetherian, coherent-ft-locnoeth and invertible-definition proof citations and their now-unused tool-use declarations are removed. The statement dependencies and the statement itself remain unchanged.

For citation check C4, its conclusion explicitly says that Y is Noetherian and that N and O_Y are coherent, precisely the three assertions Step 1 takes. The remaining Step 1 uses are integral-scheme for nonemptiness, proper-morphism and curve for the variety convention, and the Noetherian-ring definition for the direct two-ideal field argument. All later steps and both extracted statements are retained, and every old Step 1 argument still appears verbatim in the preservation section. I regenerated citations.json for the adjusted uses; every quotation is a literal substring of its current cited statement. The parent now has 2486 proof-text characters, with no step over 2000. This supplements the historical rebase review below; its earlier account of the retained Step 1 describes the pre-adjustment version.

## Repair of the landing refusal (2026-10-22)

The latest return says the previous reader approved the delivery but landing refused an unpromoted side-project completion. This repair continues the retained Q160 sandbox rather than recreating its nodes or searches. The interrupted initial dry run completed and wrote head 71a0fac2b1c to .stage1-ready.json; that was a dry run, not a push. The delivery tool constructs its commit on the current origin/sheaf-dag and preserves current maintainer-owned fields.

I compared the retained parent with the current read-clone node field by field: only proof, proof_deps and split_report differ. In particular the statement, statement dependencies, blueprint fields, source, historical searches, Lean declaration and review metadata agree. The current live node still contains the original nine-step argument; both new ids are absent from the live DAG. Thus the requested two-node redistribution remains necessary, and this delivery promotes it onto the live DAG rather than relying on a side completion. I updated the parent's split_report to record this comparison; this report is also changed from the returned delivery.

I re-read every current statement cited by the five parent steps and checked every quotation in citations.json against it. All quotations remain verbatim. Properness still includes finite type and separatedness, the integral-scheme definition supplies nonemptiness, finite-type-over-Noetherian supplies Noetherianity, and coherent-ft-locnoeth supplies coherence. The tensor-additivity lemma still covers dimension at most one. Clause (1) of h0-proper-variety still supplies a finite extension field without requiring geometric integrality. Section-degree-positivity still applies to a nonzero section with a zero. The final ideal-twist criterion still requires only one positive exponent per ideal, precisely the product En supplied by the two retained new statements. No changed cited statement forces a mathematical alteration. I also re-read both new statements' definition dependencies, including quasi-coherence, cohomology and tensor powers, and Stacks 0B5X, 0B3J, 01XR and 0B5U; the earlier detailed review below remains applicable.

The current same-tag search additionally found proper-field-invertible-coherent and curve-pullback-tensor-euler. Their statements give finiteness/coherence preliminaries and an Euler-characteristic identity respectively, not either extracted construction; the duplicate accounting below includes both. The project Lean criterion still has its entire proof sorry, while the upstream criterion still requires smoothness and GlobalSectionsBijective, so neither supplies a new attachment. The retained search responses were read and reused because neither new statement nor its search question changed. All parent steps remain below 2000 characters and their total remains 2687; no source argument was removed from the preservation section.

## Repair of the return

The sandbox initially contained only dispatcher marker files, no node, report or search log. I read the current live node and its nine-step proof as the returned mathematical work, rather than reconstructing a different proof. The existing parent statement, historical searches, created record, Lean records, blueprint fields and maintainer-owned metadata are retained. The historical Q55 report is retained below for its previous citations and search descriptions; its historical filenames and line numbers refer to that earlier run, not the current new-node inventory.

The human requested a genuine distribution of work, at least two comparable independent statement-only nodes and at most 3000 parent proof characters. The first new work item takes the positive-degree growth/evaluation/affine-locus argument of old Steps 4-5 (1827 characters). The second takes the injectivity/support/surjectivity/finite-basis argument of old Steps 6-8 (2561 characters). Neither asserts ampleness or restates a direction of the parent's equivalence. These are separate geometric and cohomological arguments that can be developed independently. Old Steps 1-3 remain the prerequisite and forward assembly; old Step 9 is the final application of the existing cohomological ampleness criterion. The tensor-power calculation from old Step 2 is also recorded as the growth calculation the first new worker needs. The repaired parent's five steps total 2687 characters, all below 2000 individually.

No old argument is discarded or replaced by an unexplained summary: the entire nine-step text, all uses and source places are copied verbatim in the preservation section below. This explicitly preserves Noetherian/coherence preliminaries, exponent-zero induction, the nonaffineness argument, residue degrees, the evaluation-kernel argument without surjectivity, stalk injectivity, zero-dimensional support, the long exact sequence, the common positive exponent including the zero-vector-space case, and the exact quantifier in the converse criterion.

No statement dispute was found. The source means an integral curve; there is no need to impose smoothness, normality, algebraic closure or geometric integrality. The new cohomological lemma makes no positivity assumption at all: its input is the already constructed nonzero affine-locus section.

## Searches and source route

I searched the whole DAG by Tag 0B5X, by affine/nonvanishing/section, by positive degree and by ideal/cohomology/vanishing. I opened every same-tag existing statement, especially the component-degree formula, section positivity, tensor degree additivity and converse ampleness criterion. I also inspected the section-annihilation and affine-local cohomology-fraction nodes: they kill individual classes, not the entire ideal-twist H1 group. The existing smooth/projective degree criteria have stronger hypotheses and do not produce either new statement without invoking the whole theorem being split. The two-section-pencil lemma assumes an ample projective curve and therefore cannot provide the positive-degree construction here. The reduced-dimension-one-ample lemma constructs some ample bundle, not a section of the prescribed positive-degree bundle.

Whole-blueprint searches through blueprint_refs.py for affine nonvanishing, ideal twist vanishing, positive degree, 0B5X, kills cohomology, affine section, ideal twist and ample degree found no equivalent blueprint statement. The ancestor command returned lem-trf-local-term-locality. Each new from.place retains the existing fibrewise-ampleness route and specifies the extracted paragraph of lemma-ample-curve; each via list prepends this item to the inherited list. same_as remains empty. The chapter and sk-i-curve-zero records were read and remain unchanged: this is a supporting lemma of the already established ampleness/projectivity chain.

For each new node msearch.py ran two LeanFinder phrasings, LeanSearch, Loogle and grep restricted to Mathlib/AlgebraicGeometry. All actual output is retained in the sandbox search response files and copied into mathlib_searches, with exact query strings and the shared searches.jsonl log. The first Loogle query used a namespace as though it were a constant and returned an unknown-identifier diagnostic. I recorded that as an invalid query, not evidence of absence, and ran a corrected pair of quoted name substrings; these returned no hits. No service was down. The semantic hits such as exists_of_res_zero_of_qcqs_of_top and exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen concern functions in the structure sheaf and restriction/localization. They neither construct a section from Euler-characteristic growth nor prove vanishing of an entire first-cohomology group of a twisted ideal. Grep's other hits concern Proj charts, elliptic-curve coordinate degrees and vanishing ideals; none is an exact match or one-line generalization. The parent's already recorded historical Mathlib searches are unchanged because its statement did not change.

## Unfinished work

The two new lemmas are intentionally unsplit statements for other workers. Their full source arguments and old input-node citations are preserved below. This delivery writes no Lean and invokes no compiler, Lake or local server-only check script. No work outside this stage-1 repair is claimed.

## Not duplicates

lem-trf-positive-degree-affine-section vs lem-trf-proper-integral-curve-ample-degree: the parent asserts ampleness if and only if positive degree; the new node isolates an intermediate construction and never asserts ampleness.

lem-trf-positive-degree-affine-section vs lem-trf-ideal-twist-vanishing-implies-ample: the existing node takes ideal-twist H1 vanishing as its hypothesis and concludes ampleness over a general Noetherian affine base; the new nodes supply intermediate input and never assert ampleness.

lem-trf-positive-degree-affine-section vs lem-trf-curve-euler-tensor-generic-rank: the existing node is an Euler-characteristic identity for coherent tensor products; it does not construct an affine nonvanishing locus or show a first-cohomology group is zero.

lem-trf-positive-degree-affine-section vs lem-trf-fibre-degree-ample-criterion: the existing node compares ampleness with degrees on normalized reduced components; the new nodes are arguments on a single integral curve and do not state any ampleness criterion.

lem-trf-positive-degree-affine-section vs lem-trf-degree-weighted-irreducible-components: the existing node computes degree on components with generic lengths, not sections or first cohomology of ideal twists.

lem-trf-positive-degree-affine-section vs lem-trf-curve-section-degree-positivity: the existing node deduces nonnegative degree, or strict positivity when a nonzero section has a zero; it neither constructs the needed section nor proves H1 vanishing.

lem-trf-positive-degree-affine-section vs lem-trf-curve-degree-tensor-additive: the existing node states degree additivity under tensor products, not an affine-locus section or ideal-twist cohomology vanishing.

lem-trf-positive-degree-affine-section vs lem-sc-positive-degree-ample: the existing node assumes a proper smooth connected curve over an algebraically closed field and concludes ampleness, unlike either new statement.

lem-trf-positive-degree-affine-section vs lem-pc-ample-positive-degree: the existing node is an ampleness-degree equivalence for a smooth projective curve; the new nodes concern intermediate statements on arbitrary proper integral curves.

lem-trf-positive-degree-affine-section vs lem-sc-ample-positive-degree: the existing node assumes ampleness over an algebraically closed field and concludes positive Hilbert degree, unlike either new statement.

lem-trf-positive-degree-affine-section vs lem-trf-affine-section-ideal-twist-h1-vanishing: the positive-degree node constructs a section with affine locus; the ideal-twist node assumes such a section and proves vanishing without any degree hypothesis.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-proper-integral-curve-ample-degree: the parent asserts ampleness if and only if positive degree; the new node isolates an intermediate construction and never asserts ampleness.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-ideal-twist-vanishing-implies-ample: the existing node takes ideal-twist H1 vanishing as its hypothesis and concludes ampleness over a general Noetherian affine base; the new nodes supply intermediate input and never assert ampleness.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-euler-tensor-generic-rank: the existing node is an Euler-characteristic identity for coherent tensor products; it does not construct an affine nonvanishing locus or show a first-cohomology group is zero.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-fibre-degree-ample-criterion: the existing node compares ampleness with degrees on normalized reduced components; the new nodes are arguments on a single integral curve and do not state any ampleness criterion.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-degree-weighted-irreducible-components: the existing node computes degree on components with generic lengths, not sections or first cohomology of ideal twists.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-section-degree-positivity: the existing node deduces nonnegative degree, or strict positivity when a nonzero section has a zero; it neither constructs the needed section nor proves H1 vanishing.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-degree-tensor-additive: the existing node states degree additivity under tensor products, not an affine-locus section or ideal-twist cohomology vanishing.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-sc-positive-degree-ample: the existing node assumes a proper smooth connected curve over an algebraically closed field and concludes ampleness, unlike either new statement.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-pc-ample-positive-degree: the existing node is an ampleness-degree equivalence for a smooth projective curve; the new nodes concern intermediate statements on arbitrary proper integral curves.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-sc-ample-positive-degree: the existing node assumes ampleness over an algebraically closed field and concludes positive Hilbert degree, unlike either new statement.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-positive-degree-affine-section: the positive-degree node constructs a section with affine locus; the ideal-twist node assumes such a section and proves vanishing without any degree hypothesis.

lem-trf-positive-degree-affine-section vs lem-trf-proper-field-invertible-coherent: the existing statement gives Noetherianity and coherence on a proper scheme over a field, not an affine-locus section or ideal-twist H1 vanishing.

lem-trf-positive-degree-affine-section vs lem-trf-curve-pullback-tensor-euler: the existing statement computes an Euler characteristic after pulling back a tensor product; it does not construct sections or annihilate first cohomology.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-proper-field-invertible-coherent: the existing statement gives Noetherianity and coherence on a proper scheme over a field, not an affine-locus section or ideal-twist H1 vanishing.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-pullback-tensor-euler: the existing statement computes an Euler characteristic after pulling back a tensor product; it does not construct sections or annihilate first cohomology.

lem-trf-positive-degree-affine-section vs lem-trf-curve-integral-filtration-multiplicity-profile: the existing node gives coherent filtrations and their generic-stalk multiplicity counts, not a section of a prescribed positive-degree line bundle or vanishing of ideal-twist H1.

lem-trf-positive-degree-affine-section vs lem-trf-curve-closed-point-twist-witness: the existing node describes the closed-point module i_*O_Z and its tensor Euler characteristic; it neither constructs an affine-locus section nor kills ideal-twist H1.

lem-trf-positive-degree-affine-section vs lem-trf-curve-integral-closed-tests: the existing node classifies integral closed subschemes and computes the O_C Euler difference; it has no affine-locus section or ideal-twist vanishing conclusion.

lem-trf-positive-degree-affine-section vs lem-trf-integral-filtration-euler-difference: the existing node computes Euler differences from a given coherent filtration, rather than constructing a section or annihilating H1 after a twist.

lem-trf-positive-degree-affine-section vs lem-trf-curve-euler-defect-additivity: the existing node states additivity of generic rank and Euler defect in exact sequences; it gives neither new statement.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-integral-filtration-multiplicity-profile: the existing node gives coherent filtrations and their generic-stalk multiplicity counts, not a section of a prescribed positive-degree line bundle or vanishing of ideal-twist H1.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-closed-point-twist-witness: the existing node describes the closed-point module i_*O_Z and its tensor Euler characteristic; it neither constructs an affine-locus section nor kills ideal-twist H1.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-integral-closed-tests: the existing node classifies integral closed subschemes and computes the O_C Euler difference; it has no affine-locus section or ideal-twist vanishing conclusion.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-integral-filtration-euler-difference: the existing node computes Euler differences from a given coherent filtration, rather than constructing a section or annihilating H1 after a twist.

lem-trf-affine-section-ideal-twist-h1-vanishing vs lem-trf-curve-euler-defect-additivity: the existing node states additivity of generic rank and Euler defect in exact sequences; it gives neither new statement.

## Review by Q160

On 2026-10-23 I performed the resumed landing review recorded above with the current statements and Stacks sources open. The current Step 1 uses proper-field-invertible-coherent, all 16 step citations match their statements, and the additional same-tag nodes have been read and distinguished explicitly. The five-step assembly and the two independent statement-only nodes preserve the approved route and all original arguments.

On this resumed repair I additionally checked the current-DAG substitution in Step 1 described above: the proper-field coherence statement supplies exactly the required preparation without additional hypotheses, and has no dependency path to this item. I re-read all current parent citation statements, both new statements and their definition inputs, Stacks 0B5X/0B3J/01XR/0B5U, and the retained actual search responses. All 16 current citations have verbatim quotes; the five-step assembly preserves the original argument with the extracted constructions assigned to their unsplit nodes. The review below is retained as the detailed mathematical audit; its old Step 1 account is superseded only by this direct reuse.

I read the source statement and complete proof of varieties.tex Tag 0B5X, lemma-ample-curve (lines 9998-10067). The first new node is exactly the construction in its second proof paragraph; the second is the claim established in its third proof paragraph, with the original fixed n and positive exponent En retained. I also read coherent.tex lemma-coherent-support-dimension-0 (0B3J), lemma-section-affine-open-kills-classes (01XR), and lemma-vanshing-gives-ample (0B5U), including its precise condition (3). These match the preserved old cohomological argument. I opened the current item, the two new files and all statements cited in the parent's five steps, along with the old input-node statements, before preparing citations.json.

For current Step 1, integral-scheme supplies nonemptiness, proper-morphism supplies finite type and separatedness, and curve defines a variety by exactly those properties. Finite-type-over-Noetherian supplies Noetherianity; coherent-ft-locnoeth supplies coherence once local rank-one freeness is used. The Noetherian-ring definition lets the field check be written directly from its two ideals. I verified all these are statements rather than facts hidden in proofs.

For Step 2, the ample-invertible-module definition explicitly defines tensor powers, including power zero, and says they are invertible. The degree definition gives degree of the unit zero, and the tensor-degree lemma applies since dimension one is at most one. Induction and rearrangement produce the stated Euler characteristic formula. This is elementary assembly of those cited statements.

For Step 3, I read clause (1) of h0-proper-variety, which requires only a proper variety and gives a finite field extension, not equality to k. Affine-spectrum explicitly says the spectrum of a field has one point; the Krull dimension definition then contradicts dimension one. Absolute ampleness supplies a positive power and section whose affine locus contains the chosen point, so the section is nonzero. The curve is not affine, so that locus cannot be all C. Section-degree-positivity states strict positivity under exactly this condition. Step 2 identifies the degree with nd; since n is positive this yields d positive.

For Step 4, I checked the first new statement concludes precisely a positive n and a nonzero section of N^n with affine C_s. The second new statement quantifies over the very same field, proper integral dimension-one C, invertible N, positive n and section, and gives a positive E for each quasi-coherent ideal. It requires no unstated smoothness, finite residue-field rationality or uniform exponent. The conclusion is H1(I tensor N^(En)) zero, so no comparison of differently indexed twists is hidden. These exact conclusions are the quotations in citations.json.

For Step 5, ideal-twist-vanishing-implies-ample has a Noetherian coefficient ring, proper structural morphism, invertible module and a possibly ideal-dependent positive exponent. The field check in Step 1 and the positive product En in Step 4 verify every hypothesis. Its conclusion is absolute ampleness, exactly the parent's notion. This proves the converse and combines with Step 3 without changing the parent's statement.

For the first new worker's argument, I checked that coherent-hi states finite cohomology over any Noetherian affine base, and separately cohomology-above-dimension supplies the bound q>1. The affine-complement statement requires precisely integral, Noetherian and dimension one. The old argument derives closedness of the finitely many boundary points by extending a strict specialization chain with the whole irreducible curve; the sober-scheme statement supplies the generic point. Closed-point-field clause (a) supplies finite residue degrees without assuming points rational. The rank-one fibre dimension and strict dimension inequality give a nonzero evaluation kernel without assuming evaluation onto. Affine-cap-section-open explicitly applies to nontrivial invertible modules, so it applies when the constructed locus is contained in the chosen affine open. These inputs and their original exact source places are retained in old Steps 4-5 below.

For the second new worker's argument, I checked coherent-kernel-cokernel-locnoeth clause (2) makes a quasi-coherent ideal coherent, and clause (1) makes the section-multiplication cokernels coherent. Integral-stalks-in-function-field states domain stalks and injections into the function field, supplying stalkwise injectivity of multiplication by a nonzero section. The zero-dimensional-support statement explicitly gives all positive cohomology zero; pqf-def-cohomology explicitly supplies the long exact sequence, yielding the successive H1 surjections. Section-affine-open-kills-cohomology concerns individual classes; a finite basis, finiteness from proper coherent-hi, and surjectivity are all still needed to conclude the whole group zero. Noetherianity gives quasi-compactness and the locally-Noetherian-quasi-separated statement supplies the other half of its qcqs hypothesis. These checks are why the new node is a substantial separate argument rather than a one-line instance of the existing class-annihilation lemma.

I tested positive, zero and negative degree on projective-line O(d): the existence lemma is asserted only for positive d; the trivial section of O has nonaffine full locus on a proper curve, so does not spuriously satisfy the second lemma's affine hypothesis. For the zero ideal the target cohomology is already zero and E=1 is allowed. If the initial H1 is zero, the same positive E=1 handles the empty basis. Non-rational closed points retain their actual finite residue degrees. Singular integral curves still have domain stalks; none of the arguments calls for smoothness. Empty or dimension-zero schemes are excluded by the stated integral dimension-one hypotheses. I checked the proof graph: neither new node depends on this parent as a statement or proof input (created.item and blueprint ancestry are provenance only). The new lemmas do not assume each other. All current proof steps are below 2000 characters, and no long hidden sublemma is retained. B1-B9, C1-C8 and D1-D5 are addressed in the files and the duplicate/search analysis; all E hypotheses above were checked explicitly. The only repair requested was redistribution, and it is now substantive: two independent unsplit work items plus a short parent assembly, with all previous details preserved.

## Preserved returned proof and allocation

The following is verbatim mathematical text from the returned nine-step node. Steps 4-5 are assigned to lem-trf-positive-degree-affine-section; Steps 6-8 are assigned to lem-trf-affine-section-ideal-twist-h1-vanishing. Steps 1-3 and 9 remain the parent assembly (Step 9 is now Step 5, referring to current Step 4). The first new lemma also uses the calculation of original Step 2 and the finiteness preliminaries of original Step 1; the second uses those preliminaries too. These are explicit proof-planning instructions in the report, not proof fields inside unsplit node files.

### Original Step 1

The scheme $C$ is nonempty by [def-pc-integral-scheme]. Properness includes finite type and separatedness [def-weil-proper-morphism], so $C$ is a variety in the sense of [def-pc-curve]. The field $k$ is Noetherian: its only ideals are $0$ and $(1)$ [def-weil-pbc-noetherian-ring]. Thus [lem-weil-pbc-finite-type-over-noetherian] makes $C$ Noetherian. By [pqf-lem-coherent-ft-locnoeth], $\mathcal O_C$ and every invertible module are coherent: locally each is free of rank one [def-sc-invertible-module]. Finite type over a field and properness therefore meet the Noetherian hypotheses used below.

Uses: def-pc-integral-scheme, def-weil-proper-morphism, def-pc-curve, def-weil-pbc-noetherian-ring, lem-weil-pbc-finite-type-over-noetherian, pqf-lem-coherent-ft-locnoeth, def-sc-invertible-module.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, preliminary proper-curve and finiteness hypotheses; Properties Tag 01OV and Cohomology of Schemes Tag 01XZ

### Original Step 2

Write $d=\deg_k(\mathcal N)$. By [def-weil-pbc-ample-invertible-module], each $\mathcal N^{\otimes n}$ is invertible, including $\mathcal N^{\otimes0}=\mathcal O_C$. The degree definition [def-pc-degree-line-bundle] gives $\deg_k(\mathcal O_C)=0$. Induction using [lem-trf-curve-degree-tensor-additive] gives $\deg_k(\mathcal N^{\otimes n})=nd$ for every $n\ge0$: the induction step adds $d$ to the preceding degree. Rearranging the definition of degree gives $\chi(C,\mathcal N^{\otimes n})=nd+\chi(C,\mathcal O_C)$.

Uses: def-weil-pbc-ample-invertible-module, def-pc-degree-line-bundle, lem-trf-curve-degree-tensor-additive.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, tensor-power degree and Euler-characteristic identities; Tag 0AYX

### Original Step 3

First assume $\mathcal N$ ample. The field $K=\Gamma(C,\mathcal O_C)$ is a finite extension of $k$ by [lem-pc-h0-proper-variety], since Step 1 showed $C$ is a proper variety. If $C$ were affine, it would be $\operatorname{Spec}K$ [def-weil-affine-spectrum], a one-point space of dimension zero [def-kun-topological-krull-dimension], contrary to $\dim C=1$. Choose a point of $C$. The ampleness definition [def-weil-pbc-ample-invertible-module] supplies $n\ge1$ and a section $s$ with that point in the affine open $C_s$. Hence $s\ne0$ and $C_s\ne C$, since $C$ is not affine. Applying [lem-trf-curve-section-degree-positivity] to $\mathcal N^{\otimes n}$ gives $nd>0$ by Step 2, whence $d>0$.

Uses: lem-pc-h0-proper-variety, def-weil-affine-spectrum, def-kun-topological-krull-dimension, def-weil-pbc-ample-invertible-module, lem-trf-curve-section-degree-positivity.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, forward implication; Tag 0B40, nonzero section with a zero

### Original Step 4

For the converse assume $d>0$. By [lem-pc-coherent-hi], the coherent modules $\mathcal N^{\otimes n}$ on proper $C/k$ have finite-dimensional cohomology. Since $C$ is Noetherian of dimension one, [lem-sc-noetherian-cohomology-above-dimension] kills their cohomology in degrees above one. Thus [def-pc-euler-characteristic] and Step 2 give $h^0(C,\mathcal N^{\otimes n})=nd+\chi(C,\mathcal O_C)+h^1(C,\mathcal N^{\otimes n})\ge nd+\chi(C,\mathcal O_C)$, which is unbounded as $n\to\infty$. Choose any nonempty affine open $U\subseteq C$. By [lem-sc-affine-complement-finite-on-integral-curve], its complement is a finite set $\{x_1,\ldots,x_t\}$. Each $x_i$ is closed: in an integral dimension-one scheme a non-generic point with a distinct specialization would give the chain $\overline{\{y\}}\subsetneq\overline{\{x_i\}}\subsetneq C$, contrary to the dimension definition [def-kun-topological-krull-dimension]; the generic point exists by [lem-weil-pbc-scheme-sober]. Since $C/k$ is finite type, [lem-kun-closed-point-field] gives $[\kappa(x_i):k]<\infty$.

Uses: lem-pc-coherent-hi, lem-sc-noetherian-cohomology-above-dimension, def-pc-euler-characteristic, lem-sc-affine-complement-finite-on-integral-curve, def-kun-topological-krull-dimension, lem-weil-pbc-scheme-sober, lem-kun-closed-point-field.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, reverse implication, growth of sections and choice of finite boundary

### Original Step 5

Choose $n\ge1$ with $h^0(C,\mathcal N^{\otimes n})>\sum_i[\kappa(x_i):k]$. Evaluation at the $x_i$ is a $k$-linear map to $\bigoplus_i(\mathcal N^{\otimes n})_{x_i}\otimes\kappa(x_i)$, whose dimension is that sum because each fibre has dimension one over $\kappa(x_i)$ [def-sc-invertible-module]. Its kernel is nonzero by the dimension inequality. Take a nonzero section $s$ in the kernel, so $s$ vanishes at every boundary point. Consequently $C_s\subseteq U$, using the fibrewise definition of $C_s$ [def-weil-pbc-ample-invertible-module]. By [lem-sc-affine-cap-section-open], $C_s=U\cap C_s$ is affine. This produces a fixed $n\ge1$ and nonzero $s\in\Gamma(C,\mathcal N^{\otimes n})$ with affine nonvanishing locus. No surjectivity of the evaluation map was required.

Uses: def-sc-invertible-module, def-weil-pbc-ample-invertible-module, lem-sc-affine-cap-section-open.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, evaluation kernel and affine nonvanishing locus; Properties Tag 01PV

### Original Step 6

Let $\mathcal I\subseteq\mathcal O_C$ be any quasi-coherent ideal. It is coherent by [lem-weil-pbc-coherent-kernel-cokernel-locnoeth](2), since $C$ is locally Noetherian and $\mathcal O_C$ is coherent. Put $\mathcal F_e=\mathcal I\otimes\mathcal N^{\otimes en}$ for $e\ge0$. These are coherent because locally the invertible factor is $\mathcal O_C$ [def-sc-invertible-module]. The nonzero section $s$ has nonzero generic value: on a trivializing open where it is nonzero its coefficient injects into the function field by [lem-sc-integral-scheme-stalks-in-function-field]. Hence its coefficient at every stalk is nonzero, by that same injection. Multiplication by $s$ on each $\mathcal F_e$ is injective: after trivializing, it is multiplication by a nonzero element on the ideal $\mathcal I_x$ in the domain $\mathcal O_{C,x}$. It is an isomorphism on $C_s$. Thus $0\to\mathcal F_e\xrightarrow{s}\mathcal F_{e+1}\to\mathcal Q_e\to0$ is exact, with coherent cokernel by [lem-weil-pbc-coherent-kernel-cokernel-locnoeth](1). Its support is contained in $C\setminus C_s$, which omits the generic point and has dimension at most zero: any strict chain there would extend by $C$ to a length-two chain [def-kun-topological-krull-dimension].

Uses: lem-weil-pbc-coherent-kernel-cokernel-locnoeth, def-sc-invertible-module, lem-sc-integral-scheme-stalks-in-function-field, def-kun-topological-krull-dimension.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, injective section-multiplication sequence and zero-dimensional cokernels

### Original Step 7

Apply [lem-pc-chi-zero-dim-support](1) to each coherent $\mathcal Q_e$ on the proper $k$-scheme $C$: Step 6 verified its support dimension at most zero, so $H^1(C,\mathcal Q_e)=0$. The long exact sequence explicitly supplied by [pqf-def-cohomology] for the short exact sequence in Step 6 gives a surjection $H^1(C,\mathcal F_e)\twoheadrightarrow H^1(C,\mathcal F_{e+1})$ for every $e\ge0$. Composing these maps shows that $H^1(C,\mathcal I)\to H^1(C,\mathcal F_e)$ is surjective for every $e$.

Uses: lem-pc-chi-zero-dim-support, pqf-def-cohomology.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, surjectivity on first cohomology; Cohomology of Schemes Tag 0B3J

### Original Step 8

The vector space $H^1(C,\mathcal I)$ is finite-dimensional by [lem-pc-coherent-hi], since $C/k$ is proper and $\mathcal I$ is coherent. Apply [lem-sc-section-affine-open-kills-cohomology] with $X=C$, $L=\mathcal N^{\otimes n}$, $F=\mathcal I$, and $p=1$: $C$ is quasi-compact and quasi-separated by Step 1 and [lem-weil-pbc-locally-noetherian-quasi-separated], $L$ is invertible, and $C_s$ is affine by Step 5. Each element of a finite basis is killed by some power of multiplication by $s$. Choose $E\ge1$ at least all these exponents (take $E=1$ for the zero vector space). The map $H^1(C,\mathcal I)\to H^1(C,\mathcal F_E)$ kills the basis and hence is zero. It is also surjective by Step 7, so $H^1(C,\mathcal I\otimes\mathcal N^{\otimes En})=0$. The exponent $En$ is positive and may depend on $\mathcal I$, exactly as required.

Uses: lem-pc-coherent-hi, lem-sc-section-affine-open-kills-cohomology, lem-weil-pbc-locally-noetherian-quasi-separated.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, finite basis and eventual annihilation; Cohomology of Schemes Tag 01XR

### Original Step 9

Step 8 applies to every quasi-coherent ideal of $\mathcal O_C$. The field $k$ is Noetherian by Step 1, $C\to\operatorname{Spec}k$ is proper by hypothesis, and $\mathcal N$ is invertible. Therefore [lem-trf-ideal-twist-vanishing-implies-ample] with $R=k$ gives absolute ampleness of $\mathcal N$. Together with Step 3 this proves the equivalence, with the original degree and without imposing smoothness or geometric integrality.

Uses: lem-trf-ideal-twist-vanishing-implies-ample.

Source: literature/stacks-project/varieties.tex, Tag 0B5X, final application of Cohomology of Schemes Tag 0B5U, implication (3) => (1)

## Retained historical report and searches

# Q55: lem-trf-proper-integral-curve-ample-degree

## Files written

- dag/nodes/sec-trace-formula/lem-trf-proper-integral-curve-ample-degree.json: statement, split into nine proof steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-curve-degree-tensor-additive.json: statement-only supporting lemma, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-curve-section-degree-positivity.json: statement-only supporting lemma, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-ideal-twist-vanishing-implies-ample.json: statement-only supporting lemma, unsplit; no Mathlib match.
- citations.json: literal statement quotations for each proof-step citation, retaining the hypotheses as context.
- report.md: this report. Search requests and responses are retained in searches.jsonl and search_outputs.jsonl.

There are three new statement nodes and zero Mathlib leaves. The item's existing statement, origin, blueprint ancestry and historical Mathlib searches are retained. No unit record is changed: this item is an auxiliary of sk-i-curve-zero, not its key node.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag and for the ampleness, degree, section and tensor-product notions. AlgebraicGeometry.Scheme.isAmple_iff_degree_pos in WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean:1519 has a sorry-free proof, but assumes SmoothOfRelativeDimension1 and GlobalSectionsBijective k X. Neither hypothesis is present here. Its local context therefore prevents an attachment, including for singular curves or nontrivial constant fields. The degree tensor declarations in the same file also carry smooth-curve hypotheses. The ampleness implication in Curve/Ample.lean:548 uses an algebraically closed field and Hilbert-polynomial degree, and is not the complete item. The upstream master is reference material, not evidence of completed proofs.

## WANTED

None. All sources used are available locally in literature/stacks-project/.

## Issues and changes

The item was unsplit and had no proof. Its statement is faithful to Stacks Tag 0B5X: a curve in that source is integral, separated and of finite type over the field, and properness supplies the latter two conditions here. No smoothness, normality, geometric integrality or algebraic closure is needed. No STATEMENT-DISPUTED correction is needed.

The new proof follows 0B5X rather than replacing the item with a lemma asserting one direction of ampleness versus degree. Its new inputs are independent facts about degree and sections and a general cohomological ampleness criterion. Tensor-power induction, the evaluation-kernel argument, local multiplication on an ideal, and taking a maximum over a finite basis are written into the item. Existing nodes supply the non-elementary inputs. In particular the ordinary forward Serre-vanishing nodes cannot supply the converse used in the last step.

I read the chapter and unit, the current blueprint ancestry, and the item source. The blueprint ancestor is lem-trf-local-term-locality, through the recorded fibre-degree/ampleness/projectivity chain. All new nodes record that same place and the intervening item in their via list. Whole-DAG searches by tags and concepts and blueprint_refs.py searches by 0B5X, 0AYX, 0B40, 0B5U, degree/tensor, degree/section and vanishing/ampleness found no equivalent general node to reuse. Existing smooth/projective or algebraically closed degree criteria have stronger hypotheses. No new same_as blueprint occurrence was found.

Each of the four candidate statements was searched through msearch.py using LeanFinder, LeanSearch, Loogle and grep, with a second semantic phrasing. Actual returned responses are saved and copied into mathlib_searches without changing query text. The broad grep ample|Ample includes irrelevant occurrences in the word example; the additional whole-word ampleness grep returned zero. The field-of-global-functions hit is useful background, but does not prove the ampleness criterion. Picard tensor-class identities do not give an Euler-characteristic degree homomorphism. The section-positivity hits concern polynomial degrees, not line bundles on proper integral schemes. None can be specialized to a new node in one line. No service was unavailable in these searches.

## Unfinished work

The three supporting nodes are intentionally statement-only, as required by the one-level split. Their complete statements and precise Stacks sources are provided for later workers. The item itself has a complete natural-language proof; no Lean is written or compiled.

## Not duplicates

lem-trf-ideal-twist-vanishing-implies-ample vs lem-pc-serre-vanishing: the existing node assumes ampleness and concludes eventual higher-cohomology vanishing for coherent sheaves over a field; the new node assumes H1 vanishing of a positive twist for each quasi-coherent ideal and concludes ampleness over any Noetherian affine base. These are different directions of 0B5U.

lem-trf-ideal-twist-vanishing-implies-ample vs lem-weil-pbc-coherent-serre-vanishing: the existing node is the forward Serre-vanishing implication over a Noetherian affine base, not its converse; the new node needs only one positive exponent for each ideal.

lem-trf-ideal-twist-vanishing-implies-ample vs lem-zl-bertini-finite-cover-curve: the existing node constructs a smooth affine curve in a higher-dimensional variety over a finite field, preserving connectedness of an etale cover. Its proof invokes forward Serre vanishing under Tag 0B5U; its statement contains no cohomological criterion for ampleness.

No existing node carries Tag 0AYX or 0B40. In particular the tensor and section lemmas are not restatements of the item: neither mentions ampleness, and their hypotheses and conclusions apply independently of the degree criterion.

## Review by Q55

I checked the split against delivery-errors B through E with the statements and sources open. I read the complete proof of varieties.tex lemma-ample-curve (0B5X), the tensor-product degree formula lemma-degree-tensor-product (0AYX), the first two clauses and proof of lemma-check-invertible-sheaf-trivial (0B40), and coherent.tex lemma-vanshing-gives-ample (0B5U), specifically implication (3) to (1). The first new node is the rank-one instance of 0AYX, with properness and dimension at most one retained; the second retains the integrality, properness and dimension-one assumptions of 0B40 and distinguishes a nonzero section from a nowhere-zero section; the third retains the Noetherian ring and proper structural map of 0B5U and uses its absolute ampleness conclusion. None uses a prohibited source.

For Step 1, I checked the proper-morphism, integral-scheme and curve definitions: they give a nonempty integral finite-type separated scheme, exactly a variety. The finite-type-over-Noetherian lemma states Noetherianity of the source, and coherent-ft-locnoeth gives coherence of the locally free rank-one modules. The field being Noetherian is immediate from its two ideals. For Step 2, the power and degree definitions together with the new tensor-additivity statement give the displayed induction, including exponent zero. There is no unproved degree-power formula hidden here.

For Step 3, I used only clause (1) of h0-proper-variety, which gives a finite extension field for a proper variety without geometric integrality. The affine-spectrum and dimension definitions make an affine such curve zero-dimensional, a contradiction. The ampleness definition supplies a nonzero section whose affine locus contains a chosen point. Because the curve is not affine this section has a zero, exactly the hypothesis of the new section-positivity node; positivity of nd implies d>0 since n>=1.

For Step 4, coherent-hi supplies finite cohomology modules over any Noetherian affine base, including the arbitrary field k. The separate Noetherian cohomology-above-dimension lemma supplies H^q=0 for q>1; coherent-hi alone does not state that bound. The Euler characteristic definition then gives the stated inequality. The affine-complement lemma applies because C is integral, Noetherian and one-dimensional. I wrote out the dimension argument showing boundary points are closed, citing sobriety for the generic point, and used only part (a) of closed-point-field to get finite residue degrees. No residue field is assumed to be k.

For Step 5, local rank one makes each evaluated fibre one-dimensional over its residue field. The strict dimension inequality gives a kernel element without needing evaluation surjectivity. The nonvanishing-locus definition implies C_s is contained in U; affine-cap-section-open says exactly that U intersected with this locus is affine even for a nontrivial invertible module. This avoids assuming a principal open of an affine in a globally chosen trivialization.

For Step 6, I read both clauses of coherent-kernel-cokernel-locnoeth: clause (2) makes the quasi-coherent ideal coherent, and clause (1) makes the cokernel coherent. Twisting by an invertible module locally preserves the same module, so coherence is local here. The integral-scheme stalk lemma states both injection into the function field and that every stalk is a domain. After trivializing the section these facts prove the multiplication maps injective on ideals. They are invertible on C_s by the definition of that locus. The proper closed support omits the generic point, so a nontrivial chain in it would contradict dimension one. This explicitly verifies the support hypothesis needed next rather than calling the cokernels torsion without explanation.

For Step 7, chi-zero-dim-support explicitly states vanishing of all positive cohomology of a coherent module with zero-dimensional support on a proper scheme. I use its H1 conclusion, not just its Euler characteristic clause. The cohomology definition node explicitly includes the long exact sequence of a short exact sequence; that actual clause gives surjectivity. For Step 8, coherent-hi applies to the now-coherent ideal. I added the existing locally-noetherian-quasi-separated lemma after checking the qcqs hypothesis of section-affine-open-kills-cohomology: Noetherianity gives quasi-compactness and that lemma gives quasi-separatedness. The section-annihilation lemma allows an arbitrary invertible module, so I apply it to N^n, not to N with the wrong section. Taking a common positive exponent over a finite basis and using Step 7 proves the entire target H1 group zero. Finally Step 9 checks precisely all hypotheses of the new ideal-twist criterion; its quantifier is a possibly different positive exponent for every ideal, exactly what Step 8 proves.

I tested the statements on O(d) on the projective line for positive, zero and negative d; the trivial section at degree zero is nowhere vanishing, so no false strict-positivity conclusion follows. Over a non-algebraically-closed field a closed point contributes its residue degree, which the evaluation argument retains. Singular integral curves still have domain stalks and finite coherent cohomology, so no smooth hypothesis slips into the proof. Dimension-zero and empty proper schemes are allowed in the tensor lemma and give the expected zero degree; the section lemma and item intentionally require dimension one. The ideal zero and a vanishing initial H1 cause no exception: the common exponent can be chosen as 1. The criterion also has the right vacuous conclusion over the zero ring and empty proper source. All steps are shorter than 2000 characters. The only newly separated lemmas are the three non-elementary source inputs; elementary linear algebra, local trivialization and finite-basis reasoning remain explicit steps. Every cited node statement is copied verbatim in citations.json, so the stated hypotheses can be inspected alongside the step using them.
