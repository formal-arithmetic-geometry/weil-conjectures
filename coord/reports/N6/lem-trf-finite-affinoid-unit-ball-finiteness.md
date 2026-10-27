## Worker report

Files written under dag/nodes/sec-trace-formula/:

- lem-trf-finite-affinoid-unit-ball-finiteness.json: item, split into nine proof steps; statement unchanged.
- lem-trf-affinoid-minimal-component-norm.json: statement-only analytic component comparison; no Mathlib match.
- lem-trf-tate-fraction-orthogonal-spectral-norm.json: statement-only orthogonal fraction-field input; no Mathlib match.
- lem-trf-tate-norm-attaining-submodules.json: statement-only generic normed Tate-module theorem; no Mathlib match.

Attachments: none. Searches of the item tag and affinoid/unit-ball terminology in lean/WeilConjectures found no declaration stating this item. The p-adic integer finiteness declarations concern finite extensions of Q_l, not finite affinoid maps. Existing Sheaf analytic declarations are reference material and do not qualify as finished project attachments.

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, archival PDF in literature/, Sections 5.2.7, 5.3.2, 6.2.1 and 6.4.1, for the item and all three new nodes.

WANTED: Conrad perfectoid seminar, Lecture 12, archival PDF in literature/, paragraph following Example 12.2.5 on PDF p.2, for confirmation of the item's hypotheses.

I read the primary BGR scan online at https://math.arizona.edu/~cais/scans/BGR-Non_Archimedean_Analysis.pdf, rendering its scanned pages for inspection in the sandbox. Printed pp.208–212 give pseudo-cartesian generators and their inheritance by submodules; p.237 gives the component norm formula; pp.251–252 give the finite-affinoid argument and algebraically closed corollary. Conrad's Lecture 12 at https://virtualmath1.stanford.edu/~conrad/Perfseminar/Notes/L12.pdf independently confirms that reducedness of the target is essential. The proof_origin is honestly agent: the book is absent from literature/, although its primary scan was read online. No repository or literature file was written. No Lean was written, compiled or built.

## What needed correction

The seeded item was statement-only. Its mathematical statement is correct, and neither it nor its hypotheses were changed. The source's algebraically closed result is specifically BGR Corollary 6.4.1/5; Corollary 6 is the discretely valued alternative. The item inherited both references, and the proof now pinpoints Corollary 5.

A tempting proof through distinguished presentations would be circular: lem-trf-affinoid-distinguished-presentation uses lem-trf-tate-reduction-norm-lifting, which already cites this item. The Grauert–Remmert powerbounded-model node also depends on that presentation chain. None is cited here. Finite canonical reductions alone do not provide the exact norm-attaining generators needed here, and no unproved identification of these notions is used.

There is no statement dispute and no departure from the chapter/unit route. I read the latest sk-i-curve-zero section and lem-trf-local-term-locality proof: their current contraction argument does not use analytic normalization. This item is an inherited analytic auxiliary below the node level, as its original blueprint ancestry already records. Its completion neither replaces a current unit step nor changes the chapter's route. The from.place and via chains retain that provenance.

## Searches

All new Mathlib searches ran with the required msearch.py N6 lem-trf-finite-affinoid-unit-ball-finiteness command and are preserved in searches.jsonl. Each new node records the actual tool/query/result records for its own mathematical question. Two semantic phrasings were tried for each input, together with Loogle and source grep. Searches for the item itself were also repeated in this sandbox and appended without deleting the inherited Q111 searches.

The orthogonal-fraction-field searches returned spectralNorm and spectralAlgNorm. I read their source and the complete-base hypothesis on spectralNorm.normedField: these do not prove an exact orthogonal basis over the generally incomplete Gauss fraction field, or its restriction to an affinoid domain. The submodule searches returned FG generating-family equivalences (Finiteness/Defs.lean:60) and FG.of_le_of_isNoetherian (Noetherian/Basic.lean:377). I read both; neither asserts exact coefficient bounds attaining a norm. The component searches returned minimalPrimes.finite_of_isNoetherianRing (MinimalPrime/Noetherian.lean:43), generic seminorm sup formulas and product norms. These do not establish affinoid Noetherianity, the affinoid quotient topology, or the spectral component identification. Thus there are three unsplit nodes and zero new Mathlib leaves.

Whole-DAG statements and blueprint_refs searches for affinoid, integral closure, pseudo-cartesian, norm-attaining, fraction field norm, Gauss norm, orthogonal basis and minimal primes were read. Existing candidates are distinguished below. No Stacks tag supplies the analytic statements, so BGR's numbered results, rather than an invented Stacks tag, are the sources.

## Not duplicates

lem-trf-affinoid-minimal-component-norm vs lem-trf-affinoid-supremum-seminorm-calculus: the existing statement gives maximal residue fields and spectral inequalities, but no finite minimal-prime family, quotient affinoid domains, or component isometry.

lem-trf-affinoid-minimal-component-norm vs lem-weil-pbc-noetherian-finitely-many-minimal-primes: the existing statement assumes Noetherianity and gives only finiteness, whereas the new analytic comparison identifies the quotient topologies and supremum functions for affinoids.

lem-trf-affinoid-minimal-component-norm vs lem-trf-affinoid-finite-galois-envelope: the envelope uses larger normal domains with Galois fraction fields, not the actual component quotients, and does not assert an isometry of spectral norms.

lem-trf-tate-fraction-orthogonal-spectral-norm vs lem-trf-tate-galois-trace-supremum-bound: the existing node bounds a field trace under a Galois and normality hypothesis. The new input gives a vector norm and orthogonal basis for arbitrary finite affinoid domains, including inseparable fraction extensions.

lem-trf-tate-fraction-orthogonal-spectral-norm vs lem-trf-affinoid-spectral-banach-norm: the latter asserts spectral completeness and norm equivalence on a reduced affinoid; it gives neither an extension to the fraction field nor an orthogonal basis there.

lem-trf-tate-norm-attaining-submodules vs lem-trf-affinoid-finite-module-strictness: strictness gives a constant H in a norm comparison and closed images, whereas the new statement gives exact coefficient norm attainment and inherits it by arbitrary submodules.

lem-trf-tate-norm-attaining-submodules vs lem-trf-restricted-saturated-submodule-finite: the latter concerns saturation over valuation-ring restricted series, not Gauss norm attainment over a field Tate algebra, and supplies no exact norm formula.

lem-trf-tate-norm-attaining-submodules vs lem-trf-tate-ideal-best-approximation: the latter treats distance to an ideal in the Tate algebra; it does not state inheritance of weighted norm-attaining generators for arbitrary normed Tate modules.

None of the three new statements concludes finiteness of spectral unit balls for finite affinoid maps. The fraction-field and component inputs give analytic comparison objects, while the submodule input is about arbitrary normed modules. The item retains the relative normalization, denominator lattice, source contraction, product and submodule assembly, value-group argument, scalar rescaling and final generating argument. They are not renamed clauses of the item.

## Review by N6

I checked delivery-errors B–E against the JSON and primary sources. Each new node has an independent self-contained statement, no proof or proof dependencies, explicit norm conventions, its own searches, and filled blueprint ancestry. The only definitions used beyond ring/field/module notation are cited or written inline. Every cited statement was opened; citations.json copies its statement verbatim, with an entry for every uses occurrence. Every step is below 2000 characters, and the maximum is about 1100; there is no long step concealing an additional standard lemma.

For the item I read BGR printed pp.251–252, including the source-reduction paragraph and the full reduced-case argument, rather than only quoting Corollary 5. For the fraction-field node I checked the domain argument on p.252, where Stability Theorem 5.3.2/1 and spectral restriction Proposition 3.8.1/7 are explicitly invoked; I also read the stability discussion on p.214. The statement does not incorrectly assert multiplicativity of a spectral norm over an incomplete field. For the submodule node I read Definition 5.2.7/3, Theorem 7 and Corollary 11 on pp.208–212: the norm is a weighted quotient norm, and the submodule need not be assumed finite beforehand. For the component node I read the entire setup and Lemma 6.2.1/3 on p.237, including the finite minimal-prime family.

Step 1 uses only the existing supremum-calculus statement: finite residue fields over algebraically closed K are K, and its bound by the quotient norm makes these residue characters continuous. This also works for nonreduced A. Multiplication, addition and scalar inequalities follow by taking suprema of the character inequalities, not by assuming A is reduced.

Step 2 uses the normalization-lift node exactly for a proper presentation ideal; A is nonzero. It obtains an actual map into A, not just an abstract normalization of B. The supremum-calculus node supplies contraction. The finite T-module generating list of B is the written double sum, so no transitivity lemma is hidden.

Step 3 uses the new component comparison exactly for reduced nonzero B. Its quotient algebras are nonzero domains, and its statement gives both injectivity and the maximum formula. The existing spectral-Banach node applies to these reduced quotients and makes their functions genuine norms. Passing a finite generating list to a quotient is elementary.

Step 4 applies normalization to T/ker(T→C_i), whose kernel is proper because C_i is nonzero. The lift lands in T, which is needed in step 6. The map from that quotient into C_i is finite and injective, so the new fraction-field statement has all its hypotheses. It does not require the common T→C_i to be injective. The spectral-calculus statement gives the contraction for S_i→T.

Step 5 constructs an actual finite orthogonal lattice using a product of denominators of finitely many coordinates. The new submodule theorem applies to the finite lattice, whose displayed basis attains its norm, not directly to the infinite T-module L_i. Its restriction norm on C_i is precisely the norm furnished in step 4. This is the central application of the independent Tate-module theorem.

Step 6 is elementary from those interfaces: its two inequalities are written, so transport of exact norm attainment is checked even though S_i→T need not preserve the Gauss norm. Finite products use the maximum norm and generators supported in single factors. Step 7 then applies the same generic theorem to the actual isometric image of B, already known to be a T-submodule. No arbitrary affinoid inclusion is claimed to have closed image.

Step 8 uses the minimal-polynomial formula in the fraction-field node, not an unsupported assertion that all real norms can be scaled. Gauss values are coefficient values, fraction values are their ratios, and algebraic closedness supplies all required roots. A finite maximum is one value. The existing spectral-Banach node gives positive norm for nonzero y_k. Scaling the finite generators to norm one preserves the exact maximum formula. Step 9 explicitly turns its coefficient bound into membership in A's unit ball, using the actual j:T→A. It proves both inclusions of the generated module.

Small cases checked: K itself and zero variables; A=K[ε]/(ε²)→K (nonreduced source); A=K⟨X⟩→K by X↦0 (noninjective map); B=K×K (component product); B=K⟨X,Y⟩/(XY) (intersecting components); the inseparable map K⟨U⟩→K⟨X⟩ with U↦X^p in characteristic p; zero submodules and empty generating families in the generic submodule node. None creates a missing separability, injectivity or discreteness hypothesis. Removing reducedness from the item would fail for K→K[ε]/(ε²): all Kε lies in the spectral unit ball. I therefore retained its reduced-target condition exactly.

What remains: no mathematical split work is left in this item; the three new input statements are deliberately unsplit stage-1 work. The initial repair dry run passed as 21ddb6a2eb5 before the clarifications below; the final repaired files are submitted to the required dry run again before pushing.

## Repair of returned delivery, 2026-10-24

The sole return point was L's refusal to land c3203c1679cb8acf0932cc3674f7ae205e2bb736 because side completion had not been promoted to the live DAG. I compared that returned head, the retained sandbox, and the refreshed current main DAG at 9e1aa5868ee0b95e30a7bf3221ac68e845e36a1e. I read the commit/tree objects without running a git command in the read-only repository. The current main item is still unsplit with an empty proof, and none of the three new analytic inputs exists there. Thus the split must be delivered on the current base, rather than treated as an already completed live item. The delivery command builds that rebase itself and preserves current maintainer metadata; promotion is L's operation, not a metadata field for this worker to alter.

The retained item is identical to the returned item. Each retained auxiliary differs from its returned file only by the generated lean_audit none-state metadata. I retained all four statements, the nine-step route, the report's source readings, all prior search records and citations. There is no change in mathematical search question requiring repeated Mathlib searches.

I compared the three existing proof-dependency blobs at the returned head and current main: lem-trf-affinoid-supremum-seminorm-calculus (d52f49fef31e0452a7a693fe764c87153cd4f288), lem-trf-tate-normalization-lift (31df9143fd74a4a6177f42157a5732b7d23bb96d), and lem-trf-affinoid-spectral-banach-norm (21ac11b2ddb4a3eb9243bc8fab0a4ac979b13a1c) are unchanged. I nevertheless re-read each current statement in full. In particular the calculus lemma applies to nonreduced affinoids, normalization supplies a lift into the original Tate algebra, and spectral nondegeneracy requires the reduced quotient. The retained quotes for all three are their entire current statements. The two presentation/finiteness definition blobs are also unchanged. I re-read the current field definition (ordinary commutative field), restricted-series definition, and finite-module definition; the uses of them retain their original meanings.

I adjusted the assembly rather than sending an unchanged patch. Step 1 now explicitly displays the ultrametric inequality that step 9 uses. Step 4 now proves that the induced T/J_i action is finite by reducing coefficients of the same finite T-generating family, before composing with normalization; injectivity follows from the definition of J_i. This keeps the proper-ideal/nonzero-domain hypotheses visible at the exact application. These are elementary clarifications of the approved route, requiring no new node or source. I reopened the retained BGR p.252 scan: its proof uses exactly this source-modulo-kernel reduction followed by the cartesian fraction-field argument and the submodule theorem. The statements and conclusions are unchanged.

I checked B–E again on the repaired files. The three inputs remain statement-only and self-contained, with their original Mathlib results and blueprint ancestry. Step 1 uses calculus, step 2 normalization and calculus, step 3 component comparison and the reduced spectral norm, step 4 normalization/calculus/fraction-field norm, step 5 the norm-attaining submodule input, step 7 the same submodule input, and step 8 the fraction-field formula and spectral norm. Each current cited statement supplies exactly that interface, and each occurrence still has its full verbatim quotation in citations.json. Steps 6 and 9 remain the written elementary inequalities and generating calculation. All steps remain below 2000 characters. The earlier nonreduced-source, noninjective-map, product, intersecting-component, zero-variable and inseparable examples still satisfy these clarified arguments. A fresh project-source search again found no completed attachment for the item. No Lean or launcher file was changed and no compiler/build tool was invoked.

## Repeated promotion refusal after 00ed83fece0

L returned the repaired head 00ed83fece09a8346f1c0b67ce9304d3cf3161c4 at 2026-10-24 10:48 UTC with exactly the same side-completion/live-queue disagreement. The retained repair already includes the explicit ultrametric inequality and the quotient-coefficient argument in step 4; this is not the original uncorrected delivery. Current main inspected on this retry is 598b68bf54bd91afa5c44e7c5c99446f65e27502. Its item is unsplit and all three auxiliary nodes are absent. There is no released repair-note record for the item. I re-read every cited statement on this retry and checked every retained verbatim quotation against it. Comparison with the returned repaired head gives:

- lem-trf-affinoid-supremum-seminorm-calculus: current statement equals the retained full-statement citation.
- lem-trf-tate-normalization-lift: current statement equals the retained full-statement citation.
- lem-trf-affinoid-spectral-banach-norm: current statement equals the retained full-statement citation.

The initial required retry dry run completed successfully at 645ab942789. No mathematical defect or changed citation was reported. I inspected tools/nt_land_batch.py: the refusal at lines 567–573 is specifically the not-stage-1-open retirement path when queue_node(item) is not stage1_completed, while the side completion prevents ordinary landing; the code comment explicitly assigns the side completion's promotion to L. The promotion operation is implemented in that same maintainer tool, not in any worker-owned node field. tools/retire_stage1.py lines 69–78 requires completion in both views before retirement. The report and proof cannot reconcile those two server views.

This retry is BLOCKED on maintainer promotion/reconciliation of the existing side completion into the DAG the queue reads. I have not changed status/review metadata to evade the check, edited a launcher or repository file, run a maintainer promotion operation, or manufactured another proof change to force a new patch. The existing split, sources, citations, searches and prior repair are retained. A third unchanged re-push would not repair the diagnosed landing-state disagreement. No delivery invocation remains active.

## Renewed delivery after the blocked retry

The dispatcher renewed the same task after the BLOCKED result. That result diagnosed the repeated landing refusal rather than invalidating the retained mathematical repair. I inspected the refreshed main reference a34aa3daa63159d3eb302cfe64892658b004ffc5 and re-read all six cited statements. The existing calculus, normalization and reduced spectral-norm statements still equal their retained full-statement quotations; the three auxiliary statements remain the retained inputs. The live item is still unsplit with no reviewed record and has no released repair note. The searches' questions and all four statements are unchanged, so their original logged results and citations remain applicable.

On this re-read I made one further elementary precision in step 8: select a nonzero series coefficient c, then use |c|/2 as the threshold. The finite set of coefficient norms above it is nonempty, and its attained maximum dominates every remaining coefficient. This explicitly proves Gauss-norm attainment, including a series with just one nonzero coefficient. It strengthens the written argument without changing the statement, the inputs, the source route or the value-group conclusion. Every step remains below 2000 characters. The previous step-1 ultrametric and step-4 quotient-module repairs remain intact.

The promotion diagnosis above remains for L's independent review. This renewed dispatch authorizes another validated delivery attempt; it does not authorize this worker to execute L's promotion operation or change maintainer-owned completion data. The next delivery contains this clarified proof and the previously undelivered diagnostic report, rather than an unchanged patch from 00ed83fece0. All source readings, prior reviews, citations and searches are retained. No repository, Lean or launcher file was changed.

## Persistent landing-state blocker after c0741d07140

The latest return is dated 2026-10-24 11:08 UTC and identifies c0741d07140486899b1d87fd82440b00272491a7. It again says the reader approved the work, then reports the same unpromoted side-completion failure. That head already contains the source-quotient argument, explicit ultrametric inequality, nonempty Gauss-maximum argument, and detailed promotion diagnosis. No additional mathematical finding was returned.

On this dispatch I compared the retained delivery files with the refreshed read mirror and checked each of the six citations against its entire stored statement. Every citation still equals the entire applicable statement. There is no changed theorem interface to repair and no changed search question. The mirror refreshed during inspection: an initial file read saw the item split and auxiliary files present, while the subsequent read at origin/sheaf-dag 65d234619dd8f0faf4f80535219d5b6d00669010 saw the item unsplit (zero steps) and the three auxiliary files absent. I do not interpret those non-atomic file observations as proof of server promotion. The required delivery tool selected its own refreshed base and passed preflight as 5aecc884b74.

The exact latest refusal remains implemented by tools/nt_land_batch.py:567–573. It concerns whether the side completion and queue completion agree; its own comment assigns promotion to L. Editing a mathematical proof, an unchanged re-push, or a worker-written review/completion flag does not repair that condition. The first two delivery heads have already demonstrated that rebasing and proof clarification can pass preflight and push yet encounter this same refusal. This is therefore a tool/state blocker requiring L to reconcile the side completion with queue_node(item), not a mathematical ABANDON. All mathematical work and logs remain retained. No promotion script, repository write, compiler, build or launcher modification was attempted.
