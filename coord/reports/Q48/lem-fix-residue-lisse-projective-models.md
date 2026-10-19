# Worker report

Item: lem-fix-residue-lisse-projective-models. Group: Q48. Date: 2026-10-16.

## Files written

- dag/nodes/sec-six-functors/lem-fix-residue-lisse-projective-models.json: statement, split into eight steps; no Mathlib match.
- dag/nodes/sec-six-functors/lem-sf-complete-residue-cohomology-bounds.json: statement-only, unsplit; no Mathlib match. It supplies cohomological bounds from residue Tor amplitude, with no local constancy or constructibility assumption and no projective-model conclusion.
- citations.json: verbatim statements for the 29 step/node citations. Complete statements are quoted where several clauses or the coefficient convention are used together.
- report.md: this report. searches.jsonl is the search command's own log; build_split.py is sandbox-only preparation code, not a delivery file.

## Attachments

None. Searched the exact item tag and identifier and the concepts residue/lisse/projective, local structure of constructible complexes, and derived-complete cohomological bounds throughout /home/ubuntu/weil-src-slopmaster2/WeilConjectures. The projection-formula declarations found do not state the local-model theorem. No matching declaration was found for the new bounds node either. The upstream master is reference material, not closed-proof evidence. No Lean file was written or compiled, and no git command was run in the shared repository.

## WANTED

None: all sources used are present locally.

## Statement corrected

STATEMENT-DISPUTED: the imported constructibility citation [def-weil-finite-torsion-constructibility] is tied to the standing global finite-field datum, whereas this lemma is about an arbitrary affine weakly contractible S. The cited definition itself allows an arbitrary scheme Y; the mismatch is its extra unused global finite-field datum and the condition ell != p, which the item does not quantify. A characteristic-zero S is allowed by that definition and is not a counterexample. The intrinsic constructibility binding removes the extraneous datum without changing the predicate on S.

Replaced that definition binding by [def-weil-proetale-constructible-sheaf], the intrinsic finite-stratification notion on arbitrary schemes, and spelled out the finite-dimensional local models in the locally constant case. This follows 09C3, which assumes no characteristic, invertibility of ell on S, Noetherianity of S, or dimension restriction. The original mathematical conclusion and all hypotheses are retained. Finite residue cohomology is meant; no constant-integral-matrix conclusion was inserted. No target statement or unit record changes.

## Proof and source audit

Read proetale.tex, Tag 09C3 (lemma-local-structure-constructible-complex), in full, including the footnote on idempotent lifting and the final induction. Read 09C2 (lemma-describe-constructible-complexes), its proof, 099Q (proposition-enough-weakly-contractibles), 09BY (lemma-derived-complete-zero), 09BZ (lemma-derived-complete-limit), and the local D_cons definition preceding 09C2. Also read algebraization.tex 099I (lemma-restriction-derived-complete-equivalence), sites-cohomology.tex lemma-bounded and 0946/0947 (lemma-w-contractible/proposition-enough-weakly-contractibles), and derived.tex 064B (lemma-morphisms-from-projective-complex). Read sites-cohomology.tex 06YQ (lemma-bounded-flat-K-flat) for the two-term quotient resolution. The existing node lem-pc-bounded-above-flat-kflat-site cites 06YS incorrectly in its source metadata; its statement agrees with 06YQ. This is an existing-node metadata correction for maintenance, not an edit by this worker. The current main-20261015 blueprint's lem-fix-weil-operations.proof.md has the evaluation sentence named in the ancestry. Its unit sk-rem-sf-pf-done is an interface-discharge remark; this child provides the local coefficient tool used beneath its evaluation comparison, not a new unit route.

The argument is marked agent-written because it expands and specializes the source's induction: over the field k one can choose a basis, rather than an arbitrary set of generators. Consequently the residue map is an isomorphism on its top cohomology. This makes the cone residue an explicit sum of the lower cohomology sheaves, plus a contracted identity complex. It supplies the details the source omits about the decreased Tor interval. The general-ring idempotent-lifting subargument is unnecessary in this field specialization. The integral differentials remain sheaf maps.

The new bounds statement extracts just the argument of 09C2(1),(2). The proof of those clauses uses finite residue Tor amplitude and completeness, not constructibility: the nilpotent quotient filtration gives the same Tor interval at all finite levels, while exact weakly contractible evaluation and the surjective top-degree cohomology transitions eliminate the possible upper lim^1 term. The result is H^j(K)=0 outside the same interval. The statement is deliberately left unsplit, with all objects and notions introduced and no proof sketch in its statement. It is a substantive input, not a projective-model clause of the item.

## Searches and reuse

Whole-DAG searches used the tags 09C3, 09C2, 099Q, 09BY, 09BZ, 099I, plus weakly contractible, complete cohomology, residue, lisse and projective-model phrases. Ran blueprint_refs.py ancestor for the item and whole-blueprint searches for projective, locally constant, 099Q, 09C2, cohomology bounds, and complete residue. There is no blueprint node stating the new bounds theorem. The old integral-heart nodes assume the standing Noetherian setting or a constructible category; they do not state the required interval on arbitrary weakly contractible affines. The existing residue-lisse-perfect-lift node assumes a Noetherian X and gives a pro-etale covering with constant integral complex models, not the finite disjoint open covering of a possibly non-Noetherian weakly contractible S. It was not used.

All item and new-node Mathlib queries in the added records were actually run through msearch.py. Used LeanFinder, Loogle, Mathlib grep and LeanSearch, including a second semantic phrasing for each. The bounds hits are ordinary AdicCompletion/IsAdicComplete and the derived t-structure IsGE/IsLE lemmas; these do not relate completeness to residue amplitude. The local-model hits are condensed locally constant functors, Profinite projectives and perfectoid period rings, not pro-etale constructible complexes. Read Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean at its t-structure definition, and Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:267-269: the latter defines finite presentations of individual module sheaves, not complete complex models. Loogle and the focused source greps returned no hits. No new Mathlib leaf or attachment is claimed.

Reused existing coefficient flatness/reduction and constant-sheaf exactness, quotient-tower derived limits, derived Nakayama, site and covering/coproduct facts, bounded projective localization, long exact cohomology, and exact derived change of rings. Each off-unit theorem used as a generic tool is declared in split_report.tool_uses; none replaces a unit step.

## Not duplicates

lem-sf-complete-residue-cohomology-bounds vs lem-fix-residue-lisse-projective-models: the new theorem gives only a cohomological interval, with no lisse hypothesis or local projective models; the item's eight steps construct those models.
lem-sf-complete-residue-cohomology-bounds vs prop-weil-pbc-levelwise-truncations: this node studies normalized truncation towers with the extra (TC) hypothesis; the new result bounds the original complete object from its residue Tor interval.
lem-sf-complete-residue-cohomology-bounds vs det-thm-sf-pf-adic-projection: that node is a proper projection formula, with no residue-bound conclusion.
lem-sf-complete-residue-cohomology-bounds vs sk-lem-int-ext: that node gives filtered-colimit and Ext bounds for constructible objects, not cohomological bounds from residue reduction.
lem-sf-complete-residue-cohomology-bounds vs det-lem-int-ext-bound: that node bounds Ext for stratum generators and constructible sheaves, not complete complexes on arbitrary quasi-compact schemes.
lem-sf-complete-residue-cohomology-bounds vs det-lem-int-integral-heart-local-model: that node requires membership in Dbc and asserts stratified constant integral models and closure of cohomology; it gives no residue Tor interval theorem on arbitrary X.
lem-sf-complete-residue-cohomology-bounds vs det-prop-diagonal-tower-limit: that node concerns diagonal classes, Tate twists and direct-image limits, not amplitude detection.
lem-sf-complete-residue-cohomology-bounds vs det-lem-int-integral-heart-triangulated: that node asserts boundedness and truncation stability of a standing constructible category; it does not give the precise residue interval, and does not cover arbitrary quasi-compact X without that constructibility hypothesis.
lem-sf-complete-residue-cohomology-bounds vs sk-lem-int-integral-heart: that node concerns the constructible heart and its duals and stratifications, with no general residue interval assertion.
lem-sf-complete-residue-cohomology-bounds vs det-lem-int-tensor-pullback: that node preserves a standing constructible category under pullback and identifies completed pullback; it does not detect cohomological bounds.
lem-sf-complete-residue-cohomology-bounds vs sk-thm-sf-pf-adic: that node concerns open direct image, proper base change and the projection formula.
lem-sf-complete-residue-cohomology-bounds vs def-weil-pbc-tower-preservation: that node defines preservation of uniformly constructible towers and does not prove residue amplitude detection.
lem-sf-complete-residue-cohomology-bounds vs def-weil-pbc-ringed-site-ideal: that node defines ideal sheaves and their scalar extension, with no theorem about complete complex cohomology.
lem-sf-complete-residue-cohomology-bounds vs lem-weil-pbc-tower-compatibility: that node records transition compatibility of four corner operations, not cohomological bounds.
lem-sf-complete-residue-cohomology-bounds vs lem-weil-pbc-levelwise-isomorphism-cones: that node detects zero from all finite reductions and uses intrinsic completion, but gives no same-interval bound from the first residue Tor interval.
lem-sf-complete-residue-cohomology-bounds vs lem-weil-pbc-torsion-limit-sheaf-completeness: that node gives Serre and inverse-limit closure of degree-zero derived complete sheaves and completeness of bounded complexes; it does not deduce bounds on an initially unbounded complex from residue amplitude.
lem-sf-complete-residue-cohomology-bounds vs thm-weil-pbc-amplification-proper: that node requires proper maps and Noetherian finite-dimensional schemes to prove AMP/WIT/TOW, not the present arbitrary-scheme bound.
lem-sf-complete-residue-cohomology-bounds vs prop-weil-pbc-preservation-constructible: that node is preservation under four proper-square operations with extra Noetherian/dimension/invertibility hypotheses, not amplitude detection for an original complete object.
lem-sf-complete-residue-cohomology-bounds vs lem-weil-pbc-constant-completion-equivalence: that node compares complete coefficient categories and reductions, but states no cohomological bounds; its comparison is useful supporting material.
lem-sf-complete-residue-cohomology-bounds vs def-weil-pbc-witness-compatibility: that node defines coherent etale-origin witnesses in a base-change square, not complete complex bounds.
lem-sf-complete-residue-cohomology-bounds vs prop-weil-pbc-restriction-direct-image: that node bounds proper direct image on finite-level constructible categories and has no residue detection assertion.
lem-sf-complete-residue-cohomology-bounds vs lem-weil-pbc-flat-ringed-ideal-complete-equivalence: that node is a general restriction-of-scalars equivalence; it does not relate cohomological support to residue Tor amplitude.
lem-sf-complete-residue-cohomology-bounds vs lem-sf-proetale-vanishing-detection: that node detects acyclicity by evaluation at every affine weakly contractible object for finite coefficients, not bounds from derived completeness.

## Review by Q48

I checked the item against the complete text of 09C3, especially that its maps are maps of sheaves, rather than matrices required to lie in the coefficient ring. No SGA route is used. For the new node I checked the proof of 09C2(1),(2), the 0947 Milnor sequence and the 099I comparison; quasi-compactness and a single residue Tor interval are present, and neither Noetherianity of X nor constructibility is silently used in those two clauses. The new node introduces X, R, B_X, K, its complete quotient tower and the quantified Tor interval explicitly. All its non-Mathlib definition dependencies exist. It has no proof, no proof dependencies and no undeclared data.

Step 1 reads exactly the existing DVR statement, coefficient-flatness/reduction statement, constant-sheaf exactness statement and surjective-tower derived-limit statement. The domain property makes multiplication by each uniformizer power injective; flatness then gives the two-term quotient resolution over B. The Nakayama statement supplies cone closure and first-residue detection. I added det-prop-integral-criterion-constant-coefficients and sk-def-pe-derived-completion explicitly to identify its completed integral coefficient convention with B, instead of identifying coefficient categories silently.

Step 2 reads the covering definition for a finite affine refinement, the site node for common refinements, the actual scheme coproduct statement for clopen components, weak-etale stability for composition/source-locality, and subcanonicity for representables. I corrected the initial draft by citing open-immersion-etale and etale-implies-weakly-etale separately: weak-etale stability alone does not supply that input. The lift is a section of the representable h_V over S, hence an actual scheme map, and the clopen pieces are inverse images of genuine coproduct components. This is the categorical weak-contractibility hypothesis the item has, not the stronger ring formulation of the existing w-contractible partition lemma.

Step 3 uses only the actual localization statement from lem-weil-proetale-weakly-etale-localization. The rest is the written-out sheaf gluing argument for a finite disjoint open cover: categories and complexes split into factors, epimorphisms extend by a terminal factor, and limits/tensors/completion units restrict componentwise. Thus weak contractibility and completeness remain true on each U. The elementary equality Hom_C(C,F)=F(U) proves the needed projectivity of free sheaves; no assumption that every module sheaf is projective is made. The closedness of U in quasi-compact S is enough for the new bounds node, so no unjustified affine or Noetherian hypothesis on U enters.

Step 4 invokes the new node for the exact [a,b] support. It builds, rather than assumes, residue formality: cycles lifting cohomology bases define a quasi-isomorphism from a bounded zero-differential free complex. The existing projective-localization statement is for arbitrary abelian categories and bounded-above complexes of projective objects; those precise hypotheses were checked using step 3. Its bijection gives the Hom calculation used in step 5. A ring-module-only resolution theorem would not have sufficed here.

Step 5 uses the stated long exact cohomology sequence, the actual two-term quotient resolution, and projective localization. The surjection onto top residue cohomology uses the already-proved vanishing H^(b+1)(M), not the converse. I also added the existing K-flat resolution and bounded-above flat K-flat lemmas: the two quasi-isomorphisms in step 5 justify computing the unbounded M residue by the two-term free quotient resolution. The same bounded-flat theorem justifies the tensor test in step 6. Two lifts are performed explicitly: residue basis sections to H^b(M)(U), then to cycles. The residue derived map is determined by this basis through the projective Hom calculation, so it is the top-summand inclusion.

Step 6 uses exactly cone closure/residue detection and exactness of derived change of rings. I computed the residue cone, contracting its two-term identity summand; therefore both constant finite cohomology and Tor amplitude [a,b-1] follow directly from the remaining free residue terms. This avoids an uncited assertion that a kernel of locally constant sheaves is automatically locally constant. For a=b the residue cone is zero and Nakayama gives the one-term base case, and r=0 is harmless.

Step 7 checks the induction hypothesis for L on the same U. Projective localization represents the connecting morphism by a sheaf chain map, whose sole component and chain equation are displayed. The shifted cone has Q^q in degrees below b and P in degree b, so its support is exactly within [a,b]; the triangle rotation identifies it with M. Step 8 uses the identity splittings of free terms and the finite cover already constructed. No step asserts integral formality, constant integral matrices or etale triviality of K.

For B1-B10 and C1-C8 I checked that the only new theorem is a genuine supporting bound, not any projective-model clause; every non-elementary input is cited, with each cited statement opened and quoted in citations.json. The elemental projectivity, product decomposition, residue splitting and cone calculations are written as arguments within steps, not new nodes. Source tags and labels were checked against the local tag table (I corrected the exact-evaluation tag to 0946). For D1-D5 the induction has a stated invariant, length-zero base, strict decrease and a constructed model; the source's omitted amplitude argument is present. Off-unit generic tools are declared without altering maintainer-owned tool_uses.

For E1-E7 I checked the empty scheme, zero residue, zero top rank, one-degree interval, finite disjoint unions with different ranks, and a torsion object B/varpi: its residue has two adjacent degrees, and the construction can produce the differential varpi, so it does not wrongly assert an integral split complex. For the new bound, B shifted into one degree, B/varpi (degrees [-1,0] after reduction), and the empty scheme have the claimed bounds. Dropping completeness would be false for B[1/varpi] with zero residue, and completeness is explicitly retained. Characteristic ell schemes are allowed by both local source results; no invertibility hypothesis was borrowed from unrelated finiteness nodes.

No new statement remained doubtful after these repairs. The only statement dispute was the inappropriate original definition binding, corrected above. The source and the proof route themselves were not disputed. The required dry run and its outcome are recorded below.

## Unfinished work

The new cohomological-bounds lemma is intentionally unsplit, as required for a one-level split. No other proof gap is left in the item's argument. A second reader must review and deliver; this worker does not push.

## Dry run

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q48 lem-fix-residue-lisse-projective-models --no-push` printed `OK (not pushed)` with preflight passed (first successful dry-run commit d742cb3f18). The command is repeated after this outcome is recorded so the handed-over report is itself part of the accepted sandbox. No delivery is pushed by this worker.

## Second reading by Q48

Step 1 was checked against Stacks 09C3's coefficient setup and the cited DVR, completion, reduction, K-flat, derived-limit, and Nakayama statements; verdict: the quotient resolution and completeness claims use the stated hypotheses.

Step 2 was checked against 09C3, the pro-etale covering definition, coproduct-family, weakly-etale stability, open-immersion etaleness, etale comparison, and subcanonicity statements; verdict: the finite clopen trivializing partition is constructed from the categorical weak-contractibility hypothesis.

Step 3 was checked against the weakly-etale localization statement and the disjoint-open sheaf product description; verdict: restriction preserves weak contractibility, completeness, residue amplitude, and projectivity of finite free sheaves on each piece.

Step 4 was checked against 09C2(1),(2), the abstract derived-category definition, and projective-complex morphism representation; verdict: the residue basis lifting gives the claimed bounded zero-differential model and the Hom calculation.

Step 5 was checked against the two-term quotient resolution, K-flat resolution and bounded-flat K-flat statements, the long exact cohomology statement, and projective localization; verdict: top-degree basis lifts define the required map and its residue is the top-summand inclusion.

Step 6 was checked against derived Nakayama, exact derived change of rings, and bounded-flat K-flatness; verdict: the cone calculation explicitly contracts the identity summand and decreases the residue interval, including the zero-rank and length-zero cases.

Step 7 was checked against projective localization and the explicit cone and shift conventions; verdict: the connecting morphism is represented by the displayed last differential and the shifted cone represents the original complex.

Step 8 was checked against the item hypotheses, the finite partition, and derived Nakayama; verdict: the resulting finite free models imply the stated direct-summand conclusion and cover the empty and zero cases.

The new node `lem-sf-complete-residue-cohomology-bounds` was checked against Stacks 09C2(1),(2), 099Q, 0946/0947, and 099I; verdict: it is statement-only, self-contained, and supplies only cohomological bounds from the explicitly quantified residue Tor interval. Its Mathlib searches are recorded and yielded no match.

I changed the report by adding this second-reading record and retained the worker's correction from the global finite-field constructibility binding to the intrinsic pro-etale constructibility definition. I also verified all 29 citation quotes verbatim, the absence of SGA 4/4½ sources, the empty/zero/one-degree and torsion edge cases, and the required Mathlib search log. The mathematical proof steps required no repair. I found the same unused global finite-field convention in the completion and reduction definition bindings: I replaced those bindings in the item and the new node by the explicitly written quotient-tower completeness condition, the generic derived-limit and restriction-of-scalars definitions, and generic derived change of rings. The completed ring remains the displayed inverse limit of constant quotient sheaves. No hypothesis or conclusion changed. I also corrected the worker report: its old cited constructibility definition does allow arbitrary Y, so a characteristic-zero S is not a counterexample; the actual mismatch is the unquantified unused finite-field datum. The new independent searches used t-exact completion/AdicCompletion/IsLE vocabulary and are recorded verbatim in the new node and searches.jsonl; the ordinary finite-module adic exactness result is not a match.

Second-reader dry-run follow-up: the first run found that the current delivery base had expanded the definition references in `sk-lem-pe-weakly-etale-stability`; the mathematical statement is unchanged. I reopened it in the current live DAG mirror and refreshed its full verbatim quote in citations.json.

Independent dependency check: the repaired item reaches 890 existing/new dependencies after stopping at Mathlib leaves; every reference exists and no dependency path returns to this item. The proof_deps list is exactly the union of the eight steps' uses. The whole-blueprint searches for cohomological bounds, residue, and derived complete found no duplicate of the new bound; det-pe-unbounded-classical-bounds instead concerns torsion etale direct-image bounds for finite-type schemes over a field. AdicCompletion.map_exact was read at Mathlib/RingTheory/AdicCompletion/Exactness.lean:184 and is ordinary exactness on finitely generated modules, not derived-complete pro-etale amplitude detection.

The second reader's final dry run printed `OK (not pushed) deliver/Q48/lem-fix-residue-lisse-projective-models at ec89ec6f77: preflight passed`. The corrected sandbox passed preflight before delivery.
