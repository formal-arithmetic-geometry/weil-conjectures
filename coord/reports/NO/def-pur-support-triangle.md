## Worker report

Files written:

- `dag/nodes/sec-smooth-purity/def-pur-support-triangle.json`: definition, split using existing nodes; not a Mathlib leaf. Its statement is byte-for-byte unchanged. No new nodes.
- `citations.json`: empty list, because this definition has no proof steps.
- `searches.jsonl`: actual msearch.py queries; LeanSearch returned Internal Server Error and is recorded unavailable.

Attachments: none. In the read-only slopmaster2 source, `AlgebraicGeometry.Etale.supportsUnit` (SixFunctors/OpenClosed/Supports.lean:102) and `AlgebraicGeometry.Etale.supportsShortComplex` (:115) define the restriction and its kernel short complex on the small **etale** site, for an already supplied complex I. They do not state this item's entire construction on the small **pro-etale** site fixed by def-pur-flasque-support, from the specified resolution of K and with its cone differential. `supportLocalizationTriangle` (:157) is likewise etale and assumes the supplied degreewise injective complex. The docstring tags alone do not give an attachment. No master sorry declaration is treated as proved.

WANTED: the item's original `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/def-pur-support-triangle.md`, and its slopmaster2 counterpart, for def-pur-support-triangle. Neither file is installed here; the read-only master checkout's blueprint directory is empty. I read the exact imported statement in the node and the chapter/unit records instead, preserved the statement, and did not pretend to have read the missing primary document. Also absent locally are the Stacks tex sources referenced by the reused nodes (derived.tex, Definition 070H and cone definition; injectives.tex, Theorem 079P). No literature or live files were changed.

The imported dependency `def-weil-pbc-kinjective-resolutions` is etale-only: its statement fixes Mod(T_et,R). It cannot serve directly for the pro-etale category in the supported-sections definition. Replaced it by `def-pur-kinjective-complex`, whose statement works on an arbitrary ringed site, and cited `prop-pur-kinjective-resolutions-exist` for the specified choice with injective terms. Added `def-weil-abstract-derived-category`, whose statement already writes the exact cone terms and differential. There is no mathematical change to the item's statement, no change of site or coefficients, and no statement dispute. The definition has no proof to split into steps; creating separate nodes for A, B, C or this very cone would only duplicate its clauses.

Nothing mathematical remains unfinished in this one-level definition split. The missing primary source is explicitly recorded above for the second reader. The support exactness and quasi-isomorphism assertions in `dag/notes/sec-smooth-purity/rem-ptr-pur-support-triangle-2.json` are not assertions of this item: this item supplies the construction only. I did not add them or cite them circularly.

## Existing nodes reused

- `def-pur-flasque-support`: closed immersion s and complementary open j on the small pro-etale sites; supported sections are ker(M -> j_*j^*M), with s_*s^!M equal to this kernel. This gives A(K), C(K), and the inclusion u, degreewise. Its statement explicitly distinguishes s^! from ordinary restriction.
- `def-pur-kinjective-complex`: for any ringed site, defines K-injectivity and a quasi-isomorphism into a K-injective complex. It applies to the constant finite coefficient sheaf on X_proet, unlike the replaced etale-specific definition.
- `prop-pur-kinjective-resolutions-exist`: its statement gives a functorial resolution for every complex on a small ringed site, with every term injective. Use the small site skeleton already fixed by the pro-etale conventions. Thus it covers the bounded-below input K without requiring I(K) to stay bounded below. Its statement, not any internal proof construction, supplies the chosen resolution data.
- `def-weil-abstract-derived-category`: for any abelian category, its statement explicitly gives C(f)^r=L^r direct-sum K^{r+1} and the matrix differential (d_L,f;0,-d_K). Substitute f=u, source=A(K), target=B(K). This is also sufficient for the cochain-complex and morphism notions. The small pro-etale module category is abelian as recorded in the general ringed-site resolution theorem.

## Searches and duplicate check

Searched the whole DAG for mapping cone, Cone(u), cone complex, support, and K-injective notions; ran blueprint_refs.py search with `mapping cone`, `support`, and `cone`, and ancestor on the item. The generic cone already occurs in def-weil-abstract-derived-category; general ringed-site K-injectivity already occurs in def-pur-kinjective-complex and its existence theorem. None of the other blueprint nodes returned states this item's full support-specific construction. Set same_as=[]; blueprint.from is correctly null for this imported node. No new node was necessary, so there are no new-vs-existing tag pairs for a Not duplicates section.

msearch.py was run for the whole item with LeanFinder, Loogle, LeanSearch and grep, and a second semantic phrasing isolated the cone. The first semantic hits concerned CM5b factorization/injective objects. The second returned mappingCone and its API. Loogle likewise returned mappingCone. Source grep found MappingCone.lean:57 and related general triangle constructions, not supportLocalizationTriangle or supportsShortComplex. Read MappingCone.lean:45-68 and 260-300 and Pretriangulated.lean:45-64. Its projections give d(a,b)=(-d_A a,u(a)+d_B b) in the source-first coordinate order; exchange coordinates to the item's (b,a) to obtain exactly (d_B b+u(a),-d_A a). These hits cover only a constituent already in the DAG; they do not make this whole definition a Mathlib leaf. The second grep was a single-file invocation; its wrapper output parsed the line numbers as file names, so the report and node record that limitation and the subsequent direct source reading honestly.

## Review by NO

I read stages/1-dag.md, the three levels in SETUP.md, GOAL.md, coord/dag-sync.md, coord/brief-stage1.md and delivery-errors B through E, the chapter and unit JSON records, this item's imported source text, the four reused node statements, the replaced etale-only definition, the neighbouring pointer remark, and slopmaster2 SixFunctors/OpenClosed/Supports.lean. The original literature blueprint file is unavailable; the WANTED entry identifies this rather than claiming a primary-source comparison. No new node needs an additional source review. The definition realizes the imported displayed construction without replacing any unit proof step.

For C4 I matched every dependency to the precise content just listed: supported sections and its inclusion come from the kernel definition; K-injectivity comes from the definition on an arbitrary site; existence with injective terms and functorial choice comes from the full statement of prop-pur-kinjective-resolutions-exist; the cone formula comes verbatim from the statement of the general derived-category node. The former etale-only dependency failed this check and was corrected. There are zero proof steps, so there are no step citations to quote in citations.json. The empty proof and proof_deps are intentional for a definition, not an omitted proof of localization or distinguishedness. For C1, no theorem about exactness of supported sections, injectivity preservation, restriction acyclicity, or identification of Cone(u) with C(K) is asserted or assumed in the construction. Those are separate properties. The one non-elementary existence input is explicitly represented by the existing ringed-site resolution theorem.

For B and D I avoided creating any new node: the ingredient definitions already exist, and the composite A,B,C and cone formulas are precisely the data this item defines. All maintainer and imported fields are preserved. The statement is not changed to etale sheaves to fit the project declaration. No Mathlib match for the whole item is claimed from the generic cone hits. Recorded searches are exactly the tools and query strings executed, with the failed LeanSearch marked unavailable. The imported blueprint id stays its own is field, from stays null, and the report identifies the three clauses it realizes.

For E I checked the small-site hypothesis of the resolution theorem against the chosen small skeleton of the pro-etale site and used its constant commutative coefficient sheaf. Its unbounded theorem includes a bounded-below K. The construction requires no exactness of j_*: a functor applied to a complex gives the degreewise complex and kernel naturality makes u a chain map. Squaring the displayed cone differential gives (d_B^2 b + d_B u(a) - u d_A(a), d_A^2 a)=(0,0), since u is a cochain map. For Z empty, A=0 and Cone(u)=I; for U empty, A=I and u=id, so the formula gives the identity cone and C=0. For the zero complex, the zero resolution would give all zero terms; the specified functorial resolution need not choose it, and the construction also applies to a nonzero acyclic I(0). A degree m source element contributes u(a) in B^{m+1}, while -d_A(a) lies in A^{m+2}; thus the shifted index and sign type-check. These tests use no identification of s^{-1} with Rs^!, no exactness of s^!, and no unproved change from pro-etale to etale coefficients.

Corrections made in this reading: replaced the etale-only K-injective dependency with the general ringed-site definition; supplied the already existing injective-term resolution theorem and cone definition; populated blueprint same_as and split_report; retained the mathematical statement literally. No agents were started, no Lean was written or compiled, and only the sandbox was edited.


## Earlier second reading (a previous round; superseded)

- Proof steps: none; checked the item's `kind=definition`, `proof=[]`, and construction-only wording against stages/1-dag.md §3(2) and the imported statement. PASS: there is no localization, exactness, or distinguishedness assertion to prove here; `citations.json=[]` is exact.
- New nodes: none; independently searched the DAG by source tags 070H/079P and by support/cone terminology, and searched the whole imported blueprint with blueprint_refs.py. PASS: existing ingredients suffice, and neither the localization theorem nor the triangle-meaning definition duplicates this construction.
- Item, closed–open pair and coefficients: checked against the complete statement of `def-pur-flasque-support`, `def-pur-conventions`, and `def-weil-pbc-proetale-site`. PASS: the site is pro-etale and the coefficient sheaf is the fixed finite constant commutative ring sheaf; no etale replacement was made. Direct comparison with the primary blueprint remains unavailable: the local master/slopmaster2 blueprint files are absent, and attempts at their exact archived GitHub URLs returned HTTP 404. The original WANTED entry therefore remains valid for the blueprint.
- Item, chosen resolution: checked `def-pur-kinjective-complex` against Stacks 070H, derived.tex label `definition-K-injective`; checked the full statement of `prop-pur-kinjective-resolutions-exist` against Stacks 079P, injectives.tex label `theorem-K-injective-embedding-grothendieck`, and 07A5, sites-cohomology.tex label `section-unbounded`. PASS: functorial resolutions have injective terms for every complex. The V-small skeleton is explicitly fixed by `def-weil-pbc-proetale-site` and `def-weil-size-convention`, so the theorem's smallness hypothesis holds in V. Boundedness of I(K) is neither supplied nor needed.
- Item, A/B/C and inclusion: checked the kernel formula and identification in the statement of `def-pur-flasque-support`. PASS: writing r_M:M -> j_*j^*M for restriction, its naturality gives r_{I^{m+1}} d_I^m = (j_*j^*d_I^m) r_{I^m}. Thus d_I carries ker(r_{I^m}) into ker(r_{I^{m+1}}); this defines d_A and gives d_B u = u d_A. Degreewise applying the additive restriction and direct-image functors defines C. No preservation of injectives or exactness of j_* is needed for these complexes.
- Item, cone clause: checked the exact statement of `def-weil-abstract-derived-category`, then Stacks derived.tex label `definition-cone` at lines 2470–2490, and the pinned Mathlib `CochainComplex.mappingCone` at MappingCone.lean:57 with differential projections :275 and :288. PASS: in degree m the off-diagonal map is u^{m+1}; exchanging Mathlib's source-first coordinates gives (d_B^m b+u^{m+1}a,-d_A^{m+1}a). Squaring gives (d_B^2 b+d_Bu(a)-ud_A(a),d_A^2 a)=(0,0). The kernel inclusion and the ordinary cone maps are actual specified maps, with no derived comparison assumed.
- Reused nodes (all four): read each complete statement, not just its proof or source tag; the preceding three lines identify exactly the clauses used. PASS for C3/C4/E1. The etale-only resolution node removed by the first worker really is insufficient for the present site. No unquoted proof citation was added.
- Existing Lean: independently read slopmaster2 Supports.lean:96–119 and :157–160 and searched by the item id and support declaration names. PASS on the first reader's decision not to attach them: their category is Sheaf X.smallEtaleTopology A and their input is a supplied I; they do not state the whole current pro-etale definition. No sorry declaration from master was used as a proof.
- Small cases: checked X empty (the module category is zero), Z empty (A=0, C=I, cone=I), U empty (A=I, u=id, C=0, identity cone), and a field (both possible closed–open pairs satisfy these formulas). PASS. For K=0 an arbitrary fixed resolution I(0) may be a nonzero acyclic injective complex; the formulas and d^2=0 still hold. The earlier all-zero test is valid only if the zero resolution is chosen. In degrees m=0 and m=1 the cone terms are B^0 ⊕ A^1 and B^1 ⊕ A^2 and d has the stated codomain. The smallest permitted coefficient stage n=1 introduces no division or further condition.
- Independent Mathlib search: ran msearch.py LeanFinder with “Kernel of the adjunction unit from a sheaf complex to the direct image of its restriction to an open subspace and mapping cone of the kernel inclusion”; the eight hits concern HomComplex cocycles, CM5b factorizations and Mayer–Vietoris squares, not this construction. Ran source grep `localizationTriangle|sectionsWithSupport|supportedSections|support.*cone|cone.*support`; its only two hits concern convex cones and submonoid support. PASS: these searches supply no whole-definition match. Their exact outputs are recorded by msearch.py in searches.jsonl. No new Mathlib leaf is claimed.

Changes in this second reading:

- Retrieved the official Stacks source files into sandbox-only `sources/` and checked the labels above. These resolve the first reader's missing-Stacks-source limitation without writing into the live project. Source URLs: https://raw.githubusercontent.com/stacks/stacks-project/master/derived.tex ; https://raw.githubusercontent.com/stacks/stacks-project/master/injectives.tex ; https://raw.githubusercontent.com/stacks/stacks-project/master/sites-cohomology.tex . The matching tagged statements are https://stacks.math.columbia.edu/tag/070H , https://stacks.math.columbia.edu/tag/079P , and https://stacks.math.columbia.edu/tag/07A5 .
- Added independent searches, the explicit kernel differential argument, and the qualification of the zero-input test. No mathematical fault in the item's statement or dependency split was found; the node is preserved without further edits. There are zero new nodes and zero new Mathlib leaves.
- Left all first-worker sections, including `## Review by NO`, in place. No Lean, compiler, build, live-repository write, launcher edit, or sub-agent was used.


## Returned delivery repair audit by NO

Return read: coord/returns/NO.md, def-pur-support-triangle, immutable head
`de6b49de87e2`, H1/H3/H8/H10/H13. This return explicitly requests stage 2,
whereas the current direct-delivery brief, GOAL.md, and the final isolated-run
section of coord/brief-stage1.md authorize only stage 1 and forbid Lean writing
and compilation. The instruction to compile in the repair paragraph conflicts
with that explicit restriction. No stage-2 work or compilation is claimed.

1. H1 (Lean module and lean record): unresolved within this assignment. The
   sandbox contains the stage-1 definition node and report, not a Lean module.
   Reading /home/ubuntu/weil-launcher-nt/deliver.py confirms that it collects
   dag/nodes/*/*.json and the report (plus permitted unit realization fields),
   never collects Lean modules, and excludes `lean` among maintainer fields.
   Thus even a fabricated sandbox lean record would not repair this return.
2. H3 (complete pro-etale construction and exact signature): unresolved as a
   Lean signature. The mathematical node still specifies the same bounded-below
   input, K-injective resolution with injective terms, A/B/C, inclusion, and cone
   differential. Its statement has not been weakened to fit an etale API. The
   existing report explains why the etale support construction is not an exact
   attachment; that observation is not a completed pro-etale implementation.
3. H8 (module and declaration docstrings): unresolved because the requested
   docstrings belong to the forbidden new Lean module. Existing natural-language
   source and review records cannot be represented as Lean docstrings instead.
4. H10 (scompile evidence): unresolved. No compiler, Lake, build tool, or remote
   compilation was run; no evidence was invented. The stage-1 delivery preflight
   is not compilation evidence and cannot discharge H10.
5. H13 (usable dependency interfaces): unresolved as Lean dependency modules.
   The four existing statement dependencies remain the stage-1 interfaces. A
   compiled implementation on the pro-etale site is additional stage-2 work,
   not something this stage-1 package or a dependency citation supplies.

This audit changes only this sandbox report; it does not claim to repair any of
these stage-2 requirements. No new node, new Mathlib search, statement change,
attachment, or mathematical abandonment is warranted by the return. The blocker
is the mismatch between the requested stage-2 repair and the authorized stage-1
workflow/tool, not a counterexample to the construction. The return needs stage-1
review, or a separate stage-2 assignment with its permitted delivery/compiler
path. No delivery will be pushed by this worker.


Dry-run result for this repair audit: invoked exactly
`python3 /home/ubuntu/weil-launcher-nt/deliver.py NO def-pur-support-triangle --no-push`.
It produced no preflight result and waited on
`/home/ubuntu/worktrees/locks/weil-newtargets.worktree.lock` (confirmed by
`ps` showing `locks_lock_inode_wait` and `lslocks` showing the queued FLOCK).
Stopped this worker's waiting process with SIGINT; no other process or lock was
changed. The dry run did not print OK; this repair is BLOCKED, not READY. This
lock observation is separate from the unresolved stage-1/stage-2 scope mismatch.


## Repair retry by NO — 2026-10-16

Re-read the exact immutable-head return in coord/returns/NO.md. Its five requested repairs remain stage-2 requirements: H1 requires a Lean module and record; H3 the complete pro-etale implementation and exact Lean signature; H8 Lean docstrings; H10 scompile evidence; H13 usable Lean dependency interfaces. None is discharged by this stage-1 DAG package. I have not relabelled unchanged artifacts as a repair or invented a compile result.

The current coord/STATE.md has an isolated stage-2 pilot entry dated 2026-10-15. It expressly limits that authorization to NA, at most two distinct items, and defers pro-etale master-dependent nodes. This worker is NO and its item is pro-etale. Consequently that entry does not override this assignment's explicit ban on Lean writing and compilation. GOAL.md and coord/brief-stage1.md likewise identify this assignment as stage 1. The return needs routing to the applicable stage-1 review or an authorized stage-2 assignment, rather than a mathematical abandonment of a valid construction.

I re-opened all four statement dependencies in the current shared DAG. def-pur-flasque-support supplies the kernel defining supported sections and the pro-etale category; def-pur-kinjective-complex supplies the general ringed-site definition; prop-pur-kinjective-resolutions-exist supplies functorial resolutions with injective terms for a small ringed site; def-weil-abstract-derived-category explicitly supplies the cone terms and differential. The construction remains definition-only, so no proof-step citations are missing from the empty citations.json. Re-read slopmaster2 Supports.lean:96–160: its supportsUnit and supportsShortComplex take an already supplied complex in Sheaf X.smallEtaleTopology A. They still do not give an exact attachment for this pro-etale resolution construction. No statement or node change was justified by the returned stage-2 complaint.

Retried the exact mandated dry run from this sandbox, bounded externally to 60 seconds with SIGINT, with output saved in dry-run-repair-20261016.log. During that attempt the delivery process was observed in locks_lock_inode_wait at the sharedrepo.worktree entry; the same shared worktree lock already had other waiting delivery processes. No other process was stopped and no lock was deleted or bypassed. The retry does not supply stage-2 compilation evidence, regardless of its stage-1 preflight outcome. No delivery was pushed and no Lean, compiler, Lake, live-file edit, launcher edit, or sub-agent was used.

Retry outcome: timeout exit code 124 after 60 seconds. The captured traceback shows deliver.py:127 calling sharedrepo.worktree, sharedrepo.py:56 calling lock(prefix, "worktree"), and sharedrepo.py:22 interrupted inside fcntl.flock. No preflight check ran and no OK was printed. This is a confirmed delivery-tool lock blocker; the five stage-2 return requirements also remain unresolved under this stage-1 assignment.

## Current return audit by NO — 2026-10-16

The dispatched return is exactly the stage-2 return in `coord/returns/NO.md`,
for immutable head `de6b49de87e2`. Re-read delivery-errors B–E and H and
independently matched its numbered requirements:

- H1: no Lean module or `lean` record is supplied by this stage-1 package.
- H3: the source declarations at slopmaster2 Supports.lean:102,115,157 are
  explicitly over `X.smallEtaleTopology`; attaching them would fail the
  pro-etale category required here. They also take a supplied complex rather
  than the specified resolution. An exact pro-etale signature remains absent.
- H8: report prose and DAG source fields are not Lean declaration docstrings;
  the requested docstrings remain absent.
- H10: no compiler was run and no scompile evidence is claimed.
- H13: the four dependency statements give the required mathematical notions,
  but this package does not supply their requested usable Lean interfaces.

These five requirements are not repaired. The direct assignment says “only
stage 1” and “Never write Lean or run any compiler/Lake/build tools”; GOAL.md
and coord/brief-stage1.md repeat that scope. The stage-2 pilot in
coord/STATE.md is restricted to NA and defers pro-etale master-dependent
nodes. Thus it does not authorize this NO worker's pro-etale Lean repair.
An unchanged DAG split cannot resolve a stage-2 return, and I have not called
it READY or represented this audit as the requested Lean repair.

Re-opened the full statements of all four current dependencies. The support
node fixes the pro-etale site and the kernel; the K-injective definition is
for a general ringed site; the existence proposition explicitly provides
functorial resolutions with injective terms on a small ringed site; the
abstract-derived-category node writes the required target-first cone and
matrix differential. No proof steps or new nodes were introduced. In
particular no step citation, Mathlib search, or finished attachment has been
invented. The empty citations list still corresponds to the definition's
empty proof. The statement and node JSON remain as received because this
return identifies no stage-1 mathematical correction. Only this report and
the new dry-run log were written by the current audit.

Current dry-run outcome: the exact deliver.py NO def-pur-support-triangle
--no-push command was bounded to 45 seconds with timeout/SIGINT and exited
124. `dry-run-current-repair.log` records interruption inside
sharedrepo.lock's `fcntl.flock`, reached from sharedrepo.worktree before
preflight. While running, its process was observed in
`locks_lock_inode_wait`. No OK was printed. No lock was changed, no other
process was stopped, and nothing was pushed. This is still a delivery-tool
blocker in addition to the unresolved stage-2 scope conflict.


## Second reading by NO

This is the current independent stage-1 second reading, under the direct brief of 2026-10-16. The preceding stage-2 return audits and delivery-lock observations are historical; they do not change this assignment into stage 2. Only the prescribed stage-1 delivery will be attempted. The first worker's sections, including `## Review by NO`, are retained.

- Proof steps (none): checked `kind=definition`, `proof=[]`, `proof_deps=[]` against stages/1-dag.md §3(2) and the complete imported item statement. PASS: this node constructs complexes and a cone; the localization and distinguishedness assertions belong to other nodes. There are no proof-step citations, so `citations.json=[]` is correct.
- New nodes (none): checked all sandbox node paths against the shared DAG. PASS: the only node file is the existing item; B1–B7 introduce no new statement obligation. No elementary, duplicate, clause-restatement, or new Mathlib-leaf node was added.
- Item, site and input: compared its statement byte-for-byte with the imported DAG node and read the full statements of `def-pur-flasque-support`, `def-pur-conventions`, `def-weil-pbc-proetale-site`, and `def-weil-size-convention`. PASS: the pro-etale site, finite constant coefficient sheaf, closed immersion, complementary open, and bounded-below input are preserved. The primary blueprint file remains absent in the shared literature and both source checkouts; the existing WANTED entry remains a source limitation, not a claimed primary-source comparison.
- Item, resolution clause: read `def-pur-kinjective-complex` and `prop-pur-kinjective-resolutions-exist`, then sandbox `sources/derived.tex:9620` (070H, `definition-K-injective`), `sources/injectives.tex:1807` (079P, `theorem-K-injective-embedding-grothendieck`) and `sources/sites-cohomology.tex:3921` (07A5, `section-unbounded`). PASS: their statements apply to the ringed small site in the specified universe and provide K-injectivity, injective terms and a functorial choice. No bounded-below claim about I(K) is needed. The replaced etale-only definition really cannot supply this pro-etale notion.
- Item, A/B/C and u clause: read the entire kernel formula in `def-pur-flasque-support`. PASS: write r_M for the restriction unit; naturality gives r_{I^{m+1}} d_I^m = (j_*j^*d_I^m) r_{I^m}, so d_I restricts to the degreewise kernel and d_B u = u d_A. Applying the additive functors degreewise defines C. This is the explicit elementary well-definedness check; no exactness of j_* or derived comparison is used.
- Item, cone clause: read the cone terms and matrix in `def-weil-abstract-derived-category`, `sources/derived.tex:2471` (`definition-cone`), and pinned Mathlib MappingCone.lean:57,275,288. PASS: the off-diagonal term in degree m is u^{m+1}, and in the item's target-first coordinates the differential is (d_B^m b + u^{m+1}a, -d_A^{m+1}a). Its square is (d_B^2 b + d_Bu(a) - ud_A(a), d_A^2 a)=(0,0). The ordinary cone inclusion is b ↦ (b,0) and projection is (b,a) ↦ a in A[1]; these are chain maps by this formula. No identification of ordinary restriction with Rs^! is made.
- Existing-node/blueprint check: searched current DAG source tags 070H/079P and support/cone words, ran `blueprint_refs.py search 'mapping cone'` and `ancestor def-pur-support-triangle`, and read `def-pur-triangle-meaning`, `lem-pur-support-localization-triangle`, and `lem-pur-support-restriction-triangle`. PASS: they concern properties or a different supported-cohomology triangle, not this definition. The item remains its own blueprint id with null `from` and `same_as=[]`; no new-node ancestry is required.
- Existing Lean/Mathlib check: independently read slopmaster2 Supports.lean:96–160 and ran fresh msearch.py LeanFinder, Loogle and whole-Mathlib grep searches, with queries and actual outputs logged in `searches.jsonl` and summarized in the item's `mathlib_searches`. PASS: Supports.lean takes a supplied etale complex, and the generic Mathlib cones/resolution ingredients do not state this whole pro-etale construction. No attachment or new leaf is justified; no master sorry is used as a proof.
- Small cases: PASS for empty X (zero sheaf category), empty Z (A=0, cone=B), empty U (A=B, u=id, C=0), and X the spectrum of a field (both possible complementary pairs). For K=0 the specified I(0) can be a nonzero acyclic complex; the formulas and square-zero check remain valid. Degrees m=0,1 give B^0⊕A^1 and B^1⊕A^2, with the displayed differential landing in the next term. Coefficient stage n=1 requires no extra hypothesis.

Changes made in this second reading:

- Corrected the first review's zero-input sentence: a specified resolution functor need not preserve zero strictly.
- Added three independent, genuinely executed Mathlib searches and their inspected results; kept every earlier search record.
- Added this current review with the kernel naturality, cone maps, hypotheses and edge cases explicit. Kept the item statement, dependency split, empty proof and empty citations unchanged: no mathematical repair was warranted.
- The dependency-closure inspection also saw inherited live-DAG missing references and a cycle away from this item; those are not edits of this split. The required delivery preflight compares inherited findings with its baseline. No live file, tool, Lean source or compiler was touched and no agent was started.

Current required dry run completed successfully:

`python3 /home/ubuntu/weil-launcher-nt/deliver.py NO def-pur-support-triangle --no-push`

printed `OK (not pushed) deliver/NO/def-pur-support-triangle at 18682d6522: preflight passed`. The earlier worktree-lock blocker did not recur. No preflight failure required repair. The authorized final delivery command reruns preflight before pushing this reviewed stage-1 package. Counts: zero new nodes; zero new Mathlib leaves.
