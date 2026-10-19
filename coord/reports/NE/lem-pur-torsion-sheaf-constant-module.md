# Worker report: lem-pur-torsion-sheaf-constant-module

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-torsion-sheaf-constant-module.json`: statement, split; five proof steps, using only existing nodes. The mathematical statement is unchanged; its concluding proof-outline parenthesis has been moved into the proof.
- `citations.json`: one exact statement quotation for each node cited by each numbered proof step.
- `report.md`: this report. `searches.jsonl` is the log written by the required search wrapper; `prepare.py` is sandbox-local preparation code.

## New nodes

None: 0 new nodes and 0 new Mathlib leaves. Two existing Mathlib leaves supply all non-elementary ingredients: `lem-weil-pbc-zmod-module-structure-killed-by-n` and `lem-pc-sites-module-sheafification-interface`.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id, `zmodModule`, and ZMod/sheaf combinations, and the relevant `Mathlib/Algebra/Category` and `Mathlib/CategoryTheory/Sites` project extensions for annihilation and torsion terminology. The results include particular constant étale sheaves, roots-of-unity sheaves and group-level ZMod modules, but no project declaration giving both clauses for an arbitrary site. A special étale construction is not evidence for the site's general statement.

## Literature and WANTED

No WANTED documents. The shared repository contains the literature index, but its untracked Stacks and blueprint text is available read-only at `/home/ubuntu/weil-launcher-nt/literature/`. I read `stacks-project/sites-modules.tex`, labels `definition-presheaf-modules`, `definition-sheaf-modules`, and `lemma-sheafification-presheaf-modules`; the tags file identifies the last as 03CY and the presheaf-module section as 03CS. I also read the actual master blueprint `sec-smooth-purity/sk-def-sf-admissible/def-coefficient-twists-detailed.md`, the chapter record, and `dag/units/sk-def-sf-admissible.json`. This item makes precise the module structures and linearity underlying the roots-of-unity system used by that definition. It changes no chapter or unit route and is not the unit's key statement.

## What was wrong or incomplete

The imported item had no proof steps, and `blueprint.same_as` had not been searched. Its parenthetical sketch correctly suggested 03CY, but did not identify the existing node for the version where the coefficient ring is still a presheaf. That version is essential: `def-weil-presheaf-modules-sheafification` alone assumes the ring is already a sheaf. I now cite the existing `lem-pc-sites-module-sheafification-interface`, whose statement explicitly allows a ring presheaf and sheafifies it too.

The old sketch also did not show why the sheafification unit can be taken to be the identity or why an arbitrary module structure has the normalization on constants. The five steps give both arguments, and use the morphism factorization clause of 03CY to prove full linearity, not only linearity over globally constant sections. There is no statement dispute: no hypothesis or conclusion was changed. The obsolete proof-outline parenthesis was removed from the statement and realized as actual proof steps. The inherited grep-only Mathlib search record was replaced by the queries actually run in this session with the prescribed wrapper.

## Searches and reuse

All Mathlib searches in the delivered item were executed using `/home/ubuntu/weil-launcher-nt/msearch.py NE lem-pur-torsion-sheaf-constant-module ...`, and I read the hits. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. The first LeanFinder phrasing returned abelian-category and sheaf-cohomology facts; a second phrasing about sheafifying the constant ring returned `PresheafOfModules.sheafify`, `Sheafify.module` and the scalar-candidate construction. Loogle found `AddCommGroup.zmodModule` and, on the other query, the module sheafification and morphism universal property. The grep searches found the sheafification declarations and no ZMod/torsion/annihilator statement under `Algebra/Category/ModuleCat/Sheaf`. I read `Mathlib/Algebra/Module/ZMod.lean:44` (construction), :63 (additive maps preserve scalar multiplication), and the general sheafification implementation in `Presheaf/Sheafify.lean:203`, :328 and :380. These facts compose into the result but are not a one-line match for the entire item, which remains split.

Before considering any new node, I searched the whole DAG for 03CY, `sheafification-presheaf-modules`, and torsion/constant-module terminology, and used `tools/blueprint_refs.py search` with `constant module`, `03CY`, `killed by`, and `sheafification`. The ancestor command confirms `def-coefficient-twists-detailed`. The only same-content sheaf theorem I found in the DAG, `lem-weil-pbc-sheaves-killed-by-n-zmod-modules`, concerns the small étale site of a scheme, so it cannot prove the arbitrary-site statement here. Its already existing group-level child is exactly the algebra needed, so I reused it. The general ring-presheaf sheafification interface already exists as a Mathlib leaf; no duplicate or clause-restating child was created. No blueprint node states this entire arbitrary-site result, so `same_as` is empty.

## Unfinished work

None in this one-level split. No Lean was written, compiled or built. The sandbox is for an independent second reader; no push is authorized for this worker.

## Review by NE

I compared the item against Stacks 03CY, `sites-modules-lemma-sheafification-presheaf-modules`, with its full statement open. It permits any presheaf of rings, specifies abelian sheafification of the module, gives a unique compatible module action after both sheafifications, and gives the unique factorization of module maps into a module sheaf. The item is a corollary with coefficient presheaf the constant Z/N, not a claimed verbatim Stacks statement. I read every cited node's statement, rather than relying on its tag. I made no new nodes, so B1–B9's new-node requirements and tests for duplicate new nodes have no additional instances here; the existing notions used in the item remain explicitly cited, and JSON TeX is escaped only once when decoded.

For step 1 I read `def-weil-pbc-constant-sheaf`, which defines the constant sheaf as sheafification of the constant presheaf, and `def-weil-pbc-sheafification`, which gives the universal property. The step proves directly that an already sheaf-valued presheaf has identity as a sheafification unit. It does not take a theorem about local representatives or finite products from a mere definition node.

For step 2 I read all four numbered clauses of `lem-weil-pbc-zmod-module-structure-killed-by-n`. Clause (1) supplies the module action under exactly the sectionwise annihilation hypothesis in the item, and clause (4) makes restrictions linear because restrictions are additive. The explicit calculation for two integer lifts verifies well-definedness; identity coefficient restrictions give the presheaf compatibility. The step is elementary after this cited algebra leaf. It does not pretend that the constant presheaf is itself a sheaf.

For step 3 I read `lem-pc-sites-module-sheafification-interface` in full. Its presheaf coefficient hypothesis accepts P, its ring sheafification is exactly R by step 1, and its module's abelian sheafification may be the identity because F is a sheaf. Its uniqueness is explicitly uniqueness of the compatible action map, enough to conclude uniqueness on the fixed underlying F. This is a non-elementary application, marked as such; citing the smaller fixed-ring sheafification definition instead would have failed C4.

For step 4 I checked `def-weil-sheaf-of-modules-category`: each H(U) is a unital R(U)-module with the given addition. The constant sheafification map is a ring homomorphism. Clause (3) of the algebra leaf states exactly that an integer times the ring unit acts by the integer multiple. It gives the displayed N-annihilation calculation even if R(U) is the zero ring. This also checks the normalization for every possible module action, so the converse and uniqueness are not restricted to a chosen construction.

For step 5 the algebra leaf's clause (4) proves the component maps are linear over the constant coefficient presheaf. I checked that the sheafification interface's second assertion factors a presheaf-module map into a sheaf of modules over the sheafified ring. Its hypotheses are satisfied by G, with scalar restriction as established in step 4. The factorization equation has identity as its source unit by step 1, so the resulting R-linear map is the original h itself. This is the missing bridge from constant scalars to every section of R; it is supplied by a cited theorem, not by an unsupported claim that the extension is automatic. The converse on morphisms is precisely the module-category definition. All cited nodes have exact statement quotations in `citations.json`.

For section E I tested N=1, F=0, disconnected objects, and objects admitting the empty covering sieve. For N=1 the original annihilation hypothesis forces F(U)=0, and a unital module over the zero ring must likewise be zero; all five steps apply. The zero sheaf has the unique zero action. No connectedness, enough-points, finite-type, field-characteristic or invertibility hypothesis is used. Scalars of the constant sheaf on disconnected objects need not be globally constant; the 03CY factorization handles them, so the proof has no such hidden assumption. If the empty sieve covers U, the sheaf condition forces singleton sections of the abelian sheaf there; the identity sheafification and all module equations still hold. The zero ring is allowed throughout. Standard site sheafification is used in the same universe convention already implicit in the item's constant-sheaf definition; no small-index colimit or new universe assertion occurs.

I checked C1–C8 and D1–D5: every non-elementary claim is the statement of one of the two existing Mathlib leaves; there is no dependency on an internal construction of a cited proof, no off-route open tool theorem, no newly introduced clause of the item, and no induction or circular argument. The three steps marked elementary only unpack a cited definition or calculate from an explicit algebra leaf; the two 03CY applications are marked non-elementary. The only earlier worker failure was an empty sandbox, not a mathematical return: this delivery supplies the missing node copy, proof, citations and report. That was the status before the stage-2 return below; the return remains unresolved for the reasons recorded below.

## Earlier second reading (a previous round; superseded)

I reread the item against `sites-modules.tex`, Lemma 03CY (`sites-modules-lemma-sheafification-presheaf-modules`), and checked every hypothesis: an arbitrary site, a presheaf of rings and modules, ring and abelian-group sheafification, the compatible module action, and the unique factorization of module morphisms. The item specializes this lemma to the constant presheaf `Z/N` and an abelian sheaf; its two clauses agree with that specialization and add the explicitly proved torsion converse. The small cases `N=1`, the zero sheaf, disconnected objects, and an empty-cover object remain valid.

Step 1: checked against the definitions of the constant sheaf and sheafification; the identity on an already sheaf-valued presheaf satisfies the universal property. Verdict: elementary and correct.

Step 2: checked against all four clauses of `lem-weil-pbc-zmod-module-structure-killed-by-n`; lift independence, restriction compatibility, and the presheaf-module structure are explicitly supplied. Verdict: elementary and correct.

Step 3: checked against the full statement of `lem-pc-sites-module-sheafification-interface`; its presheaf-ring and abelian-sheafification hypotheses match, and its uniqueness gives uniqueness on the fixed underlying sheaf. Verdict: non-elementary application, correct.

Step 4: checked against the constant-sheaf ring map, the sheaf-module definition, and clause (3) of the Z/N algebra node; it proves `N x = 0` for every section, including the zero ring. Verdict: elementary and correct.

Step 5: checked against clause (4) of the Z/N algebra node and the factorization clause of `lem-pc-sites-module-sheafification-interface`; the identity unit from step 1 identifies the factorized map with the original additive map. Verdict: non-elementary application, correct.

There are no new nodes in this split. I checked the existing-node search against all DAG nodes for 03CY, constant-module, torsion, and sheafification terminology, and against the imported blueprint with `tools/blueprint_refs.py`; no duplicate or restatement node was added. The existing algebra and module-sheafification leaves say exactly what steps 2–5 use. I checked the JSON citations: every citation quotes a verbatim statement fragment, and every proof dependency is cited by a step. I changed no mathematical statement; the worker's former parenthetical outline is represented by the five explicit proof steps. The only second-reading edit is this audit section.


## Repair assessment: returned stage-2 requirements

The return is L's independent stage-2 review of immutable head
`0f1db12d3562`, recorded in `coord/returns/NE.md`. I read the entire
return and delivery-errors B–E and H. It asks for H1/H2 (a stage-2
Lean module and complete `lean` record) and H10 (`scompile` evidence).
These requirements remain unresolved, and this report does not claim
stage-2 completion.

- H1: no Lean module was added. This worker's explicit human decision,
  GOAL.md, and the isolated-run addendum to coord/brief-stage1.md
  authorize stage 1 only and prohibit writing Lean. The later pilot
  in coord/STATE.md supersedes that prohibition only for NA, two items;
  it does not include this NE item.
- H2: no `lean` record was fabricated. Reading the source again found
  no declaration giving both clauses for an arbitrary site. The
  roots-of-unity and constant-etale-sheaf declarations are special
  constructions, not attachments for the stated result.
- H10: no compiler, Lake, build, or scompile command was run. There is
  no permitted Lean module to compile, and the stage-1-only instruction
  explicitly prohibits compilation. A stage-1 packaging/preflight
  result cannot substitute for this evidence.

I reread Stacks 03CY, sites-modules.tex lines 815–875, and the full
statements of all five cited nodes. Steps 1–2 identify identity abelian
sheafification and construct the constant-presheaf module. Step 3
uses the existing module-sheafification leaf's unique compatible action
with O=P, O#=R, and the identity abelian sheafification of F. Step 4
uses the integer scalar identity to prove the converse. Step 5 uses
exactly that leaf's morphism factorization with identity source unit
to prove linearity over all sections of R. This covers disconnected
objects without treating their scalars as globally constant. The
N=1, zero-sheaf, and empty-cover cases introduce no extra hypothesis.
No mathematical correction is warranted by this return.

The local verification passed: five steps, ten verbatim statement
quotations, proof_deps equal to their uses, and all eight inherited
Mathlib search queries present verbatim in the existing wrapper log.
No new node or Mathlib leaf was added. The earlier assessment treated
the delivery tool's internal worktree operations as a reason to skip
the dry run. I am using the exact command explicitly prescribed in
this brief; no direct Git command or launcher edit was made.

The prescribed `deliver.py NE lem-pur-torsion-sheaf-constant-module
--no-push` stage-1 dry run printed:

    OK (not pushed) deliver/NE/lem-pur-torsion-sheaf-constant-module at c1d9c676ee: preflight passed

This is stage-1 preflight evidence, not H10 compile evidence. No delivery
was pushed. After recording this result, the same dry run is repeated
on the final report. The mathematical node, citations, and search log
remain unchanged.

Stage-1 outcome: READY. The isolated run authorizes stage 1 only, and the prescribed dry run passes. The stage-2 H1/H2/H10 review requirements are outside this item and remain deferred until stage 2 opens. No new nodes or Mathlib leaves.


## Second reading by NE

Independent reading on 2026-10-16. I opened delivery-errors B–E, GOAL.md,
coord/dag-sync.md, the item and every cited node, Stacks sites-modules.tex
03CY (lemma-sheafification-presheaf-modules), 03CT
(definition-presheaf-modules), 03CW (definition-sheaf-modules), and
sites.tex 0H7J (example-constant-sheaf). The item's arbitrary site,
positive N, sectionwise annihilation, normalization, uniqueness and full
linearity are a correct corollary of 03CY, rather than its verbatim
statement. No connectedness, points or invertibility hypothesis is needed.
The mathematical statement and proof text require no repair.

- Step 1: checked against def-weil-pbc-constant-sheaf and def-weil-pbc-sheafification; the identity on an existing abelian sheaf has the stated universal property. PASS, elementary.
- Step 2: checked against clauses (1) and (4) of lem-weil-pbc-zmod-module-structure-killed-by-n and Stacks 03CT; changing a lift changes ax by k(Nx)=0, and additive restriction maps commute with this action. PASS, elementary after the cited algebra leaf.
- Step 3: checked against the full statement of lem-pc-sites-module-sheafification-interface and Stacks 03CY; P is a commutative ring presheaf, R its ring sheafification, and F with identity unit is its own abelian sheafification. Compatibility is exactly the required normalization, so uniqueness is on the fixed sheaf. PASS, non-elementary application.
- Step 4: checked against the constant-sheaf ring unit, def-weil-sheaf-of-modules-category and clause (3) of the algebra leaf; eta(N mod N)=0 gives Nx=0 for every module sheaf, and eta(a mod N)=a times 1 gives normalization for every action. PASS, elementary.
- Step 5: checked against clause (4) of the algebra leaf, the morphism-factorization assertion of the sheafification interface and the module-morphism definition; h is P-linear, its R-linear extension composes with the identity to h, hence is h. This proves linearity for all R-sections, including those not globally constant. PASS, non-elementary application.
- New nodes: none. B1–B7, removal of elementary children and leaf conversion have no new-node instances. PASS: zero new nodes, zero new Mathlib leaves.

Small cases checked: N=1 forces the zero sheaf and a unital module over
the zero ring is zero; F=0 has its unique action; a field F_p as an
additive sheaf is allowed when p divides N; the empty scheme and any
object with an empty covering sieve have singleton abelian sections.
Disconnected objects are covered by 03CY without identifying all their
scalars with global constants. N=0 is excluded by the explicit N>=1
hypothesis. No statement dispute was found.

I read the recorded Mathlib sources: Algebra/Module/ZMod.lean:44,63;
Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:54,72,125,145;
and Presheaf/Sheafify.lean:203. These support the existing algebra and
sheafification leaves used in the split. My independent wrapper searches
are preserved as returned in searches.jsonl: grep
`Module.*ZMod|ZMod.*Module|IsTorsionBy` in Algebra/Category/ModuleCat
returned no hits; the LeanFinder query beginning "The forgetful functor
from modules over the sheafification of the constant finite cyclic ring"
returned condensed discrete-module functors and
SheafOfModules.fullyFaithfulForget. I read Sheaf.lean:68,74,90:
fullyFaithfulForget forgets only the sheaf condition into presheaves of
modules, whereas toSheaf forgets the action into abelian sheaves. It does
not state the item's torsion characterization. Loogle
`SheafOfModules, FullyFaithful` rejected the unqualified identifier
FullyFaithful; this is a query error, not absence evidence. The corrected
query `SheafOfModules.toSheaf` returned that functor, faithfulness,
additivity and limit/underlying-presheaf results, not the whole item.
There is no new exact Mathlib match to attach.

I also searched the current DAG for 03CY and the constant-module/torsion
terminology and opened lem-weil-pbc-sheaves-killed-by-n-zmod-modules,
new-constant-ring-module-sheaf-equivalence,
lem-weil-pbc-module-sheaf-constant-ring-equivalence, and
lem-weil-pbc-constant-module-sheaf-underlying: their scheme/small-etale
hypotheses or constant-object conclusions do not replace this arbitrary-site
result. Blueprint searches for "constant module" and "killed by" and the
ancestor query confirm the recorded origin in def-coefficient-twists-detailed;
I read its displayed roots-of-unity and transition-map definitions. The
source checkout searches found no exact arbitrary-site declaration to
attach. No sorry declaration of upstream master was used as a proof.

Changes in this reading:

- Corrected the presheaf-module definition tag from 03CS (the section) to 03CT (the actual definition) in all five proof-step source records, checked against stacks-project/tags/tags:4396.
- Appended this independent per-step review and preserved the first worker's sections, including Review by NE. The earlier stage-2 assessment is historical; this delivery is stage 1 only, as GOAL.md and the explicit brief require.
- Corrected the report's inherited citation-count typo: citations.json contains ten records, not eleven.
- Added only actual independent search calls to searches.jsonl. Left the correct statement, proof arguments, dependency list and ten exact quotations in citations.json unchanged. A local check verified every step/citation pair and equality of proof_deps with the union of uses.

Validation and delivery use the prescribed deliver.py, whose temporary
worktree operations are explicitly authorized by this brief. No direct git
command, Lean edit, compiler, Lake or build tool was run, and no live
project or launcher file was edited.

Second-reading dry run: the prescribed `deliver.py NE lem-pur-torsion-sheaf-constant-module --no-push` exited 0 and printed `OK (not pushed) deliver/NE/lem-pur-torsion-sheaf-constant-module at c092d03102: preflight passed`. This is stage-1 preflight evidence; no Lean compilation is claimed.

The first final-delivery attempt was not pushed: preflight reported `coord/blueprint-index.tsv: file outside the item's files`. That file is absent from the sandbox and was not edited by this reader. The delivery tool created its own temporary commit; I am retrying the same prescribed command once to distinguish a transient shared-reference update from a persistent tool failure, without editing the shared repository or launcher.
