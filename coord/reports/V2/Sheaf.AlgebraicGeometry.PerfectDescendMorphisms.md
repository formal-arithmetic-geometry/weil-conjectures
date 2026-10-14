## What changed

Repair of reviewer X-34130's landing rejection: the four flagged private transport
lemmas have different meanings from the old transport lemmas. Renamed the local
constructions to recordedTr and recordedTrTo and their private helper lemmas to
recordedTr_assoc, recordedTrTo_refl, recordedTrTo_assoc and recordedTrTo_congr.
Their statements now explicitly bind the derived-category instances and identify
the recorded transport operations. The old private lemmas cannot be imported, and
use perfectHomComposition rather than recordedPerfectHomComposition. The latter
is the explicit original-counit lift, so substituting the former would undo the
comparison-data repair. No public statement or construction is changed by this repair.


Repaired AlgebraicGeometry.perfectDescentComparison: it now uses the explicit
original-counit composition lift, with equality transport along baseChangeMap_fst.
This is the explicit expression defining recordedPerfectHomComparison. Its signature,
visibility and abbreviation status, and the signature and all three clauses of
perfect_descend_morphisms, are unchanged.

Added DerivedPullbackRecordedComposition to retain the original universal presentation,
transport its tensor functor by equality, and construct the comparison by leftDerivedLift.
Its invertibility follows from the existing K-flat comparison theorem. Added
RecordedPerfectHomTransport: the existing conjugation/coherence proof is specialized
to these explicit lifts and their original counits. Added RecordedPerfectHomNormalization
and RecordedPerfectHomContinuity to state the change-of-counit identity and prove the
transfer of existing cofinal-tail Hom continuity by conjugation from that named identity.
The repaired main proof retains
the inverse descent and finite upper-bound arguments.

All five delivery modules compile through lcompile.py: 25.7s, 39.9s, 2.5s, 5.9s
and 23.1s respectively (the final main module exposes only the construction data).
The dry-run preflight is checked before READY. Caller-check results are recorded below. No push is authorized or performed by this worker.

## Proved and sorry left

Original local sorries: 0. Holes closed: 0. Holes added: 1,
AlgebraicGeometry.exists_recordedPerfectHom_normalization in the new module
RecordedPerfectHomNormalization. All other delivered declarations have complete proofs;
the repaired comparison contains no holed data.
This is a repair of undetermined data, not a net decrease in the sorry ledger.

Proved recordedDerivedPullbackCompositionLift_isIso, the recorded counit's universal
and K-flat properties, recordedPerfectHomMap_trans, recordedPerfectLimitMap_stage,
and recorded_perfect_hom_continuity from the named normalization intermediate.
The main theorem perfect_descend_morphisms and homMap_eq_iff are reproved using this API.
Printed axioms for recordedPullbackData, recordedDerivedPullbackCounit,
recordedDerivedPullbackCompositionLift, its invertibility, and
recordedPerfectHomMap_trans are exactly propext, Classical.choice and Quot.sound.
The normalization, transferred continuity and descent theorem also report sorryAx.
The comparison construction and its proved coherence do not depend on the new hole.

Edge cases: the continuity transfer is conjugation by natural isomorphisms and requires
no chosen morphism in an empty Hom set. The original counit lift is defined on every
scheme arrow, including identities and empty schemes. The n = 0 finite-equality
clause still obtains Nonempty I from the supplied stage j, so no nonemptiness assumption
is added. Source Tags 06YJ, 0D5S and 09RE were checked online because the local Stacks
source files are absent on this machine.

## No longer needed

This repair adds no imports and prunes no mathematical dependency. The ambiguous
private helper names tr, trTo, tr_assoc, trTo_refl, trTo_assoc and trTo_congr
are replaced by recorded names; no duplicate theorem about the old chosen
transport is introduced.


Removed the assigned module's direct proof import PerfectHomContinuity; the
construction and local proof use the recorded versions. Retained the original public
PerfectHomTransport import to preserve the assigned module's existing exported API.
Only DerivedPullbackRecordedComposition is added publicly for the new definition;
RecordedPerfectHomTransport is a proof import. The old modules remain needed inside
the normalization statement and
continuity transfer, so no complete target-closure module or old mathematical node
is claimed pruned. No lower affine or gluing theory is duplicated or re-proved.
The two old direct proof dependencies in the assigned node are replaced by the recorded
transport and recorded continuity nodes, which retain the old continuity route below them.

## Where the brief, the DAG or earlier work was wrong

The failed landing compared the text of private helper statements without their
private definitions. Here identical-looking tr/trTo expressions unfolded to distinct
composition comparisons. The repaired text exposes that distinction in every flagged
statement. This is not a renamed copy of a theorem about the old comparison.


The prior worker treated the absence of local sorry as a stale assignment. This item
is explicitly a repair of comparison data. The previous shared-abbreviation repair
made the same choice available to all callers but did not anchor its counit normalization;
coord/hollow-definitions.md correctly identifies the residual defect.

The change is documented in coord/changes/perfectDescentComparison-original-counit.md.
No unheld existing module is edited. No compiler error established a forced source
adaptation; the unresolved caller compilation timeout is recorded below. The unit
sk-thm-picard-semicon has no realized field containing this node; its route is unchanged.
Literal comparison data changes, so relevant target semantic review should be reopened;
target declaration text and the mathematical descent conclusion are preserved.

## New nodes

lem-pc-recorded-pullback-composition: the explicit lift from retained original counits
and its invertibility; module DerivedPullbackRecordedComposition.

lem-pc-recorded-perfect-hom-transport: conjugation, composition and finite-stage/limit
coherence for that construction; module RecordedPerfectHomTransport.

lem-pc-recorded-perfect-hom-normalization: the universal change-of-counit equation
relating recorded and old Hom maps; module RecordedPerfectHomNormalization. This
is the sole new named hole, with source and full natural-language proof. It has no geometric or continuity assumptions and is strictly an algebraic comparison step.

lem-pc-recorded-perfect-hom-continuity: transfer of the old continuity theorem through
the stated normalization equation; module RecordedPerfectHomContinuity. It proves
continuity from the normalization intermediate and asserts
neither inverse descent nor simultaneous finite relations. Only the normalization node is left sorry.

Change record: coord/changes/perfectDescentComparison-original-counit.md.

The two categorical subarguments (composition change via leftDerivedUnique and
leftDerived_ext, and conjugation cancellation via naturality) were compiled in scratch
files. The remaining formal glue is extraction of the old chosen composition's
factorization equation. Profiling exposed repeated large generated instance terms;
several typed interfaces and a structure packaging were attempted. The delivery does
not include unfinished or unused private proofs, nor split the module to evade its
compile limit. The full attempted proof is preserved in the non-delivered scratchpad.
The named normalization statement is strictly a categorical comparison step: it has
no finiteness, perfectness, directedness, descent or simultaneous-relations conclusion.

Caller validation: the first pass reported a 60-second Core timeout. The second
reader checked identical sources in both compile modes. Single-file Core
checks against the repaired overlay pass in 18.5 seconds, and Diagram passes
in 16.9 seconds. Compiling Core with output artifacts in a two-module run
times out at 60 seconds both against the repaired overlay and against the
unchanged shared baseline, in an isolated scratch sandbox with no repaired
modules. Thus the timeout has not been established as caused by this delivery.
A full rebuilt Core/Diagram check remains unavailable due to that existing
Core output-compilation timeout; the successful single-file checks do not
claim otherwise. This baseline issue is reported here for the maintainer.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered main module with the repository version. Existing public
   declarations retain their signatures; the changed `perfectDescentComparison` data
   and private `homMap_eq_iff` are documented by change records. Verdict: no accidental
   statement weakening or added hypothesis.

2. Compiled all five modules with `lcompile.py --all` (22.8, 40.7, 2.3, 5.8,
   and 23.9 seconds). A fresh scratch `#print axioms` check of thirteen declarations
   confirms only the three permitted axioms for the constructions and coherence;
   normalization, continuity, and descent additionally use exactly `sorryAx`.
   There are no forbidden
   declarations and no `sorry` in definitions. The sole remaining `sorry` is the named
   normalization theorem, with its matching node and proof docstring. Verdict: clean
   compilation with one explicitly split proof obligation.

3. Checked the normalization statement against the universal-property argument and
   searched Mathlib and the library for an existing equivalent. It is a strictly smaller
   categorical comparison and is true at identity, zero, and empty-Hom edge cases.
   Verdict: the split statement is needed and exactly scoped.

4. Read the proof downward. The continuity transfer uses the existing continuity route
   through conjugation, and the descent proof preserves the finite-family and inverse
   stabilization arguments, including the n = 0 case. Verdict: the unit route is kept
   and no shorter applicable theorem was found.

5. Checked every new node's Lean record, proof dependencies, source, and blueprint
   against the implemented declarations. Verdict: DAG and Lean agree; no module is
   claimed pruned without evidence.

Changed in this reading: added this required current review section. No proof or
   declaration was changed.

## Earlier second reading (a previous round; superseded)

1. Compared the sole existing delivered module with the repository using `diff`
   and the declaration parser. `perfectDescentComparison` keeps its exact
   signature, visibility and abbrev status; its data changes explicitly under
   `coord/changes/perfectDescentComparison-original-counit.md`.
   `perfect_descend_morphisms` keeps its exact public signature, including the
   conditional IsIso clause and the finite-family clause. The private helper
   `homMap_eq_iff` changes its RHS from the old to the recorded Hom map; this
   necessary private change is now explicitly recorded. No target or external
   declaration signature changes. Verdict: the public semantic change is
   declared, and the public descent statement is preserved.

2. Read all five modules and compiled them in import order with lcompile.py:
   29.2, 47.3, 3.3, 7.2 and 28.6 seconds, without warnings or errors. The only
   local sorry is the public named theorem
   `AlgebraicGeometry.exists_recordedPerfectHom_normalization`, whose proof is
   exactly `by sorry`. There is no hole in any definition and no forbidden
   axiom/unsafe/opaque/extern/implemented_by declaration. A scratch axiom check
   printed the original-presentation data, transported counit, universal/K-flat
   API, explicit lift, invertibility, composition isomorphism, Hom coherence,
   limit-stage coherence and perfectDescentComparison: all use only propext,
   Classical.choice and Quot.sound. The normalization, transferred continuity
   and descent theorem additionally use sorryAx, exactly as the report says.
   The original-presentation data comes from the *proved* exists_derivedPullback
   witness already defining derivedPullback; the new unproved normalization
   theorem is used in a proof, never to define data. Verdict: a concrete repair
   with one disclosed proof obligation, not a sorry-free descent theorem.

3. Read the sole remaining normalization statement and its complete docstring
   argument against Mathlib LeftDerived.lean (leftDerived_fac_app,
   leftDerived_ext and leftDerivedUnique) and the chosen family's defining lift
   equation in DerivedPullbackComposition.lean. For every arrow p, universal
   uniqueness identifies the two counits by a natural automorphism e_p. The
   factorization equations and naturality identify the composite lifts;
   inverting their comparison and cancelling the base-change automorphism
   gives exactly the stated conjugation, in its displayed orientation. This
   works also for identity arrows, scalar-rescaled counits, zero objects and
   empty Hom sets: it chooses no morphism from an empty set. It has no
   perfectness, geometric or colimit hypotheses, so it is strictly a
   categorical part of the repair, not a restatement of morphism descent.
   Independently searched with LeanFinder ('natural automorphism relating two
   universal derived functor composition systems'), Loogle (the fully
   qualified leftDerivedUnique), grep (leftDerivedNatIso/leftDerivedUnique/
   leftDerived_ext), and the local composition/Hom modules and upstream Picard
   source. The results supply the primitive universal-property lemmas, not
   this composition-system identity. Verdict: true, needed and strictly
   smaller; left open rather than claiming the unfinished scratch proof.

4. Read downward from the main proof. Surjectivity lifts a morphism and then
   its inverse; recordedPerfectLimitMap_stage keeps the first lift's image.
   Tail equality and directedness enforce both inverse equations at one
   stage. The finite-family branch uses its given starting stage to obtain
   Nonempty I even when n=0, so adds no hypothesis. The recorded continuity
   theorem conjugates the existing continuity result rather than repeating
   its affine/open-induction proof. The new public construction import is
   needed by the comparison definition; coherence and continuity are plain
   proof imports. The existing public PerfectHomTransport import deliberately
   preserves the original exported API, and is not a new proof-only public
   import. Both former direct proof dependencies are named under No longer
   needed but remain used transitively, so no module is claimed pruned from
   the target closure. Opened dag/units/sk-thm-picard-semicon.json: realized
   has empty statement and step entries; this node realizes neither, and no
   unit route is bypassed. Verdict: the original continuity route is reused
   below the repair; no shorter existing direct theorem found.

5. Opened all five delivered node files. The main node's three steps match
   lifting, inverse stabilization and finite equality. The construction node
   cites the existing lift-isIso result with exactly its universal and K-flat
   inputs; transport cites the existing comparison coherence theorem,
   specialized to these lifts. The continuity node cites normalization and
   the old continuity result; normalization records the universal comparison
   argument. proof_deps are the unions of their steps' uses, and proof_origin
   describes the implemented route. All new nodes have source, searches,
   created, blueprint, chapter/unit and Lean records. Read the online Stacks
   Tags 06YJ, 0D5S and 09RE: the first two supply K-flat computation and its
   successive-pullback comparison; 09RE supplies Hom continuity (perfect
   target objects meet its quasi-coherent clause). The normalization is the
   universal-property consequence explained in the docstring, not a claim
   that 0D5S literally states that formula. Verdict: the DAG matches the
   repaired proof.

Changed in this reading: made all four new node statements self-contained,
including the continuity node's directed ring diagram, colimit, all geometric
hypotheses, derived-category instances, perfect objects and both tail clauses;
added the normalization node's explicit derived-pullback statement dependency;
added missing module-level blueprint references to the construction and
normalization files; explicitly documented the private helper's necessary
change in coord/changes/homMap_eq_iff-recorded.md; distinguished successful single-file caller checks from the
output-writing timeout reproduced on the unchanged baseline. No proof or public theorem signature was changed by the second reader.
Holes closed: none (0 of 0 original local holes). Holes added: the one named
normalization theorem. This is a repair with net one additional hole, not proof
progress or a decomposition of an original local hole.

Additional change record: coord/changes/homMap_eq_iff-recorded.md, containing
the private helper's old and new signatures verbatim.

## Forced adaptations

- `lean/Sheaf/AlgebraicGeometry/DerivedPullbackRecordedComposition.lean` (current
  holder V2): landing reported that `recordedTensorPullback_additive` duplicated
  existing private statements `tensorAdditive` and `tensorPullback_additive`.
  Replaced that declaration with the strictly different
  `recordedPullbackData_additive`, which states additivity of the recorded witness
  functor; each tensor-pullback use now transports this result along
  `recordedPullbackData_E`.
- `lean/Sheaf/AlgebraicGeometry/RecordedPerfectHomTransport.lean` (current holder
  V2): its coherence callback referenced the removed duplicate theorem. Replaced
  only that callback with the same equality transport proof. Signatures and
  visibility of existing declarations are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared every delivered Lean module with the repository version. Existing public target signatures and the three clauses of `perfect_descend_morphisms` are unchanged; the comparison data change and private helper adaptation are covered by the existing change records. Verdict: no accidental statement weakening or added hypotheses.

2. Compiled all five modules with `lcompile.py --all`; all compile successfully. The only local `sorry` is the named theorem `exists_recordedPerfectHom_normalization`; no forbidden declarations or sorry-bearing definitions were found. Verdict: clean after repair, with the documented single split hole.

3. Checked the split normalization statement and its docstring against the universal-property argument and searched the local library for duplicates. It is a strictly smaller categorical comparison and handles identity, zero, and empty-Hom cases without arbitrary witnesses. Verdict: true, needed, and appropriately scoped.

4. Read the proof from the main theorem downward. The recorded continuity route preserves the original lifting, inverse stabilization, and finite-family arguments, including the `n = 0` case; construction and proof-only imports are separated. Verdict: route and pruning are consistent.

5. Checked the DAG records and proof dependencies against the declarations. The new nodes and sole hole match the implemented modules; no additional pruning claim is made. Verdict: DAG and Lean agree.

Changed in this reading (change record: `coord/changes/perfectDescentComparison-original-counit.md`): repaired `DerivedPullbackRecordedComposition` by binding transported additivity directly in the counit type and composition proof, and using typed local bindings in the counit lemmas. No duplicate standalone tensor-pullback additivity theorem is added. This was required for current standalone compilation; no declaration signatures changed.

Fresh axiom probes confirm only propext, Classical.choice and Quot.sound for the recorded construction, universal/K-flat properties, composition invertibility and Hom coherence; continuity and descent additionally use sorryAx as disclosed.


## Second reading by V2

1. Compared the main module and its node with the repository using diff; the other
   four delivered modules are new. Existing public signatures, visibility, and all
   clauses of perfect_descend_morphisms are byte-for-byte unchanged. The changed
   comparison body and private homMap_eq_iff RHS are explicitly covered by the two
   change records. Verdict: no accidental public statement change or weakening.

2. Read all five modules and compiled the delivery in import order with lcompile.py
   --all: 23.9, 47.1, 2.8, 7.2, and 26.3 seconds, without errors or warnings.
   A fresh scratch probe printed axioms for thirteen declarations: the recorded
   presentation, counit, universal/K-flat API, lift, invertibility, composition,
   Hom coherence, limit-stage coherence and perfectDescentComparison use only
   propext, Classical.choice and Quot.sound. Normalization, transferred continuity
   and descent additionally use sorryAx. A source scan finds exactly one sorry,
   in exists_recordedPerfectHom_normalization, and no forbidden declarations.
   recordedPullbackData projects the proved exists_derivedPullback witness that
   defines derivedPullback; the new unproved theorem selects no construction data.
   Verdict: concrete comparison repair with one disclosed proof obligation.

3. Checked the normalization formula against the old composition family's defining
   leftDerivedLift equation and the retained counits. leftDerivedUnique gives e
   with e.hom followed by the old counit equal to the recorded counit. Applying
   leftDerived_ext to the two composite counits gives the displayed comparison
   equation; inversion and naturality cancel the base-change automorphism and
   give the Hom conjugation in the stated orientation. The same argument works
   for identity arrows, zero objects, scalar changes of counit, and empty Hom sets.
   It has no geometric, perfectness, or continuity assumptions and is strictly
   smaller than descent. Fresh LeanFinder search used 'equivalence of universal
   counits induces conjugation of derived pullback morphisms'; Loogle found the
   fully qualified leftDerivedUnique; grep found leftDerived_fac_app and
   leftDerived_ext. Local searches also found ModulePullbackComparisonTargetAutomorphism,
   whose single-module/H0 conclusion does not provide this composition identity.
   Verdict: true and needed; the remaining extraction of the old chosen family's
   factorization is not a few-minute closure, so no unfinished proof was installed.

4. Read downward from perfect_descend_morphisms through continuity and transport.
   The proof reuses the existing continuity result by conjugation, lifts inverses
   on a tail, and stabilizes both inverse equations at a common upper bound.
   The finite-family branch obtains Nonempty I from its supplied j, including n=0.
   Statement/construction imports are public and new proof imports are plain;
   the existing public PerfectHomTransport import preserves the old exported API.
   No longer needed names both replaced direct proof dependencies, which remain
   needed transitively; no closure module is claimed pruned. The unit's realized
   statement and step lists are empty and the delivery does not change its route.
   Verdict: no shorter applicable route found and pruning accounting is accurate.

5. Checked all five node records against Lean, including the normalization
   docstring, new-node metadata, self-contained statements and declaration lists.
   Every proof_deps set is exactly the union of its steps' uses. Construction
   uses the existing lift-isIso theorem; transport uses the existing coherence
   theorem specialized to the recorded lift; continuity uses normalization and
   old continuity; the main node uses the recorded continuity/transport route.
   Verdict: the DAG records agree with the implemented proof and remaining hole.

Changed in this reading: appended this current independent review and retained a
fresh scratch axiom probe outside the delivery source tree. No Lean proof,
statement, definition, import or node was changed. Holes closed: none (0 of 0
original local holes). Holes added by the delivery: one, AlgebraicGeometry.
exists_recordedPerfectHom_normalization, node lem-pc-recorded-perfect-hom-normalization.
Pruned modules: none. This is a repair with net one added hole, not proof progress.
