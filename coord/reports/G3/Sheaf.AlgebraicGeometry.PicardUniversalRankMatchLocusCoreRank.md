## What changed

Repaired E2 from reviewer X-71f31 (head 71f319edd) in
`Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank`:
made `PicardUniversalRankMatchCoreCondition` an abbreviation of `PicardUniversalRankMatch`,
thereby adding exactly the missing pulled-back bundle-rank conjunct
and proved `picardUniversalRankMatchCoreCondition_iff` by `rfl`. Both existing theorem
signatures and all imports/visibility are preserved. Updated both theorem docstrings and
both existing node proof records: compatibility is definitional, while the existence
construction first fixes E's rank on open-and-closed base strata and constructs both
direct-image loci for that same rank. Removed the now-obsolete dispute comment.

Definition change record: `coord/changes/PicardUniversalRankMatchCoreCondition.md`, with
verbatim old/new definitions, the counterexample, all downstream users and their effects.
No target statement is changed and no downstream module is adapted.

## Proved and sorry left

Holes closed: 1 of 2, `AlgebraicGeometry.Scheme.picardUniversalRankMatchCoreCondition_iff`
(`lem-sc-picard-universal-rank-match-locus-core-compat`), by definitional reflexivity after
the explicitly recorded correction. This is a proof of compatibility for the corrected
predicate, not a proof of the false old implication.

Holes added / split off: 0. The sole remaining sorry is
`AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_core_rank`
(`lem-sc-picard-universal-rank-match-locus-core-rank`). Its signature is preserved but its
core predicate now includes the missing rank clause. Representability remains unproved;
this repair alone does not establish it. The docstring and node give the corrected
construction. No data is chosen from this unproved existence theorem in this delivery.

## No longer needed

No imports, existing nodes or modules are pruned. The compatibility proof no longer uses
the alleged inference of E's rank from equality of the direct-image ranks; it needs only
the two definitions. Its proof_deps remains empty. The unit
`dag/units/sk-prop-av-cube.json` has empty realized lists; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier compatibility claim was false: for X = Spec k disjoint union Spec k,
S = T = Spec k, g = identity and E = O_X, the two universal direct-image ranks are 2,
whereas E's rank is 1. The old core condition held but PicardUniversalRankMatch failed.
The corrected condition also fails on this example, so no false rank inference remains.
Empty test schemes still satisfy both conditions vacuously; rank-zero cases are kept.

The source fixes the bundle rank before imposing the two direct-image rank conditions;
it does not derive bundle rank from their equality. The old existence proof plan omitted
this necessary ordering. Both node proof records now reflect it. The previous rejected
split theorem remains removed; no new nodes are introduced. The stale prior second-reading
section was removed because it reviewed the disputed version, not this repair.

Source: [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP),
first three proof paragraphs. Downstream usage was checked with tools/downstream.py;
the corrected module and the unchanged downstream PicardUniversalRankMatchLocusCore
both compiled successfully using lcompile.py against the sandbox overlay. The downstream public
statement is still the original PicardUniversalRankMatch representability statement.

The explicit #print axioms check shows only propext, Classical.choice and Quot.sound
for the corrected definition and compatibility theorem. The existing existence theorem
still includes sorryAx, as reported above. The delivery dry run printed OK except for
the second reading, which the next worker writes; nothing was pushed.

## Second reading by G3

1. Compared the single delivered module with the repository using diff and checked both
   theorem signatures byte for byte: unchanged. The predicate's meaning changes explicitly
   under `coord/changes/PicardUniversalRankMatchCoreCondition.md`; this repairs the false
   compatibility claim rather than proving the old claim. No target declaration is changed.
   Read the actual unchanged downstream `PicardUniversalRankMatchLocusCore` proof: it uses
   the existence theorem followed by compatibility and still states the same full predicate.
   Compiled that original source against the corrected sandbox dependency. Verdict: pass
   as a recorded interface repair, not as proof-only mathematical progress.

2. Compiled the delivered module, an independent scratch copy with #print axioms for all
   three declarations, and the unchanged downstream source through lcompile.py. The
   predicate and compatibility use only propext, Classical.choice and Quot.sound. The
   existence theorem additionally uses sorryAx and is the only remaining named hole.
   No forbidden declaration, hidden sorry, hollow definition or newly chosen existence
   witness occurs. The Classical.choose in hO selects an adjunction, whose universal
   property determines its unit; it is unchanged. Verdict: pass with existence still open.

3. There are no new split-off statements or new nodes. Read Stacks Tag 0BDP, proof
   paragraphs on connected fibres, rank stratification, derived base change and the two
   lowest-cohomology loci. The remaining theorem's flat/proper/finite-presentation,
   universal structure-pushforward and finite-locally-free hypotheses support that route.
   Checked empty tests, rank zero, identity families, and the two-point counterexample:
   the last refutes the old compatibility but both corrected predicates fail together.
   The latter example need not satisfy hO, which compatibility never assumed.
   Verdict: the correction removes the false inference without adding a decomposition.

4. Compatibility's rfl is the shortest route. All six public imports supply notions in
   the public signatures or predicate; there is no proof-only public import to repair.
   Searched lean/Sheaf and upstream algebraic geometry with rank-locus/cohomology terms
   and ran msearch grep for "lowest cohomology rank immersion" (zero hits). Inspected
   upstream PerfectLocusOfRank.lean: its open-locus characterization additionally requires
   vanishing in every other cohomological degree, so it cannot prove this degree-zero-only
   immersion statement by specialization. The full rank-locus and core theorems depend
   on this item and cannot be used without a cycle. No quick closure found. Old proof_deps
   are empty, so No longer needed is complete. Read sk-prop-av-cube.json: its realized
   statement and step lists are empty, and this repair changes no unit route. Verdict: pass.

5. Compared both existing node files. Only proof and proof_origin change; proof_deps stay
   empty, correctly matching rfl for compatibility and no implemented proof for existence.
   The existence record remains a source-based plan, not a claim that its construction is
   formalized. The declaration names and Lean statement records match the file. No new
   node requirements apply. Verdict: pass.

Second-reading change: consolidated the corrected duplicate predicate into an abbrev of
PicardUniversalRankMatch, following stages/3-proving-and-pruning.md §3. It is definitionally
identical to the worker's three-conjunct correction, retains both theorem signatures and
rfl, and prevents the two predicates diverging again. Updated the change record's exact
New text and this report; added no theorem or hole and pruned nothing.
