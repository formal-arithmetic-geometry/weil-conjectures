## What changed

Proved `CommRingCat.integrallyClosed_of_localization_cocone` using a proved private
finite-family lifting helper, Mathlib polynomial `scaleRoots`, filtered-colimit
zero detection and stagewise integral closedness. Added the missing `IsColimit c`
and stage-domain hypotheses. Restored the same domain hypotheses to
`CommRingCat.filtered_colimit_localization_isIntegrallyClosed`, and adapted its
only caller in `Sheaf.RingTheory.FilteredColimitNormalRing` by passing its existing
`hF` directly. The parent `isNormal_of_filtered_colimit` statement is unchanged.
Added proof imports `Mathlib.RingTheory.Polynomial.ScaleRoots` and
`Sheaf.RingTheory.FilteredColimitIsDomain`. Updated both node proofs and Lean signatures.
Change record: `coord/changes/filtered_colimit_normal_integrally_closed.md`.

## Proved and sorry left

Replaced the one false original holed statement,
`CommRingCat.integrallyClosed_of_localization_cocone`
(node `lem-weil-pbc-filtered-colimit-normal-ring-integrally-closed-common-stage`),
with a proved, explicitly recorded correction for a colimit of normal domains.
This is a statement correction, not a proof of the original signature. This does not prove the false
old cocone statement or the stronger integral-closedness-only generalization.
`CommRingCat.filtered_colimit_localization_isIntegrallyClosed` remains proved,
now for the normal-domain hypotheses needed by the parent.
No holes added, split off, or left in either delivered module.
The private helper `lift_fin_after` is fully proved. The common-stage theorem uses
only standard axioms; the localized theorem depends on the existing
localization-colimit construction, now explicitly constructed and proved in
`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrimeData`.

## No longer needed

No imports or planned nodes pruned. The original common-stage node listed no proof
dependencies, but its proof requires the already-proved
`new-filtered-colimit-domain-cocone` (`Sheaf.RingTheory.FilteredColimitIsDomain`).
The localized theorem uses the localization-colimit node and the common-stage node.
No unit route is bypassed; neither corrected node realizes a unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The helper omitted the colimit hypothesis. A cocone from the constant diagram on Z
can have point Z[√5], which is not integrally closed: (1+√5)/2 is integral but absent.
This makes the old statement false. The localized theorem and helper also omitted
the domain hypotheses used in the source's fraction-field argument. Stacks Tag 037D
explicitly reduces to normal domains. The delivery restores that case and records
the stronger generalization as unproved; it changes no project target.

Both node statements have `statement_change` records listing all DAG citers.
The parent normal-ring node is the sole citer of the localized node and supplies
both hypotheses already; the common-stage node has no recorded DAG citers.
The zero-coefficient-family case is handled by staying at the supplied stage;
no injectivity of transition maps is assumed. The denominator stays nonzero because
its image in the colimit is nonzero. The filtered category is nonempty by IsFiltered.
Searches through leanfinder, loogle, launcher grep, and local source rg found no
direct colimit integral-closedness theorem. Source read: https://stacks.math.columbia.edu/tag/037D.

Validation: both modules compile warning-free through `lcompile.py --all`.
`deliver3.py --no-push` completed local compilation and axiom probes, then failed
preflight because the adapted parent module is unclaimed. The explicit worker brief
forbids running `tools/claim.py` manually and says deliver3 handles necessary steps;
deliver3 did not create that claim. No push was attempted. The other reported reason
is the intentionally absent second reading, which belongs to the second reader.
The dispatcher must claim `Sheaf.RingTheory.FilteredColimitNormalRing` before the
second reader reruns the dry run and supplies its reading.


Retry validation: the worker reran `deliver3.py --no-push`; both local compilation and
axiom probes succeeded. Preflight again reported the unclaimed adapted parent and the
second-reading section reserved for the independent second worker. No manual claim,
preflight bypass, or push was performed. The sandbox remains ready for the dispatcher
to arrange the adapted-module claim and the independent second reading.


Repair validation: deliver3.py --no-push now rejects the attempt before compilation with
"nothing is proved" and an empty original-sorry list, although the repository source
still contains the original common-stage sorry. Its early comparison uses the current
clone working tree, which a preceding dry run can leave containing this same delivery,
instead of the fetched sheaf-dag baseline. The independent second-reading section
remains reserved for the second reader. No push was attempted.

Latest repair dry run: local compilation and axiom probes completed, but preflight
still rejects the forced adapted parent as unclaimed, together with the absent
independent second reading. The wrapper did not acquire the required claim. The
worker brief forbids manual claims and writing the second-reader section, so this
requires dispatcher/tool repair. No proof files were changed in this repair turn.

## Second reading by S1

1. Compared both delivered modules with the repository by diff. The two changed
   signatures are exactly those documented in the change record and node
   statement_change fields; no definition or project target changes. The original
   cocone assertion is false (the Z to Z[√5] cocone is a counterexample), so this
   delivery corrects it rather than claiming its original signature was proved.
   The sole caller adaptation passes its already available normal-domain
   hypothesis; the parent theorem's signature is byte for byte unchanged.
2. Compiled both files through lcompile.py --all without errors or warnings.
   No sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition
   occurs in either delivered file. Reviewed the numerator/denominator lifts,
   monic polynomial reconstruction, scaleRoots clearing, later-stage zero
   detection, denominator nonvanishing and final cancellation. Explicit axiom
   checks are recorded below. Localization data are explicitly constructed in
   the existing dependency; its maps are also uniquely fixed by restriction to
   the original rings, so there is no arbitrary data from an unproved existence.
3. No statements were split off and no holes added. The proved private helper
   covers Fin 0 by the original stage and Fin (n+1) by filtered common successors.
   Degree zero is handled by the same polynomial reconstruction; no transition
   map injectivity is assumed. A fresh launcher grep search for scaleRoots and
   integral closedness with DirectLimit, and rg on lean, found no replacement for
   the common-stage proof. The first worker's leanfinder/loogle searches agree.
4. The proof follows the common-stage normal-domain argument of Stacks Tag 037D
   (https://stacks.math.columbia.edu/tag/037D), independently read. The two new
   proof imports are plain imports and are used. No old proof dependency is
   discarded. Neither corrected node occurs in sk-thm-p1's realized route;
   localization and the parent normal-ring route remain in use.
5. Both node statements and lean.statement records match the declared corrections.
   proof_deps matches the domain theorem for the helper and localization plus
   common-stage theorem for the localized result. No new nodes need validation.
   The statement_change records name the existing DAG citers. Their author labels retain the
   mandatory “S1 stage 2” statement-change schema, although this is stage-3 work.

Second reader changes: corrected progress accounting to distinguish the false
original statement from its proved correction; updated the stale dependency-hole
note. No proof code was rewritten.

Explicit scratch-copy #print axioms checks: integrallyClosed_of_localization_cocone,
filtered_colimit_localization_isIntegrallyClosed, and isNormal_of_filtered_colimit
all use exactly propext, Classical.choice, Quot.sound, with no sorryAx. Scratch
copies were removed before delivery.

The first second-reader dry run found only a metadata-schema error introduced
by this reading: statement_change.by requires the literal stage-2 format even
for stage-3 corrections. Restored the schema labels and reran the gate.

Second-reader dry run succeeded: deliver3.py --no-push printed OK and review class
CODEX. Its counterfactual compile verified that the original parent compiles with
the baseline, fails with this changed dependency, and the one-line adapted parent
compiles. The sole changed line passes hF in place of its second projection; it
is necessary and no unrelated edits occur. The earlier unclaimed-adaptation
blocker is resolved by the forced-adaptation exception implemented in the tool.

## Forced adaptations

### Sheaf.RingTheory.FilteredColimitNormalRing
Original against changed dependencies failed:
```
/tmp/forced-adaptation-otol2kb7/lean/Sheaf/RingTheory/FilteredColimitNormalRing.lean:57:70: error: Type mismatch
  (hF i q).right
has type
  IsIntegrallyClosed (Localization.AtPrime q)
but is expected to have type
  IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)

(with the modules compiled into /tmp/forced-adaptation-otol2kb7/.lbuild) [3.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
