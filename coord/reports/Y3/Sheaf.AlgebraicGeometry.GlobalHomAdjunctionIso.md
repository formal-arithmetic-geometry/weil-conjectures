## What changed

Partial repair of the original-counit normalization defect, now packaged in the
new module `Sheaf.AlgebraicGeometry.GlobalHomOriginalCounitNormalization`.
The existing `GlobalHomAdjunctionIso` declarations retain every signature and
data body. Its tensor-existence proof now uses the monoidal realization
components directly, avoiding a redundant `IsIso`/`asIso` reconstruction. This is substantive
Lean construction and compatibility work, not the rejected comment-only audit.
The two legacy definitions are deliberately not claimed as repaired yet.

`schemeHomOriginalTensorSpec` exposes EXACTLY the trailing existential in the
original specification of `derivedPullback`, retaining every field. Its proof is
the original projection. Proof irrelevance identifies the choices with the
original witnesses; this is not a fresh existential of universal counits.
`schemeHomPullbackCounitData` extracts that presentation, identifies its module
functor with tensor pullback by the recorded object/map equations, maps that
identification to homotopy categories, and transports the ORIGINAL counit.
`SchemeHomUniversalCounit` carries the counit and its named universal property.

`schemeHomOriginalPullbackAdjunction` applies the existing derived adjunction
construction to this original counit. `schemeHomPullbackCounitIso` is the universal
comparison from the composition presentation to this original presentation;
`schemeHomPullbackCounitIso_fac` and `_inv_fac` prove both counit equations.
`schemeHomOriginalTensorPullbackIso` transports the existing tensor iso by the
inverse comparison on its input and the tensor square on its outputs.
`schemeHomOriginalTensorPullbackIso_originalCounit` proves the representative equation,
the unchanged pure-tensor summand formula, and naturality. The coordinate equation fixes the normalization relative to the original datum.
The existing canonical predicate supplies uniqueness before transport; inverse
transport gives the corresponding uniqueness argument for the original datum.
A separate formal uniqueness theorem is not part of this delivery.

All existing signatures, data bodies, visibility and imports remain unchanged.
Only the tensor-existence theorem proof is shortened as explained below. In particular `schemeHomPullbackAdjunction` and
`schemeHomTensorPullbackIso` retain their legacy definitions: using the new
adjunction there immediately breaks a caller that relies on the still-unnormalized
base-change data. The new API provides the genuine construction needed for the
next coordinated repair. No protected SingleComplex module, target, upstream
composition or other group's module is changed. No forced adaptation is delivered.

## Proved and sorry left

Baseline: zero local sorries. Closed zero baseline holes, added zero holes,
zero split-offs. No delivered definition or theorem contains `sorry`.
The complete global Hom proof `schemeGlobalHomAdjunctionMap_isIso` is retained
verbatim; the already complete tensor-existence proof is shortened without
closing a hole. No net proof-hole progress or completed repair of the two
legacy entry points is claimed.

New fully proved theorems:
- `schemeHomCounit_comp_iso_leftDerived`;
- `schemeHomOriginalTensorSpec`;
- `schemeHomOriginalUnderived_eq`;
- `schemeHomCompositionCounit_isLeftDerived`;
- `schemeHomPullbackCounitIso_fac`;
- `schemeHomPullbackCounitIso_inv_fac`;
- `schemeHomOriginalTensorPullbackIso_originalCounit`.


The normalized data and these equations are recorded by the new node
`lem-pc-global-hom-original-counit-normalization`. Before second-reading repackaging, the combined module compiled cleanly in
49.7 seconds with the unchanged
60-second limit. Separating the module-functor equality and using a direct term
for the counit package avoided the expensive let-to-have transformation. Axiom
Artifact compilation also passed cleanly in 55.2 seconds. A separate importer
checked axioms of all 14 new public declarations: each uses only `propext`,
`Classical.choice`, and `Quot.sound`. The unchanged global theorem still has
`sorryAx` through existing dependencies, as before. The unchanged `MixedTensorPairingBaseChangeTransport` caller compiled against
the FINAL sandbox artifact in 34.8 seconds. The required final validation is
`python3 /home/ubuntu/weil-launcher/deliver3.py Y3
Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso --no-push`; its result is reported
by the tool and the final READY response, not by a claimed completed alias repair.

## No longer needed

None. Existing imports are unchanged; the new normalization module imports the
existing global Hom API publicly because its data construction uses that API. No DAG route, module or proof dependency is pruned.
The existing canonical-comparison and monoidal-realization construction is still
used, now with explicit counit transport. No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item has no local holes: the task is the queued normalization repair. The
previous comment-only delivery did not perform it. The original counit was not
addressable as a shared datum, and the uniqueness theorem for the old tensor only
pinned it relative to an independently chosen composition counit. This delivery
constructs the original-counit datum and the normalized adjunction and tensor,
and proves the latter's original-counit characterization.

A local alias switch is insufficient. With both legacy entry points temporarily
switched, 19 of 20 unchanged direct importers compiled, but
`Sheaf.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport` failed at its
base-change-mate equation (line 87). Its ORIGINAL baseline source compiles in
34.1 seconds; against the switched adjunction it cannot change the transpose to
`(p'.homEquiv _ _).symm (p'.homEquiv _ _ _)`. The base-change map still uses the
composition-counit adjunction. This is a mathematical normalization mismatch,
not a slow build or missing lemma. Merely asserting that equation would be wrong.

A scalar check explains the necessary coordinated repair: rescaling a legacy
counit by lambda rescales its adjunction counit by lambda and its Hom equivalence
by lambda inverse, while the old tensor scales by lambda inverse. Switching only
the adjunction breaks the mixed pairing; switching only the tensor breaks the
cancellation in the global Hom mate. The new tensor transport cancels all three
factors, as expressed by its proved original-counit coordinate equation. Consequently
both legacy entry points have been restored unchanged in the delivered file.

Remaining work: move/share the original-counit datum upstream, normalize
`DerivedPullbackComposition`, then the base-change map and mixed tensor/square
comparisons coherently, and finally switch the two global Hom entry points.
`SchemeDerivedBaseChangeMap` is held by D2 on this snapshot; the mixed tensor and
pairing modules are unclaimed. The forced-adaptation rule allows only necessary
proof/import/helper edits in nonheld modules, not this coordinated change of
upstream data definitions. No claim was acquired and no other holder was edited.

Edge cases: every new transport equation is proved without geometric or nonzero
hypotheses, including identity morphisms and zero objects. No false statement,
weaker theorem, target-signature edit, hollow definition or new axiom is supplied.
Sources read: official Stacks Project Tags 06YJ and 079U (literature files are not
present locally). The shared counit's universal property is proved, not assumed.

## New nodes

`lem-pc-global-hom-original-counit-normalization` records the fully proved
original-counit tensor characterization. Its source, dependencies,
Lean declaration and complete proof follow the actual construction. The original
global Hom node and its Lean record are unchanged. The new API is recorded by
the new normalization node in its own module.
Change record: `coord/changes/schemeHom-original-counit-normalization.md`.


## Second reading by Y3

1. **Existing interfaces: PASS.** Compared the whole delivered global Hom module
   with the repository using `diff -u`. Initially all existing declaration bodies,
   signatures and imports were unchanged, with added declarations interleaved.
   Moved the new API to `GlobalHomOriginalCounitNormalization`, as the brief
   requires for a new statement. The existing module and original DAG node are
   unchanged except for the tensor-existence proof simplification described below;
   the original DAG node remains byte-for-byte unchanged. No target, existing
   definition, or caller changes.

2. **Proof and data: PASS.** Read
   the original `exists_derivedPullback` specification and construction and the
   complete added proof. `schemeHomOriginalTensorSpec` retains every field of its
   trailing existential; proof irrelevance makes it the same choice proposition.
   The object/map equations give `Functor.ext`, and homotopy transport uses the
   induced transformation on both the hom and inverse. The counit's universal
   property is transported by Mathlib's Kan-extension iso theorem. The adjunction
   is selected from the already proved, normalization-pinned derived adjunction
   theorem. The unique derived comparison satisfies both displayed counit
   identities. The tensor iso is conjugated by inverse on the input and hom on
   both outputs. Its representative proof cancels this inverse and replaces all
   three counits; the chain iso and its degreewise summand equation are retained.
   No delivered source contains `sorry`, prohibited axioms or unsafe mechanisms.
   The independent scratch-copy axiom check and final compilation are recorded
   below. The unchanged global theorem retains inherited `sorryAx` only.

3. **New statements and edge cases: PASS.** No statements are split off and no
   holes are added. Read Stacks [06YJ](https://stacks.math.columbia.edu/tag/06YJ),
   [079U](https://stacks.math.columbia.edu/tag/079U) and
   [079W](https://stacks.math.columbia.edu/tag/079W): existence via K-flat
   representatives, the termwise total tensor comparison, and derived adjunction
   apply to arbitrary ringed-space morphisms, hence to all scheme morphisms here.
   No flatness, qcqs or nonzero assumption is introduced. Checked identity
   comparison: taking delta to be identity reduces the transport equation to its
   original hypothesis. For zero objects all compositions remain typed and the
   cancellation only uses iso components, never a nonzero hypothesis. A scalar
   change delta=lambda gives exactly one inverse input factor and two output
   factors, confirming the direction of transport. Searches with msearch grep
   (`NatIso.*mapHomotopyCategory|mapHomotopyCategory.*Iso`), Loogle
   (`Functor.IsLeftDerivedFunctor`, no hit), and LeanFinder (uniqueness of right
   Kan extensions after changing target by iso) confirm the generic infrastructure
   already used. Source search in Mathlib/HomotopyCategory.lean and the library's
   canonical tensor and K-flat counit modules found no original-witness
   normalization theorem to reuse. The private tensor transport lemma is the
   coordinate cancellation specialized to an existing tensor comparison.

4. **Route and pruning: PASS.** Mathlib supplies the universal comparison and
   target-iso transport; the existing global Hom tensor existence theorem supplies
   the canonical chain comparison. No alternate resolution or unproved existence
   witness is introduced. The new module has one public import, needed by its
   statement types and data bodies. Existing imports are unchanged. No old
   proof dependency is removed; `No longer needed` is complete. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step arrays
   are empty in this snapshot and remain unchanged; no realized route is bypassed.
   This is enabling API work, with zero net hole progress. The legacy repair
   remains outstanding and is explicitly not claimed complete.

5. **DAG and report: PASS after repair.** The old node is unchanged. The new node
   records the exact original-counit predicate theorem, its source, creation,
   searches, chapter/unit and actual proof. Updated its Lean module/file to the
   separate normalization module and added the existing global Hom node to the
   recorded dependencies, since its tensor existence theorem is used directly.
   The added API is fully proved rather than a renamed open item. The change
   record documents an additive API only; there are no forced adaptations.

Second-reading changes: separated the added API into its own module, restored the
original data bodies and node verbatim, corrected the new node's location and dependency
on the existing tensor theorem, and expanded this report. No existing signature or legacy normalization was altered. The existing
tensor-existence proof is shortened as described below.


Independent validation after repackaging: both repackaged modules compiled
without warnings via `lcompile.py`, in import order (25.6 s for the unchanged
original, 29.4 s for the new module). A scratch copy of the complete added proof
with explicit `#print axioms` for all 14 new public declarations compiled in
52.5 s: only `propext`, `Classical.choice`, `Quot.sound`; the unchanged global
Hom theorem reports inherited `sorryAx`. These checks close no baseline hole
and add no hole (proved 0 of 0 local baseline holes; 0 split-offs).


The first delivery dry run refused an unchanged claimed module. On re-reading
`exists_schemeHomTensorPullbackIso`, a genuine shorter route was available:
`canonicalPullbackTensor_monoidal_realization` already supplies the isomorphisms
`m.muIso`, so use their inverses directly as `NatIso.ofComponents`. Rewrite by
its equation `hm` for naturality and the canonical predicate. This removes the
intermediate natural transformation, local componentwise `IsIso` proof and
`asIso` reconstruction. Its theorem signature and proposition are unchanged;
proof irrelevance preserves any `Classical.choose` from that proposition, so
all existing data bodies and normalization stay fixed. The original node route
still uses exactly the same canonical-comparison and monoidal-realization
nodes. This is proof simplification, with zero additional proof-hole progress.


Final validation: `deliver3.py Y3 Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso
--no-push` printed `OK (dry run)` at commit `4adb137dc4`: both delivered modules
compile and the preflight passes, review class CODEX for the new proved API/node.
An earlier attempt was interrupted by another process's Git index lock; the
normal tool retry succeeded without removing the lock. The tensor-existence
proof simplification separately compiled cleanly in 24.1 s. The delivery command
below revalidates and pushes the same sandbox sources with this final report.
