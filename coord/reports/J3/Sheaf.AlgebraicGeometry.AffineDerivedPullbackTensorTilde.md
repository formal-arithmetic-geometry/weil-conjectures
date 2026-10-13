## What changed

Completed both remaining restriction proofs in
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`.
All six public statements, universes, visibility, and existing public imports are unchanged.

`derivedPullback_openRestriction_iso` uses composition of derived pullbacks and the
identification of derived open pullback with exact restriction. The composition proof
uses the existing `nonempty_tensorPullbackComp`, K-flat pullback preservation, and
K-flat resolutions. It supplies only the three local derived-category instances;
it does not assume a family of instances on all schemes.
`derivedTensor_openRestriction_iso` transports the existing monoidal model of derived
pullback through the exact-open comparison and applies Mathlib's curried tensor comparison.

The new private helpers are proved, with no postponed statement:
`tensorDerivedCounit`, `derivedPullback_comp_iso`, `derivedOpenRestriction_iso`,
`complexDerivedCounitIso`, `complexFunctorSquareIso`, and `complexDerivedSquareIso`.
The last three assemble the affine comparison over abstract categories, before
specialization to sheaves. Explicit shared sheaf-category parameters and the supplied
counit-isomorphism instance avoid repeated reduction of concrete sheafification and
module structures. All these helpers stay inside the item; no file was split.
The affine pullback proof reuses the counit extraction helper.
Added proof-only imports of Mathlib's PointwiseLeftDerived and the existing
DerivedPullbackMonoidalModel module. Updated the existing node's proof route and dependencies.
File-local irreducibility settings are documented in
`coord/changes/AffineDerivedPullbackTensorTilde-local-transparency.md`.

## Proved and sorry left

Closed both existing holes, belonging to
`lem-pc-affine-derived-pullback-tensor-tilde`:

- `AlgebraicGeometry.derivedPullback_openRestriction_iso`.
- `AlgebraicGeometry.derivedTensor_openRestriction_iso`.

No sorry remains in the item. No hole was added and no statement was split off.
The four existing affine comparisons and all private helpers have complete proofs.
This is a proof from existing declarations; their transitive import closure still
contains existing unfinished statements. This report does not claim that closure is proved.

## No longer needed

No original import was removed, and no globally unreachable module is claimed.
Removed the earlier sandbox's extra proof import of TensorPullbackAdjunction:
the ordinary composition comparison and basic adjunction already occur in TensorPullback,
which the existing public imports provide. The pinned sectionwise adjunction theorem
`lem-pc-module-pullback-adjunction` is not a direct proof dependency of this item.
The proof uses `def-pc-module-pullback` and
`lem-pc-module-pullback-identity-composition` instead.
The original direct proof dependency `def-pc-tensor-complex-sheaves` is mediated by
existing tensor comparison and monoidal model statements; it remains a statement dependency.

The general DerivedPullbackComposition and DerivedPullbackCompositionIsIso modules
are not imported: their interfaces require derived-category instances for every scheme.
DerivedPullbackOpenRestrictionUniverses is not imported because it already imports this item.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox had complete proofs but exceeded the current 60-second file limit.
The repair uses the existing ordinary composition theorem and assembles the whole
localized affine comparison in abstract categories. Abstracting only its separate
counit and degreewise parts still forced expensive concrete reductions when composing
them; the combined helper avoids that cost. An initial decomposition experiment was
removed because stage 3 forbids splitting a proof to evade the compile limit.
No mathematical statement or unit route changed. The unit's realized lists are empty
for this supporting node.

Empty opens, identity inclusions, identity ring maps, zero complexes, and unbounded
complexes are permitted by the unchanged hypotheses. The restriction argument is
formal adjunction/localization transport and does not require nonempty or affine opens.
Sources checked: Stacks Tags [08DW](https://stacks.math.columbia.edu/tag/08DW),
[08DX](https://stacks.math.columbia.edu/tag/08DX),
[0D5S](https://stacks.math.columbia.edu/tag/0D5S), and
[079U](https://stacks.math.columbia.edu/tag/079U).
No new data definition, arbitrary witness definition, or axiom is introduced.

Validation: the complete module compiled cleanly through lcompile.py in 52.2 seconds.
There is no sorry in the delivered item and no new module or node.
`deliver3.py J3 Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde --no-push`
printed OK: the dry-run commit compiled and passed preflight except for the second
reading, which the designated second reader supplies. Nothing has been pushed.

## Second reading by J3

1. PASS: compared the sole delivered Lean module with the repository using diff,
   and separately compared the exact text from each existing theorem name through
   its `:= by`. All six public signatures are byte-identical, with the same universes,
   hypotheses and visibility. There are no changed definitions or exported attributes.
   The transparency override is local and has its change record.
2. PASS: independently compiled the complete module through lcompile.py, cleanly in
   53.3 seconds. A scratch copy with `#print axioms` for all six public declarations
   and all eight private helpers compiled in 54.3 seconds. Axioms are restricted to
   propext, Classical.choice, Quot.sound and existing dependencies' sorryAx.
   derivedTensor_tilde_kFlat_natIso and the abstract comparison helpers have no
   sorryAx. No sorry or forbidden declaration occurs in the delivered module;
   no data definition or arbitrary existence-witness construction was added.
3. PASS: no statement was split off, no new module or node, and no new hole.
   Read all fully proved private helpers: the composition counit is invertible on
   K-flat representatives, and naturality transports this along localized resolutions;
   the remaining comparisons are adjunction uniqueness and formal natural-isomorphism
   compositions. Empty opens, identity maps and inclusions, zero complexes and
   unbounded complexes require no extra assumptions or exceptional case.
4. PASS: searched the library for open restriction and composition comparisons,
   and independently queried Loogle for IsLeftDerivedFunctor. Mathlib's
   leftDerivedNatIso and isLeftDerivedFunctor_of_inverts are already used.
   The existing composition theorem requires a global family of derived-category
   instances, whereas this item's hypotheses supply only the required local ones;
   the universe-general restriction module imports this item and cannot be used.
   Both added imports are proof-only and needed. The original imports supply the
   public signatures and the four retained affine proofs. The report lists the sole
   original proof dependency removed, def-pc-tensor-complex-sheaves. No original
   module is pruned. Read dag/units/sk-thm-picard-f-representable.json: its realized
   statement and step lists are empty; this supporting proof bypasses no realized unit.
5. PASS: read the original and delivered DAG records, checked each dependency's
   module and declaration, and checked that proof_deps equals the union of step uses.
   The six proof steps describe the Lean arguments and proof_origin records their
   sources. Only the authorized proof-route fields differ; there is no statement change.

Second-reading repairs: corrected stale affine proof-step numbers to steps 4–6,
and replaced the natural affine tensor theorem's outdated expanded proof description
with the actual composition of the existing K-flat and total-tensor comparisons.
No proof body, signature, import, definition or node needed repair.
