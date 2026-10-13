## What changed

The target module now obtains the point direct-image unit from
`RingedSpace.isIso_moduleDirectImage_unit_on_kInjective` and transports it using the
new `AlgebraicGeometry.globalSections_unit_isIso_of_point_unit` theorem. The transport
module records the categorical comparison step and leaves that step as one named hole.

## Proved and sorry left

Closed `isIso_directImage_globalSections_unit_on_kInjective` by applying the point-unit
transport theorem and the successive direct-image acyclicity theorem. One sorry remains:
`globalSections_unit_isIso_of_point_unit` in
`GlobalSectionsPointUnitTransport.lean`, node
`new-global-sections-point-unit-transport`.

## No longer needed

No imports or proof-dependency nodes were removed.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan suppresses the substantial categorical comparison between the
point direct image and the global-sections functor. This delivery makes that comparison
an explicit named intermediate theorem.

## New nodes

`new-global-sections-point-unit-transport` is added for the explicit transport theorem;
its Lean module is `Sheaf.AlgebraicGeometry.GlobalSectionsPointUnitTransport`.

## Second reading by T2

1. **Statements and accidental changes.** Compared both delivered modules against the repository. The
existing target theorem signature is unchanged; the added transport theorem is a separate statement.
Verdict: passed.

2. **Compilation and axioms.** Compiled both files with `lcompile.py --all`; compilation succeeds. The
only remaining `sorry` is the explicitly named transport theorem
`AlgebraicGeometry.globalSections_unit_isIso_of_point_unit`, and no forbidden declarations or hollow
definitions were introduced. Verdict: passed.

3. **New statement review.** The transport theorem assumes exactly the point direct-image derived-unit
isomorphism and concludes the corresponding global-sections unit isomorphism at the same direct image.
Its categorical comparison proof is documented and represented by node
`new-global-sections-point-unit-transport`; no duplicate declaration was found in the library. Verdict:
passed, with this theorem necessarily split off as the unresolved comparison step.

4. **Route and pruning.** The target proof uses the point direct-image unit theorem and the transport
step, preserving the unit route. The transport module's unused public import of
`RingedSpaceDirectImageKInjectiveAcyclic` was removed; no proof-dependency node is otherwise obsolete.
Verdict: passed.

5. **DAG agreement.** The target node proof now records the transport and point-unit applications, and
`new-global-sections-point-unit-transport` records the split theorem, module, declaration, source, and
blueprint linkage. Verdict: passed.

### Changes made during second reading

Replaced the target proof's proposition-valued `letI` with `let` (which still supplies the required
instance) to remove the style warning, and removed the unused public import from the transport module.
