## What changed

Closed both remaining proofs in `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
The direct-image compositor is Mathlib's pushforward composition followed by the canonical
change-of-site isomorphism. Its scalar equation is `condensedPushforwardHom_comp` evaluated
on sections. Its uniqueness follows from the specified underlying section maps.

The transport theorem uses additive exact equivalences, normalized adjunction comparisons,
their compositor compatibility, and inverse-mate compatibility. It proves all displayed
unit, counit, finite exactness and actual base-change transformation equations.

The combined candidate already compiled within the standard limit (42.8 seconds).
The generic helper was then placed in its required new module, rather than leaving a new
public statement in the item. This relocation is not the performance repair.

To keep the complete proof within the standard compiler budget, ring, equivalence,
upperStar and adjunction carry explicit types but stay reducible abbreviations with their
published bodies; lowerStar is unchanged. The two square isomorphisms are stored with their
compatibility proof in a structure and projected back; their data are the same
compositor/equality/compositor expressions as before. All data are constructed, and every
proof field is proved. No source-library declaration is changed.
(Reviewer FIX 2026-10-25: the delivered version made these five operations ordinary `def`s,
re-packaged the equivalence as a structure literal and ascribed lowerStar's type; this hid
instances found through the abbreviations and broke the unchanged importers
OpenInternalKFlatMateNormalization, SectionDerivedTensorData and
SupportedCommonFieldScalarData. With the abbreviations restored the item compiles in 17.6 s
and 49 of 50 direct importers compile within 60 s; CartesianCoefficientTwists also times out
against the published module and compiles in 50.7 s with a longer limit.)

The new module `Sheaf.CategoryTheory.CompatibleSquareComponents` contains the public
generic square record, constructor and pasting theorem, with one node; the
public scheme squareData and upperComp_compatible belong to the existing transport node.
The change record is `coord/changes/D4-internal-module-operations-canonical-data.md`.
It records the conservative downstream user inventory, including current claim holders.
No existing theorem signature changes. The new generic data module is publicly imported
because the squareData definition exposes its record. Existing public imports are retained. No target statement changes meaning.

Validation: both final delivery modules compiled cleanly at normal compiler settings:
CompatibleSquareComponents in 6.2 seconds and the item in 46.9 seconds.
Unchanged SectionModuleOperationsData compiled against the repaired module in 5.0 seconds;
ScalarSixDefinitions compiled in 40.9 seconds. The canonical-data probe proves by rfl that the equivalence and both square maps equal
the original constructions (4.8 seconds). SectionDerivedPushpullNormalization timed out
both against the published original module and against this repair; it is an existing
consumer performance problem, not evidence of a forced adaptation.
ProEtaleSectionModuleFunctors also timed out; its unchanged baseline is being checked.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.ProEtale.InternalModuleOperations.lowerComp_existsUnique`.
- `AlgebraicGeometry.ProEtale.InternalModuleOperations.internal_module_operations_transport`.

Both belong to `lem-sfb-internal-module-operations-transport`. Zero sorries remain in the
item. Zero holes are added and zero statements are split off. All new helpers, structure
proof fields and the new node's theorem are proved.

## No longer needed

Removed the duplicate private import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.

The planned proof dependency `lem-sfb-section-ring-lax-pushforward-coherence`
(`Sheaf.CategoryTheory.SectionRingLaxPushforwardCoherence`) is unused. The already proved
concrete reconstruction, identity-on-sections comparison and Mathlib pushforward compositor
suffice. It is removed from this node's proof dependencies; its module and declarations
remain available to other users. No module is withdrawn, and no realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. Repeated definitional expansion of the
square composites was the main bottleneck in completing the proof within 60 seconds.
Storing the actual two composites and their compatibility together fixes this representation
problem. Merely writing the long proof or increasing tactic automation did not fix it.

The generic private adjunction-comparison helper now permits independent object and morphism
universes and reuses the existing normalized-comparison theorem. The ring-map reconstruction
reuses its already constructed monoid morphism rather than rebuilding its instance.

## New nodes

`lem-sfb-compatible-square-components` owns `square_pasting`, the
`CompatibleSquareComponents` record, and `compatibleSquareComponents`. It states and proves
the elementary pasting equation for two specified compositor squares and an equality of
indices. The record stores the actual prescribed composites; it neither chooses an
arbitrary comparison nor repackages an unproved transport theorem. The calculation uses
functoriality, cancellation of isomorphisms and associativity (Stacks Categories Tag 0B65).
LeanSearch, Loogle and local source search found related square and composition APIs;
the explicit record is needed to avoid repeating the large concrete kernel comparison.
All statements in this node are proved in this delivery.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
