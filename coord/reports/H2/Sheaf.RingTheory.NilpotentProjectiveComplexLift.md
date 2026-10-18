## What changed

Proved `CochainComplex.exists_projective_lift_of_nilpotent` with its signature unchanged.
The proof verifies the projective-class hypotheses, lifts the terms using the stated
projective-module lifting theorem, detects an upper cohomological bound, obtains a
bounded-above projective representative, and applies the existing class lifting theorem.
Nilpotent Nakayama and the quotient/tensor identification supply surjectivity reflection.

Added `Sheaf.Algebra.Homology.NilpotentModuleDerivedUpperBound`, proving
`DerivedCategory.isZero_homology_of_nilpotent_module_reduction` from the existing ring-site
upper-bound theorem. The adapter constructs the evaluation equivalence on the one-point
bottom-topology site, proves the natural scalar-extension comparison, transports the
right Kan universal property, and handles larger module carriers by `ULift` and the
induced quotient-ring isomorphism. The two supplied ordinary derived-category hom
universes remain independent. The returned duplicate private `DerivedCategory.point_eq`
declaration was removed; its four uses now contain the elementary unique-point equality
locally, so the imported `CategoryTheory.point_eq` statement is not redeclared.
No existing definition or statement changed.

The main proof also imports the large filtered free resolution, filtered free
K-projectivity, and generic resolving-class declarations. These give the derived
scalar-extension counit comparison on the bounded-above projective representative
without imposing a monoidal-category universe restriction. Updated the item's DAG
proof and dependencies to record that computation and the proved adapter.

## Proved and sorry left

Closed the original one hole:
`CochainComplex.exists_projective_lift_of_nilpotent`
(node `lem-weil-pbc-nilpotent-projective-complex-lift`).

Also proved the new adapter:
`DerivedCategory.isZero_homology_of_nilpotent_module_reduction`
(node `lem-weil-pbc-nilpotent-module-derived-upper-bound`).

There are zero `sorry` holes in either delivered module. Added zero holes and split off
zero unproved statements. This is a proof from existing stated dependencies, including
`DerivedCategory.isZero_homology_of_nilpotent_derived_reduction`,
`DerivedCategory.exists_boundedAbove_projective_model`, and
`Module.exists_projective_lift_of_nilpotent_ideal`; their existing holes are unchanged.
No claim is made that the target's full import closure is now axiom-free.

The combined server compile passed without errors or warnings: the adapter took
17.1 seconds and the item took 5.9 seconds. The assigned signature was also compared
byte for byte with the repository version and is unchanged.

## No longer needed

Replaced the item's direct proof import of
`Sheaf.Algebra.Homology.NilpotentDerivedUpperBound` with the proved ordinary-module
adapter. Also removed the unused public import of `Sheaf.Algebra.Homology.DerivedChangeOfRings`
from the item. Its only direct consumer, `PseudoCoherentNilpotentInvariance`, imports that
module independently. The site theorem and derived change of rings are still needed
transitively, so no mathematical dependency
or entire module is claimed pruned. All original five-hypothesis lifting steps remain.
The counit computation uses K-projective resolutions; no new K-flat computation or
bounded-flat replacement import was added to the item.

## Where the brief, the DAG or earlier work was wrong

The planned upper-bound input does not directly match the item: it uses
`RingSiteModules A` with carriers at the ring universe and a common derived hom universe;
the item uses `ModuleCat.{max u v} A` and independent hom universes `w`, `w'`.
These are mathematical equivalences, not definitional equalities. The new adapter proves
exactly the required transport instead of changing either existing signature.

The returned delivery was correctly rejected because its adapter redeclared the
same unique-point equality already present as `CategoryTheory.point_eq` in
`Sheaf.Algebra.Homology.RingHomExtensionTransport`. Private declarations are still
checked for duplicate statements. The repair removes that declaration and inlines the
proof at each use.

The class lifting declaration also needs a derived comparison for the reduction of its
chosen bounded-above representative. The earlier plan did not spell out that glue for
the supplied universal pair `(L, ε)`. The proof now constructs a derived pair using
K-projective resolutions, computes its counit on the representative, and uses uniqueness
to compare with `(L, ε)`.

The unit's realized statement and proof steps were retained. The resolving-class and
filtered-resolution declarations are generic algebraic tools; no theorem of the unit
was replaced. Edge cases checked in the argument include the zero ring, `I = 0`,
infinite projective modules, complexes without a lower bound, and unrelated derived
hom universes. No finiteness or bounded-below hypothesis was introduced.

## New nodes

`lem-weil-pbc-nilpotent-module-derived-upper-bound` records the proved ordinary-module
transport of the existing site lemma. Its single public theorem is strictly the
upper-bound-detection step, not the complex lifting conclusion. Searches of the imported
blueprint for the upper-bound phrase and Tag 0H75 returned no matching blueprint node.
LeanSearch returned tensor-quotient and ordinary cohomology-bound lemmas, Loogle returned
zero hits, and the Mathlib grep returned zero hits for nilpotent derived upper-bound
detection. The original site node was reused as the substantive proof dependency.
The import-pruning record is
`coord/changes/H2-nilpotent-projective-lift-imports.md`; no existing statement or
definition changed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
