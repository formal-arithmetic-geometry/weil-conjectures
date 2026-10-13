## What changed

Replaced the hole in `AlgebraicGeometry.derivedOpenStructure_evaluation_unit` by an
explicit composition of source transport, canonical evaluation on one, and the open
cohomology comparison. The proof verifies postcomposition naturality and identity
normalization without changing any existing definition or declaration signature.

Added `Sheaf.AlgebraicGeometry.DerivedStructureEvaluationOne`. Its definition
`AlgebraicGeometry.derivedStructureGlobalOne` constructs the global class of one through
single-complex homology and the ordinary-to-derived unit. Its theorem
`AlgebraicGeometry.derivedStructure_evaluation_one_bijective` is proved: ordinary
structure maps and homotopies are recovered from global sections; K-injective and
K-projective localization, projective-source truncation, and the naturality of the
derived unit show that the specified evaluation map is bijective. Private helpers
adapt the already proved calculations in StructureSheafHomotopyGlobalSections and
DerivedFreeModuleHomology because their public existential equivalences do not retain
the formula needed for normalization. No witness of an unproved existence theorem is
used to define any object.

Added the real definition `AlgebraicGeometry.openStructureRestrictionIso`, which
constructs the restricted structure-object identification using `extendSingleIso`,
termwise tilde, the derived single-functor comparison and the over-unit isomorphism.
Its body is fully proved. The remaining lemma fixes this concrete isomorphism rather
than asking for an unspecified source isomorphism.

Added `Sheaf.AlgebraicGeometry.OpenSectionsCohomologyComparison` for the remaining
comparison of the two cohomology computations, including the concrete unit class.
This comparison has no Hom-set equivalence in its statement. The original theorem
now follows by real Lean functoriality and composition of equivalences.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.derivedOpenStructure_evaluation_unit`
(node `lem-sc-derived-open-structure-sections-unit`). This is a reduction with one
lower hole, rather than a completed sorry-free proof of open evaluation.

Also proved the new theorem
`AlgebraicGeometry.derivedStructure_evaluation_one_bijective`
(node `lem-sc-derived-structure-evaluation-one-bijective`). Its definition and every
private helper are proved, with no `sorry`.

The sole hole added, and the sole textual `sorry` in the delivery, is
`AlgebraicGeometry.openSections_cohomology_unit_comparison`
(node `lem-sc-open-sections-cohomology-unit-comparison`). It is strictly a comparison
of cohomology and its explicit unit class; it does not assert the requested Hom
bijection. Its docstring supplies the full K-injective/scalar-restriction proof.
Holes closed: 1. Holes added: 1. Net: 0. The general evaluation component is proved.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology`
from the item. Its node `lem-pc-derived-structure-sheaf-hom-hypercohomology` is no longer
needed on this item's branch: the proof uses canonical evaluation bijectivity instead
of an unspecified existential natural equivalence. This also avoids this branch's
imports of DerivedStructureSheafGlobalSectionsHom and DerivedFreeModuleHomology;
their proved private calculations are used as reference and adapted in the new,
normalized proof. No claim is made that these modules are globally unreachable.

Removed the item's direct proof import
`Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`. Its node
`lem-sc-derived-open-restriction-adjunction-exact` remains needed by the new open
cohomology comparison module, which imports it. KoszulOpenSystem,
PrincipalOpenCechTotal, ExtendHomology and SingleHomology are still needed by the
item's unchanged definitions. Unit/chapter routes are unchanged; the unit's
`realized` record has no node assignment that this pruning bypasses.

## Where the brief, the DAG or earlier work was wrong

The old Hom/hypercohomology theorem gives only an existential family of equivalences
and naturality. Its public signature does not specify evaluation on one, so it
cannot establish the required identity normalization. The new proof retains that
formula throughout, rather than inferring a normalized value from an arbitrary
existential equivalence. The original statement is unchanged and no mathematical
counterexample was found. Edge cases: empty open/empty scheme and the zero ring give
zero module groups; no proof step requires a nonempty scheme, a nonzero ring,
quasi-coherence or boundedness.

The cited local Stacks source directory is absent on this machine. The official
Tag 09M1, 08BS, 06Z0, 079V, 0B6A and 08CX pages were read. Tag 09M1's first paragraph uses the general
perfect-object Hom formula; specializing the structure object gives the calculation
here. Tag 08BS explicitly proves preservation of K-injectives by open restriction.

## New nodes

`lem-sc-derived-structure-evaluation-one-bijective` records the proved canonical global
evaluation map. Its concrete global class of one is independent of open restriction.
The proof uses Mathlib and existing source-library tools, with no new holes.

`lem-sc-open-sections-cohomology-unit-comparison` records the remaining open restriction,
sections/scalar comparison and preservation of the explicitly constructed class.
It is a cohomology comparison, strictly below the item's Hom evaluation statement.
Tag 079V, rather than the older dependency docstrings' Tag 0B6A,
is the precise citation for the K-injective computation of derived sections.
Both new nodes are in `dag/nodes/sec-picard-framework/`. The parent node's proof and
proof dependencies have been updated to match the Lean reduction. No change records
are required: all existing signatures, visibility and definitions are unchanged,
and the new proof imports are non-public.

## Second reading by A4

1. Compared the entire item with the repository using `diff -u`. All eight existing
   declaration signatures and all seven existing definitions are byte-for-byte
   unchanged. The only item edits are two proof-import changes, a local elaborator
   option and the theorem proof. Neither new module exists in the repository.
   There are no forced adaptations or interface change records. Verdict: pass.

2. Compiled all three modules in import order with `lcompile.py --all`: no errors
   or warnings (21.8, 24.0 and 29.2 seconds). In a scratch module, printed axioms
   for every delivered public declaration. `derivedStructureGlobalOne`,
   `derivedStructure_evaluation_one_bijective`, `openStructureRestrictionIso` and
   the seven unchanged item definitions use only `propext`, `Classical.choice`
   and `Quot.sound`. The comparison and the original theorem additionally use
   `sorryAx`, exactly as reported. The only textual hole is the named comparison
   theorem; there is no forbidden declaration or hollow definition. The two new
   data constructions use concrete complex/homology isomorphisms and derived units.
   `Equiv.ofBijective` in private helpers selects uniquely specified inverses of
   proved bijections; resolution representatives are chosen only inside proofs.
   Verdict: pass as a decomposition, not a completed proof of the original item.

3. Read the complete signatures, bodies, docstrings and nodes of both new modules,
   and the official Stacks pages [08BS](https://stacks.math.columbia.edu/tag/08BS),
   [079V](https://stacks.math.columbia.edu/tag/079V),
   [09M1](https://stacks.math.columbia.edu/tag/09M1),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0) and
   [08CX](https://stacks.math.columbia.edu/tag/08CX).
   Tag 08BS applies to every open of every ringed space, so no compactness,
   quasi-coherence or boundedness hypothesis is missing. Tag 079V supplies the
   common K-injective computation. Scalar restriction leaves the underlying
   sections complex unchanged and is exact. The fixed source isomorphism uses
   the degree-zero single comparison, so sends the ordinary class of one to one;
   naturality of the resolution units gives the stated normalization.
   Tested the zero object, empty open (including the zero ring), total open, and
   a degree-zero sheaf: respectively both groups are zero, both groups are zero,
   the comparison is the global-sections/scalar identification, and the equality
   is restriction of the ordinary unit section. The remaining theorem contains
   no derived Hom assertion and removes the entire separately proved evaluation
   argument, so is a strictly smaller comparison problem.
   Fresh searches used different wording: LeanFinder on restriction of
   K-injective complexes and derived open sections returned ordinary restriction
   lemmas only; Loogle on `rightDerivedFunctorCompMapDerivedCategoryIso` and
   `mapDerivedCategoryHomologyFunctorIso` returned no indexed hits; grep located
   the ordinary over-unit isomorphism and overFunctorEquiv. Read the local
   derived composition implementations, RestrictedGlobalHomShiftedEquiv,
   RestrictedDerivedSectionZeroComparison, ScalarUnitCohomologyComparisonFamily,
   AffineSectionsSquareComparisonCoherence and FiniteAffineDerivedFactorization:
   these give ingredients or different statements, not this normalized comparison.
   Also searched both Lean roots and the upstream checkout. No exact duplicate
   or short complete replacement was found. Verdict: pass; comparison remains open.

4. Read the old dependency declarations and the concrete private calculations in
   StructureSheafHomotopyGlobalSections and DerivedFreeModuleHomology. Their public
   existential equivalences do not pin the evaluation formula, so the adaptations
   retain information needed here. The proof constructs evaluation bijectivity
   first, then uses the cohomology comparison, then proves both requested equations
   by functoriality. All new proof-only imports are plain `import`; new public
   imports support signatures or public definition bodies. The retained import of
   OpenRestrictionAdjunctionExact records the open comparison's still-needed proof
   dependency. Both old parent proof dependencies removed from its direct route
   are listed in No longer needed; open restriction remains below the comparison.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement and step
   lists are empty; no assigned unit node is bypassed. Blueprint searches across
   all chapters found no duplicate normalized evaluation or open-unit comparison.
   Verdict: pass; pruning is local to this branch, not a global reachability claim.

5. Matched the parent proof's three steps to source transport/comparison,
   canonical evaluation, and functoriality/normalization in Lean. Matched the
   new evaluation node to its proved ordinary Hom, homotopy, projective-source
   and K-injective arguments; matched the open node to its concrete isomorphism
   and sole remaining theorem. Each proof_deps list equals the union of step uses,
   and new nodes have the required source, search, created and verbatim Lean
   records. Found two metadata faults: new blueprint.from.node named the non-
   blueprint parent rather than its recorded blueprint ancestor; the comparison
   proof text's final sentence still referred to the parent's b rather than c.
   Corrected both, and added the evaluation node's missing statement dependency
   on the global-sections definition node. Verdict: pass after these repairs.

Second-reading changes: corrected the two new nodes' blueprint ancestry and via
chains; corrected the comparison node's normalization prose; recorded the global-
sections definition dependency. Lean proofs, definitions and signatures needed no
repair. No additional holes were closed or added: one original hole closed, one
lower hole added; net zero. The canonical global evaluation theorem is sorry-free.
