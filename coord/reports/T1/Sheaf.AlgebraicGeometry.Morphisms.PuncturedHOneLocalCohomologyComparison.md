## What changed

Replaced the proof of
`AlgebraicGeometry.Scheme.punctured_h_one_subsingleton_of_local_cohomology_vanishing`
with a compiling combination of two independent comparison statements. The existing signature
and docstring are unchanged. Added proof-only imports of
`Sheaf.Algebra.Homology.LocalCohomologyDerivedTorsion` and
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedHOneDerivedTorsion`.

The shared intermediate object is the second right derived functor of ideal-power torsion.
`Sheaf.Algebra.Homology.IdealPowerTorsionFunctor` constructs that additive endofunctor explicitly
from Mathlib's `Ideal.primaryComponent` and `Ideal.primaryComponent.map`. Its functor laws and
additive instance are proved. No data are selected from an unproved existence theorem.

The algebraic comparison identifies the Ext-colimit with derived torsion, for a finitely
generated ideal and an arbitrary coefficient module and degree. The geometric comparison
identifies puncture H¹ with derived torsion in degree two, without any Ext-colimit or vanishing
hypothesis. The original proof combines them using injectivity of both equivalences and the
given subsingleton hypothesis. Neither new statement is the original vanishing implication
under another name: one concerns only modules and Ext, and the other only the localization
sequence and derived torsion.

Updated the original node's proof, proof_deps, and proof_origin to match this combination.
All four delivered modules compile through lcompile.py. The new statements were checked on
zero coefficients, the zero and unit ideals, a field's empty puncture, and the zero ring
(the last cannot have the IsLocalRing instance required by the geometric statement).
For J=0 the torsion functor is identity; for J=R it is zero. The exponent-zero term is
zero in both the Ext diagram and torsion union, so there is no indexing discrepancy.
Scratch Lean checks also compiled without warnings: the primary component for the zero
ideal is top, that for the unit ideal is bottom, and the second derived torsion module
vanishes on injective coefficients. These checks are outside the delivered modules.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.punctured_h_one_subsingleton_of_local_cohomology_vanishing`
(node `lem-sbc-depth-three-puncture-h-one-comparison`). No sorry remains in the original module.

Added exactly two named holes, each the whole proof `:= by sorry`:

- `ModuleCat.nonempty_localCohomology_iso_derived_torsion`
  (node `lem-sbc-local-cohomology-derived-torsion`).
- `AlgebraicGeometry.Scheme.nonempty_punctured_h_one_addEquiv_derived_torsion`
  (node `lem-sbc-punctured-h-one-derived-torsion`).

This is a decomposition, not a net proof: one old hole closed and two lower holes added.
`ModuleCat.idealPowerTorsion` and `ModuleCat.idealPowerTorsion_additive` contain no holes.
The two remaining declarations have source references and complete proof plans in their
docstrings and nodes.

## No longer needed

Removed the redundant public import `Mathlib.Algebra.Category.ModuleCat.Basic` from the new
torsion-functor module: its API already arrives through `PrimaryComponent`; the scratch
module compiled with that import removed. No library module becomes unreachable.
The original module had no proof-dependency imports or proof_deps to prune. Both original
public imports remain necessary for its unchanged statement. Both newly added proof imports
are used. No unit statement or unit proof step is bypassed, and no unrelated module is imported.

## Where the brief, the DAG or earlier work was wrong

The original node's proof was one non-elementary paragraph with no proof_deps, so there were
no stated declarations from which to translate it directly into Lean. Its paragraph combines
two different comparisons, which this delivery separates at derived ideal-power torsion.

Mathlib's `localCohomology` uses the older projectively derived `CategoryTheory.Ext` construction,
whereas `Modules.H` uses sheaf Ext. Mathlib's LocalCohomology module explicitly lists comparison
with right derived functors as future work. Thus its same-radical isomorphisms do not close this
bridge. The new algebraic proof plan explicitly includes the balanced Ext comparison using
the first-quadrant Hom double complex and compatibility with quotient transitions.

LeanSearch returned Internal Server Error; this is recorded as unavailable. LeanFinder,
Loogle, and grep searches ran and their logs are in searches.jsonl. Searches of both library
roots and the DAG found no existing comparison. Blueprint searches for local cohomology and
punctured spectrum found no duplicate statement (the punctured-curve branch lemma is unrelated).
The ancestor script cannot follow created.item entries containing module names in this branch;
the new nodes therefore follow the existing blueprint.from chain to
`sbc-thm-spreading-finite-etale-galois`. The unit's realized arrays are empty and no route is changed.

## New nodes

`def-sbc-ideal-power-torsion-functor` records the explicitly constructed additive functor
M ↦ M[J^∞], using the existing Mathlib submodule, and the proved restriction-on-maps API.
Source: Stacks Tag 0BJA. Module: `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`.

`lem-sbc-local-cohomology-derived-torsion` states the algebraic Ext-colimit comparison, using
the finitely generated ideal hypothesis of Stacks Tag 0954, Lemma 47.8.2.
Module: `Sheaf.Algebra.Homology.LocalCohomologyDerivedTorsion`.

`lem-sbc-punctured-h-one-derived-torsion` states the geometric degree-one localization
comparison with derived torsion. Its plan uses flasqueness of associated injective modules
over a Noetherian ring, identifies the kernel of restriction by finite principal opens,
and applies the long exact sequence. Sources: Stacks Tags 0BK0, 0A6T, and 09T2.
Module: `Sheaf.AlgebraicGeometry.Morphisms.PuncturedHOneDerivedTorsion`.

No existing definition, statement, visibility, or public import changed. No change record
or forced adaptation is needed.

## Second reading by T1

1. **Existing interfaces: PASS.** Diffed the existing module against the repository. Its only
   changes are the two plain proof imports and the proof body. The original declaration's
   signature and docstring are byte for byte unchanged, including hW and hzero. The three
   other modules are new; no existing definition, visibility, target, or public import changes.
   The existing node diff changes only proof, proof_deps and proof_origin. No change record
   or forced adaptation is necessary.

2. **Kernel proof and construction: PASS, conditional on the two reported holes.** All four
   delivered modules compiled locally without errors or warnings. Scratch copies with
   `#print axioms` checked every delivered declaration. The torsion functor and its additive
   instance use only propext, Classical.choice and Quot.sound. Both comparison theorems and
   the original theorem additionally use sorryAx, precisely as expected from the two named
   holes. There are exactly two occurrences of sorry, both whole named theorem proofs, and
   no forbidden axiom, unsafe, opaque, implemented_by or extern declaration. The functor's
   object and maps are explicit Mathlib constructions. The original proof eliminates
   Nonempty equivalences only to prove a proposition; it defines no data from their witnesses.

3. **Split statements: PASS.** Read both statements and their complete docstring arguments,
   and independently checked the cited sources: [0954](https://stacks.math.columbia.edu/tag/0954),
   [0BK0](https://stacks.math.columbia.edu/tag/0BK0),
   [0A6T](https://stacks.math.columbia.edu/tag/0A6T), and
   [09T2](https://stacks.math.columbia.edu/tag/09T2).
   The first comparison is the purely algebraic Ext-colimit versus derived-torsion step;
   the second is the puncture localization step with no Ext or vanishing hypothesis. They
   are strictly separate parts of the original comparison argument, rather than the same
   vanishing implication renamed. Finitely generated J is sufficient for the first and
   Noetherian local R for the second. Independently recompiled the scratch checks that
   torsion for J=0 is top, torsion for J=R is bottom, and higher derived torsion vanishes
   on injectives. At q=0 the algebraic comparison identifies Hom(R/J^n,M)'s union with
   the torsion submodule; zero coefficients give zero on both sides in all degrees.
   For a field the puncture is empty and maximal-ideal torsion is the identity, so both
   degree-one puncture cohomology and degree-two derived torsion vanish. For an Artinian
   local ring the nilpotent maximal ideal likewise gives the identity functor and empty
   puncture. A zero ring is admissible algebraically but excluded by IsLocalRing
   geometrically. No edge case contradicts either statement.
   Repeated LeanFinder, Loogle and grep searches with different queries and searched both
   library roots. Results are recorded in searches.jsonl and the new nodes. The existing
   higher-direct-image versus H theorem handles a different comparison and supplies no
   ideal-torsion localization sequence. No duplicate or immediately applicable proof was
   found. Neither comparison can be closed by the available elementary API in a few minutes.

4. **Route and pruning: PASS after removing one redundant import.** Read the original node,
   its empty proof_deps, and sk-prop-input-spreading's realized record. No existing planned
   dependency or realized unit step is bypassed. The proof combines the two comparisons
   by injectivity and hzero; neither comparison alone proves the original implication.
   Both added imports in the original module are proof-only and used. Removed the redundant
   ModuleCat.Basic import from the new functor module after compiling a scratch copy without
   it. EnoughInjectives and RightDerived remain public because the new theorem signatures
   need their instances and API; removal trials failed with missing injective resolutions
   or missing rightDerived. No old node or module can be pruned. The hole accounting is
   one original hole closed, two lower holes added: decomposition, net minus one, not a
   completed axiom-free proof of the original theorem.

5. **DAG agreement: PASS after metadata repair.** The original node lists exactly the two
   comparisons applied by its Lean proof. The new definition node matches the explicit
   functor and additive instance; the two new comparison nodes match the named holes,
   sources, proof arguments, chapter, unit and blueprint ancestry. Their proof_deps equal
   the union of uses in their proof steps. Required creation and Lean records are present.
   Replaced the three new nodes' normalized one-line Lean statements with verbatim
   multiline signatures, and added the independent second-reader search evidence.

Changed only the redundant import, the new nodes' signature/search metadata, and this report.
The proof terms and theorem statements were retained.
