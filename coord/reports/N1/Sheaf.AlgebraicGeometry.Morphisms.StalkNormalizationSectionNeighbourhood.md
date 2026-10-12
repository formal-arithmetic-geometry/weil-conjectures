## What changed

Replaced the sorry proof of
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_section_neighbourhood`
with a complete Lean reduction to two dimension-specific, source-local calculations.
The existing signature, universes, visibility, hypotheses, conclusion and docstring are unchanged.

The new modules are
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource` and
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource`.
Each states only source etaleness at points above the closed section point, respectively
under local Krull dimension less than two and at least two. Neither constructs the target open.
Their statements retain the concrete normalization and all geometric input.

The private helper `etale_shrink_of_fibre_source_opens` is fully proved from Mathlib.
It takes the union E of the source etale opens, removes the closed image of its complement,
and proves etaleness over the resulting target open using source locality and cancellation
of the target open immersion. The main proof splits the dimension cases, obtains the
source neighbourhoods, and applies this helper. The existing DAG node now records that route.
All three delivered modules compile together without errors or warnings.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_section_neighbourhood`
(node `lem-sbc-stalk-normalization-section-neighbourhood`).

Added two named holes, each exactly `:= by sorry`, each in its own new module:

- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_trait_section_source`
  (`lem-sbc-stalk-normalization-trait-section-source`).
- `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_depth_two_section_source`
  (`lem-sbc-stalk-normalization-depth-two-section-source`).

No sorry remains in the assigned module or its private helper. This is a decomposition,
not an unconditional proof: one upper hole closed, two strictly case-specific lower holes added.
The helper is an independent complete proof of the target-open extraction step.
No data definition, axiom or existing statement was added or changed.

## No longer needed

Removed these four direct proof imports from the assigned module:

- `Sheaf.RingTheory.NormalLocalDepthTwo`.
- `Sheaf.RingTheory.FlatLocalDepthFormula`.
- `Sheaf.AlgebraicGeometry.Morphisms.NormalIntegralGenericHomFull`.
- `Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension`.

They are replaced by the two new ordinary proof imports. At second reading, the
old dependency modules were imported ordinarily in the new source-calculation modules,
matching their recorded proof plans. All four therefore remain in the import closure;
they are not claimed as globally unnecessary or pruned. The trait case does not require the depth-two
or flat-depth-formula nodes. No existing public import was removed or privatized.
There is no additional original node or module whose mathematical work is now unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original node's trait step names no dependency for the tame normal forms or the
split-section trait test. Its higher-dimensional step lists the normal-depth and flat-depth
lemmas but not the depth-two extension theorem, the smooth section-ideal completion,
or power-series full faithfulness. Reading the four imported declarations confirms that
they do not supply those conclusions. The two new nodes isolate those missing geometric
calculations with the source arguments in full in their docstrings and node proofs.
No existing mathematical statement was found false, and no target was changed.

Checked the source at Stacks Tags 0EYJ, 0EYI and 0EY9. The two-case route is the unit's
trait and depth-two route; no unit statement or proof step is bypassed. Blueprint searches
for 0EYI and 0EY9 found no existing blueprint node with these specialized conclusions.
LeanSearch was unavailable (HTTP internal server error), recorded as unavailable;
LeanFinder, Loogle and source grep were run and found no exact normalization-section result.

Edge cases checked mathematically: dimension zero cannot satisfy hs and hηU for an integral
base (the corresponding local domain is a field and s is generic). The dimension-less-than-two
case is consequently the DVR case. Dimension two belongs to the depth-two case.
For relative dimension zero the completion has no variables and the splitting comparison
is immediate; this avoids applying 0EY9's positive-variable hypothesis there.
Empty fibres make the source conclusions vacuous and the closed-image proof still works;
no source point is selected. Disconnected torsors are covered componentwise by stabilizers.

## New nodes

`lem-sbc-stalk-normalization-trait-section-source`:
`dag/nodes/sec-smooth-base-change/lem-sbc-stalk-normalization-trait-section-source.json`,
with module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource`.
This is the trait part of the calculation, restricted to individual source points.
The proof follows the tame normal forms and the split-section test of 0EYI(2).

`lem-sbc-stalk-normalization-depth-two-section-source`:
`dag/nodes/sec-smooth-base-change/lem-sbc-stalk-normalization-depth-two-section-source.json`,
with module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource`.
This is the higher-dimensional part of the calculation, restricted to individual source points.
The proof follows depth-two uniqueness, smooth section completion, and power-series
full faithfulness, with flat descent. Both nodes have source citations, complete proof text,
real recorded Mathlib searches, Lean signatures, and the inherited chapter and unit.
No change record is needed: every existing public interface is identical.


## Second reading by N1

1. **Existing interface unchanged — PASS.** Read the complete module diff against
   the repository. The original theorem signature is byte-for-byte identical, including
   universes, visibility, instances, the finiteness implication and the concrete
   normalization. Its existing docstring and all public imports are unchanged. The only
   existing-node changes are `proof`, `proof_deps` and `proof_origin`; no change record
   is required. The two new signatures match their nodes verbatim.
2. **Kernel proof and holes — PASS as decomposition.** Compiled all three delivered
   modules through lcompile.py in import order, without errors or warnings. A scratch
   copy with `#print axioms` checks the private helper, original theorem and both split
   theorems. The helper uses only `propext`, `Classical.choice` and `Quot.sound`; the
   three geometric theorems additionally depend on `sorryAx`, exactly as expected from
   the two named split holes. There is no new definition or forbidden declaration.
   The helper constructs the etale-source union and complementary closed-image open
   explicitly. Its choices are confined to a theorem proof; no object is defined by
   an arbitrary unproved existence statement.
3. **Split statements and source arguments — PASS.** Read both full docstrings and
   nodes against Stacks Tags [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ),
   [0EYI](https://stacks.math.columbia.edu/tag/0EYI),
   [0EY6](https://stacks.math.columbia.edu/tag/0EY6) and
   [0EY9](https://stacks.math.columbia.edu/tag/0EY9). The trait case proves source-local
   etaleness using the split-section tame test; the other case uses the depth-two
   extension and completion calculation. Neither merely renames the original target:
   each covers one dimension case and leaves target-open extraction to a proved helper.
   Checked zero-dimensional exclusion, the dimension-two boundary, relative dimension
   zero, disconnected torsors and empty fibres. These are true case-specific parts of
   the argument, with the original geometric input retained. Independent LeanFinder
   search for a finite-morphism fibre-neighbourhood criterion returned algebraic
   etale-locus facts and cancellation, not these geometric cases. Loogle with
   `AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite` returned the Zariski-main
   etale complement theorem, whose quasi-finite conclusion does not supply source
   etaleness here. A first unqualified `IsFinite` query was invalid and is not counted
   as evidence. A new grep for tame ramification, punctured etale covers and completion,
   and direct source searches in both Lean roots, found no duplicate case statements
   or shortcut. Neither split hole can be closed in a few minutes from these results.
4. **Shortest route, imports and unit — PASS after import repair.** The generic
   closed-image helper uses finiteness, open restriction, etale cancellation and
   Zariski source locality directly. Read all four old proof-dependency declarations;
   none supplies the missing tame or power-series calculation. Removed direct imports
   are fully listed under No longer needed, and no module is claimed globally pruned.
   Added the planned proof dependencies to the split modules as ordinary imports:
   generic full faithfulness and action extension in both, and the two depth lemmas
   only in the higher-dimensional module. This preserves the imports of those still
   needed nodes. Read `dag/units/sk-prop-input-spreading.json`: its trait and depth-two
   route is retained. Its `realized` fields are already empty in the repository; this
   delivery does not alter them or bypass any recorded realization.
5. **DAG agreement — PASS.** The existing node records exactly the dimension split
   and proved closed-image extraction. New nodes have complete source-backed proof
   text, dependency unions, origins, actual searches, provenance, inherited chapter
   and unit, and matching Lean records. Their added proof imports now agree with
   their dependency plans. Existing statement and statement-dependency fields stay
   unchanged.

Second reading changed only the six ordinary proof-import lines in the two new modules
and this report. No proof body, theorem statement or definition needed repair. One
original hole is closed by decomposition and two named holes are added; this is not
claimed as a net reduction in holes or as an unconditional geometric proof.
