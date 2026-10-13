## What changed

Replaced the earlier attempt's restatement with two separate parts of the original plan.
`RestrictedDerivedEvaluationPullback` constructs `Hzero`, `transportZero`, and `pullbackHom`
and states `restrictedDerivedEvaluation_pullback`, an equality of homomorphisms for an
arbitrary source sheaf and derived morphism, before choosing any represented generator.
`RestrictedComparisonGeneratorPullback` states `restrictedComparison_generator_pullback`,
which has no degree, target coefficient sheaf, or raw class. The item's proof specializes
the square, evaluates it at the represented generator, and substitutes its transport identity.
All original signatures and visibility are unchanged. The added import is proof-only.
A declaration-scoped recursion limit of 2048 handles definitional comparisons of the
inverse-image composition isomorphism; this is not a file-level option.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.rawRestrictedCohomologyComparison_naturality` by decomposition.
There are no sorries in the item's module. Two holes were added:

- `AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedDerivedEvaluation_pullback`
  (node `lem-sbc-restricted-derived-evaluation-pullback`).
- `AlgebraicGeometry.Etale.RawRestrictedComparison.restrictedComparison_generator_pullback`
  (node `lem-sbc-restricted-comparison-generator-pullback`).

This is one upper hole closed, two strictly separate lower statements added, not an
unconditional proof or a net reduction in holes. All new data are explicit compositions;
no data are chosen from an existence theorem. The source and target types compile also
without nonemptiness, affineness, or qcqs assumptions. The two remaining claims retain
identity-map and empty-scheme cases, and the derived square allows p = 0.

Validation: the second reader independently compiled all three modules through
lcompile.py. Axiom checks and delivery preflight are recorded below.

## No longer needed

No original imports or modules were pruned. The parent node's direct proof uses the two
new statements instead of performing inverse-image, sheafification, and derived-adjunction
calculations itself. These ingredients remain needed in the two lower statements. The old direct
proof dependencies absent from the new parent proof_deps are:

- `def-sbc-raw-affine-restricted-cohomology`;
- `def-weil-pbc-inverse-image`;
- `def-weil-pbc-sheafification`;
- `lem-weil-pbc-inverse-image-composition`;
- `prop-weil-pbc-derived-inverse-image-adjunction`.

These are moved below the new lemmas, not pruned from the import closure.
Removed from the saved attempt the redundant unchanged copy of
`RawRestrictedCohomologyComparisonMap` and the uncommitted restatement node
`lem-sbc-raw-restricted-cohomology-comparison-derived-evaluation`.

## Where the brief, the DAG or earlier work was wrong

The saved intermediate theorem merely expanded `rawAffineRestrictedCohomologyMap` and
was definitionally the original conclusion. It was not a reduction. Its report also
claimed an unused projection lemma remained, although no such lemma was present,
and wrote the second-reader section before independent reading. All three issues
are removed. The existing map-module copy was identical to the repository and is
not part of this delivery.

The cited Stacks Tag 0EZM is the continuity theorem for complexes under limits,
not a theorem about derived pullback units. New docstrings instead cite 07A6 for
adjunction and 0D6F for restricted derived sections; 03Q8 is the parent presentation.
The expanded compatibility calculation is recorded as an agent proof, not claimed
to be explicitly written in 03Q8. Mathlib searches found only generic ingredients;
LeanSearch returned Internal Server Error and is recorded as unavailable.
The original two-step route is preserved; no realized unit statement or step is bypassed.

## New nodes

`lem-sbc-restricted-derived-evaluation-pullback`, in the new module
`Sheaf.AlgebraicGeometry.RestrictedDerivedEvaluationPullback`: the square of
homomorphisms for arbitrary single-complex source and target, including explicit
underived source transport and the five derived pullback factors. It isolates
the parent's second step and contains no chosen represented generator.

`lem-sbc-restricted-comparison-generator-pullback`, in the new module
`Sheaf.AlgebraicGeometry.RestrictedComparisonGeneratorPullback`: the parent's
first step, transporting the particular represented identity section under the
explicit source transport. It involves no higher derived-Hom class.
No existing definition or statement was changed, so no change record is needed.

## Second reading by C1

1. **Interfaces: PASS.** Read the repository and sandbox modules with `diff -u`.
   Compared the existing theorem signature byte for byte: identical, including
   all schemes, the triangle equation, degree, coefficient morphism, etale object,
   raw class, and the two explicitly constructed maps. No existing definition or
   visibility changed. The one added parent import is plain `import`, used only
   by the proof. There are no adapted existing modules or change records.
2. **Proof and axioms: PASS as a decomposition.** Independently compiled the three
   modules in import order through `lcompile.py`: no errors or warnings in the
   delivered modules. The parent's proof specializes the square to the pulled-back
   free sheaf, applies `congrArg` at the inverse-zero image of the generator, uses
   the generator identity, and identifies the five factors with the original raw
   pullback. The two named theorems listed above are the only new sorries. No
   forbidden axiom mechanism or sorry in data is present. Scratch `#print axioms`
   checks of all six declarations found only `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx` for the parent and the two open theorems. In
   particular, the three new constructed maps use no `sorryAx`. Scratch copies
   were removed. One original hole is closed by two lower holes: this is not a
   net improvement in the sorry count.
3. **Split statements: PASS.** Read both statements, their definitions and their
   full docstring arguments. The square asserts naturality before choosing a
   represented source or element; the generator lemma only asserts transport of
   an ordinary section and has no coefficient class or degree. Thus neither
   repeats the parent conclusion. For the square, degree zero reduces to
   naturality of section pullback; for zero `t` or zero coefficient morphism both
   sides vanish. For identity maps, the inverse-image identity/composition and
   single comparisons cancel. On empty restricted schemes the section and
   cohomology groups vanish. An arbitrary source identification `e` is handled
   by the adjacent `e.hom` and `e.inv`, not an unsupported isomorphism of section
   pullback. No affineness, qcqs, or nonempty hypothesis is needed. Repeated
   Loogle, LeanFinder and Mathlib grep with different queries and read related
   library declarations: `globalSectionsUpperStarMap_comp`,
   `upperStarComp_hom_app_unit_app`, `rightDerivedZeroIsoSelf`, and
   `rightDerivedPlusSingleUnitHomology_comp_comparison` are ingredients, not
   duplicates. The terminal-object/localization and derived comparison
   calculations remain substantial, so neither hole closes in a few minutes.
   Checked [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [0D6F](https://stacks.math.columbia.edu/tag/0D6F), and
   [07A6](https://stacks.math.columbia.edu/tag/07A6): these provide the presentation,
   localization, and adjunction ingredients; the explicit coherence arguments
   are correctly identified as agent expansions.
4. **Route and pruning: PASS after report repair.** The two new lemmas isolate
   the original node's two steps: generator transport and derived naturality.
   Read `dag/units/sk-lem-failure-field.json`; its `realized.statement` and sole
   `realized.steps` list are empty, and no recorded realization or unit route is
   replaced. All three delivered modules have one import each, each needed by
   their statements or proof; there is no removable import. Expanded
   `No longer needed` to list all five old direct dependencies missing from the
   parent's new proof_deps, and distinguished that relocation from pruning.
   No module is claimed pruned.
5. **Nodes: PASS after metadata repair.** Read the three node records; the parent
   changes only `proof`, `proof_deps`, and `proof_origin`. Its proof steps and
   dependency union match the two-lemma reduction. Both new nodes have matching
   hypotheses and conclusions, source, full argument, dependency union, agent
   origin, search records, creation data, blueprint ancestry, chapter and unit.
   Replaced their flattened `lean.statement` strings with the verbatim multiline
   signatures and added the independent search results.

Second-reading changes: completed dependency reporting, corrected the existing
module's misleading 0EZM source comments to 0D6F/07A6, made the two new node
signatures verbatim, recorded independent searches, and wrote this review.
The proof implementation and mathematical statements were retained.

Final validation: `deliver3.py C1
Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality --no-push`
printed `OK (dry run)` after compiling and passing preflight. The review class
is CODEX because the delivery adds two modules/nodes with named open theorems.
