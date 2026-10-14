## What changed

Reviewed `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore`. Its existing
canonical quotient-lift definition and complete theorem proof are retained.
The second reader removed three redundant direct public imports, already publicly
available through `SectionRingVeroneseFractionKernel`, and restored the repository's
missing docstring sentence. No declaration signature, definition body, or proof changed.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` is fully proved,
including both canonical-map bijectivity and the displayed generator formula.
It was already proved on the repository baseline: holes closed by this delivery: none;
holes added: none; holes left in the item: none. This is a review/pruning of an already
repaired item, not new proof progress or a decomposition. There are no split-off statements.
Both the canonical-map definition and theorem have exactly `propext`, `Classical.choice`,
and `Quot.sound` as axioms, checked in a scratch copy through `lcompile.py`.

## No longer needed

Removed redundant direct imports:
- `Sheaf.AlgebraicGeometry.InvertibleSectionRing`
- `Sheaf.AlgebraicGeometry.SectionFractionPresentation`
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`

`SectionRingVeroneseFractionKernel` publicly imports `SectionRingVeroneseFractionMap`
and `SectionFractionPresentation`; the map module publicly imports `InvertibleSectionRing`
and `HomogeneousLocalization`. Their declarations remain publicly available. No DAG proof
dependency is obsolete: both `lem-sc-section-ring-veronese-fraction-kernel` and
`def-sc-section-ring-veronese-fraction-map` are actually used. No module becomes unreachable.

## Where the brief, the DAG or earlier work was wrong

The item is still listed as an upstream-review repair, but its current repository
statement already gives bijectivity of the explicitly constructed canonical map and
its generator formula, with a complete proof. No new hole is closed. The first worker's
claim that all four direct imports were needed was inaccurate: three are redundant.
The sandbox also omitted a sentence present in the current repository docstring.

## Second reading by H2

1. Compared the delivered module with the repository using `diff`. Both existing
   declaration signatures, all hypotheses, both theorem conclusions, visibility,
   definition data, and proof bodies are unchanged byte for byte. The initial difference
   was one missing docstring sentence; restored it. The only final source differences
   are removal of the three redundant imports above. The public-import removal is recorded in
   `coord/changes/SectionRingVeroneseFractionsCore_imports.md`; all transitive
   public declarations remain available. Verdict: pass.

2. Compiled the original sandbox module and then a scratch copy of the final module
   with `#print axioms` for `sectionRingVeroneseFractionCanonicalMap` and
   `sectionRing_veronese_fraction_core`. Both compile cleanly; both axiom lists contain
   only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`. The module has no
   `sorry`, axiom, unsafe, opaque, implemented_by, or extern declaration. The map data
   are `QuotientAddGroup.lift` of the explicitly constructed numerator map; the named
   kernel theorem supplies its well-definedness proof, with no arbitrary witness choice.
   Verdict: pass.

3. No new statement, split-off hole, or node exists. Read the existing numerator-map
   module: surjectivity uses `Away.mk_surjective` and numerator-isomorphism cancellation,
   with no assumption that d is positive or s is nonzero. For d=0 and n=0 the tensor
   identities still apply; for zero or nilpotent s the localization and relation quotient
   collapse together via the kernel equality. No edge case is excluded. No new-node
   duplication search is applicable. Verdict: pass.

4. Read the proof top downward and the actual Mathlib quotient-lift lemmas in
   `Mathlib/GroupTheory/QuotientGroup/Defs.lean`. Injectivity follows directly from
   `injective_lift_iff` and the existing relation/kernel equality; surjectivity follows
   from `lift_surjective_of_surjective` and the existing numerator surjectivity.
   The generator calculation reduces the quotient lift to `DirectSum.of`, evaluates
   `DirectSum.toAddMonoid_of`, and applies `sectionRingVeroneseNumerator_cancel`.
   This already uses the generic Mathlib route; no replacement lemma or inverse
   construction is needed. Removed redundant imports and compiled the reduced module.
   Read `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, with no realized steps; this auxiliary argument changes
   neither that unit route nor its realization. Verdict: pass after import pruning.

5. Read `lem-sc-section-ring-veronese-fractions-core.json` and both dependency nodes.
   Its two proof steps match respectively the quotient-lift bijectivity argument and
   generator calculation. Its `proof_deps` lists the kernel node and numerator-map
   node, both genuinely used; the map node records the cancellation and surjectivity
   declarations as well as its construction. `proof_origin` describes the same direct
   route. No node changes or new-node fields are necessary. Verdict: pass.

Changes by the second reader: restored the repository docstring sentence, removed
three redundant direct imports, and corrected the report to record zero new holes closed.

The dry run required a change record for public-import removal; added
`coord/changes/SectionRingVeroneseFractionsCore_imports.md`, listing every downstream
module and the unchanged transitive public availability. No new nodes.
