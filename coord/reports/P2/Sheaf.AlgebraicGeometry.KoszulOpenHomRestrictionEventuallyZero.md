## What changed

Replaced the hole in `AlgebraicGeometry.koszulOpenHom_restriction_eventually_zero`
with a complete Lean proof. Its signature and original docstring are unchanged.
The proof constructs a termwise quasi-coherent representative using the core affine
qcoh derived equivalence, uses the stagewise Hom comparison, applies injectivity of
zeroth homology of the existing Koszul–Cech derived isomorphism, and transports
later-stage vanishing back through the additive stage equivalences.

Added `Sheaf.Algebra.Homology.FilteredModuleComplexHomologyZero`, with a fully proved
`CategoryTheory.filteredModuleComplex_homology_eventually_zero`. Its private helper
adapts the short-complex preservation argument already used by
`Sheaf.CategoryTheory.DirectedColimitHomology` from abelian groups to modules;
the existing public theorem has a different coefficient category and integer-pair
complex shape. The new proof uses Mathlib's ModuleCat AB5, naturality of homology,
and its concrete filtered-colimit equality criterion. No new hole is needed for
exactness of filtered colimits or for the final element argument.

Added `Sheaf.AlgebraicGeometry.KoszulOpenHomHomologyComparison` for the remaining
stagewise additive identification and restriction compatibility. This is a strict
part of the argument: it asserts no filtered-colimit exactness, invertibility of
the comparison, or eventual vanishing. The original theorem still explicitly
uses the existing affine derived comparison and the fully proved filtered-homology
criterion. No data definitions or existing interfaces were changed.

All three modules compile locally without warnings. Sources were checked against
Stacks Tags 08DC, 08DD and 00DB in the online edition. The new statements include
the empty sequence, zero ring, zero target, and zero class. Nilpotent or invertible
generators require no separate assumption. The module-class typeclass inference
for termwise tilde did not synthesize in this context; the proof instead supplies
its actual `presentationTilde` quasi-coherence proof.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.koszulOpenHom_restriction_eventually_zero`
(node `lem-sc-koszul-open-hom-restriction-eventually-zero`).

Proved, without any hole:
`CategoryTheory.filteredModuleComplex_homology_eventually_zero`
(node `lem-sc-filtered-module-complex-homology-zero`). Its private
`CategoryTheory.shortComplexHomologyPreserves` helper is also fully proved.

Added exactly one hole:
`AlgebraicGeometry.koszulOpenHom_homology_comparison`
(node `lem-sc-koszul-open-hom-homology-comparison`). This is a decomposition,
not an assertion of a net decrease in holes: one upper hole closed, one lower
hole added. The item's module contains no remaining `sorry`.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`,
replacing it with `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore`.
The stronger wrapper's shift-normalization conclusion is unused. Nodes
`lem-pc-affine-qcoh-derived-equivalence` and
`new-affine-qcoh-derived-equivalence-shift`, and modules
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` and
`Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalenceShift`, are not needed on this
item's route; the core equivalence and its own dependencies remain needed.
This is pruning of this route, not a claim that other targets cease using them.

Removed direct proof imports
`Sheaf.AlgebraicGeometry.DerivedStructureSheafHomHypercohomology` and
`Mathlib.Algebra.Homology.HomotopyCategory.KProjective` from the item's module.
Their results remain inputs of the new stagewise comparison theorem and are
imported there; they are moved dependencies, not pruned theory. Explicitly, the old
direct proof dependencies `lem-sc-bounded-above-projective-kprojective` and
`lem-pc-derived-structure-sheaf-hom-hypercohomology` leave the original node's
`proof_deps` and remain in the new comparison node's `proof_deps`.
The affine Koszul–Cech derived comparison and canonical construction remain
needed. No other original proof dependency is discarded. The unit's realization
record is unchanged; it places no realized statement or step on the removed
shift-normalization route.

## Where the brief, the DAG or earlier work was wrong

The old plan accurately identifies the mathematical argument. Its imported
lemmas did not state the bridge from stagewise derived Hom to Hom-complex
cohomology, with power-transition naturality and the explicit restriction
formula. The new stagewise comparison node makes that missing bridge precise.
The original DAG also treated filtered-colimit exactness and the element
criterion as elementary; they are now supplied by a fully proved generic Lean
lemma, with no unsupported invocation.

The repository's source-literature and unit-text paths are absent on this
machine; the unit record was read, and the relevant Stacks pages were read
online. LeanSearch returned Internal Server Error for both new topics.
LeanFinder, Loogle, Mathlib/project grep, and blueprint searches were used;
the absence of LeanSearch results was recorded as unavailable.

## New nodes

`lem-sc-koszul-open-hom-homology-comparison`:
`lean/Sheaf/AlgebraicGeometry/KoszulOpenHomHomologyComparison.lean`.
One public theorem, one hole, sourced to the stagewise Hom argument and
restriction formula of Stacks 08DD/08DC. Its docstring and node give the full
construction and compatibility proof in words. It does not duplicate the
original eventual-vanishing statement.

`lem-sc-filtered-module-complex-homology-zero`:
`lean/Sheaf/Algebra/Homology/FilteredModuleComplexHomologyZero.lean`.
One fully proved public theorem for arbitrary natural-number diagrams of
module cochain complexes, sourced to Stacks 00DB. No Koszul, restriction,
or quasi-coherence hypothesis enters this lemma.

The original node's proof, proof dependencies, and proof origin now follow
the implemented proof. No change record is required: every existing signature,
visibility, public import, and definition is unchanged.


## Second reading by P2

1. **Existing interfaces — pass.** Diffed the original module against the repository.
   The complete signature of `koszulOpenHom_restriction_eventually_zero`, its
   visibility, universe parameters, original docstring and sole public import are
   byte for byte unchanged. Only its proof and private proof imports changed.
   Both other modules are new; no existing definition, target or adapted module
   is delivered. No change record is needed.

2. **Kernel proof and holes — pass as a decomposition.** Independently compiled
   all three modules in import order through `lcompile.py`, without warnings.
   There is exactly one syntactic hole, the public named theorem
   `koszulOpenHom_homology_comparison`; its source, proof docstring and node are
   present. There are no new data definitions or forbidden trust mechanisms.
   Scratch `#print axioms` checks give only `propext`, `Classical.choice` and
   `Quot.sound` for `filteredModuleComplex_homology_eventually_zero`; the original
   theorem and the open comparison additionally use `sorryAx`. In particular,
   the upper theorem is not yet axiom-free: one original hole is closed and one
   strictly smaller hole added, with zero net decrease in holes. The affine
   equivalence and representative are unpacked inside a proposition's proof;
   no arbitrary existence witness is used to define public data.

3. **New statements and sources — pass.** Read Stacks
   [08DD](https://stacks.math.columbia.edu/tag/08DD),
   [08DC](https://stacks.math.columbia.edu/tag/08DC),
   [08D2](https://stacks.math.columbia.edu/tag/08D2),
   [06Z0](https://stacks.math.columbia.edu/tag/06Z0) and
   [00DB](https://stacks.math.columbia.edu/tag/00DB), and the actual
   `KoszulOpenSystem` and `KoszulCechComparisonConstruction` definitions.
   The comparison hole specifies the global-sections complex of the given
   termwise quasi-coherent F, an explicit Q(F)-to-E isomorphism, additive stage
   equivalences, the correct contravariant power transition, and annihilation
   after applying the specified homology comparison. It does not assert that
   comparison is invertible or that a stage eventually vanishes. Thus it supplies
   a genuine part of 08DD's argument, rather than renaming the original item.
   The finite free tail permits K-projectivity even for an unbounded target.
   The final compatibility is the denominator/sign formula in the construction,
   followed by restriction and evaluation at one; no regular sequence assumption
   is needed. For r=0 all positive exterior powers vanish, so both stage groups
   vanish. For a zero ring or zero target the same is true. A zero arrow maps to
   zero by additivity. If all generators are nilpotent, the open is empty and
   later transitions kill the classes; a unit generator requires no alteration.
   The generic filtered-homology theorem uses only exactness and the concrete
   equality criterion, with no geometric or boundedness hypotheses.
   Independent LeanFinder search for homotopy/Hom-complex naturality found
   `HomComplex.CohomologyClass.homAddEquiv`, but it does not supply the affine
   stage identification or restriction compatibility. Loogle search for
   homology and `PreservesColimitsOfShape` found no exact theorem; launcher grep,
   local Mathlib/project searches and upstream Koszul/colimit searches likewise
   found no replacement. The existing `directed_colimit_homology` has abelian
   group coefficients and a different complex shape, so its private preservation
   argument is legitimately adapted here without duplicating its public statement.

4. **Route and pruning — pass with report repair.** Checked the proof top down:
   the core affine equivalence supplies F and eF; `presentationTilde` proves hF;
   the new comparison supplies alpha and the zero equation; the existing affine
   comparison gives `IsIso` and hence injectivity of beta; the fully proved
   filtered-homology lemma supplies b; alpha naturality and injectivity return
   zero precomposition. The last step uses `map_zero` for the additive equivalence.
   No simpler available theorem handles the missing explicit compatibility in
   a few minutes. All public imports of the new generic module support the
   statement's complexes, module homology or chosen colimit; the AB5, concrete
   equality and functor-category imports are private proof imports. The new
   comparison's private imports match its stated proof dependencies.
   `dag/units/sk-thm-picard-duality.json` is unchanged, with no realized statement
   or step assigned to the discarded shift-normalization route. The removed
   affine wrapper is replaced by its core, while the K-projective and
   structure-sheaf Hom dependencies move to the new comparison. Updated
   `## No longer needed` to enumerate these old node IDs explicitly and name the
   shift node exactly; this prevents treating moved dependencies as pruned theory.

5. **DAG and Lean agreement — pass.** Opened all three delivered nodes and the
   original node. Their recorded Lean signatures match the files verbatim;
   `proof_deps` are exactly the unions of the proof steps' `uses`. The original
   node records precisely the three reductions above. Both new nodes have the
   required source, creation, chapter/unit, search, blueprint and Lean records.
   The filtered-homology node's Mathlib assembly is fully formalized and has no
   residual hole; the comparison node records its actual open stagewise argument.
   The affine comparison remains a dependency rather than being hidden in the
   new hole. No original node statement or statement dependency was changed.

Changes by this reader: repaired the pruning report's explicit node accounting
and added the missing blueprint IDs to the two new module docstrings. The Lean
proofs and all theorem signatures were correct and were left as supplied.
