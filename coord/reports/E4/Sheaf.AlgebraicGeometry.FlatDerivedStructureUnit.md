## What changed

The existing theorem `AlgebraicGeometry.exists_flat_derived_structure_unit` keeps its
signature byte for byte. Its proof constructs the morphism as the single ordinary
structure map followed by `Scheme.Modules.canonicalSingleDirectImageMap`. It constructs
the two degree-zero isomorphisms from `singleFunctorCompHomologyFunctorIso`,
`homologyRightDerivedFunctorObjSingleFunctorIso`, and `rightDerivedZeroIsoSelf`.
`Scheme.Modules.canonicalDirectImageH0Unit` and naturality of the single homology
isomorphism prove the comparison equation. No object or map is chosen from a new
unproved existence theorem, and no definition is added or changed.

The first worker's proposed `FlatDerivedStructureUnitData` module and
`flat-derived-structure-unit-data` node were removed: the existing canonical unit
normalization already supplies this part of the proof. The remaining new module
`Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties` states the two fibre
properties for the explicit canonical composite. It has a complete mathematical proof
in its docstring and one named `sorry`. Its former universal quantifier over an arbitrary
morphism was false and has been removed before publication.

The parent module imports `Picard.CanonicalDirectImageH0Unit` and the new fibre-properties
module with plain `import`. Its old proof-only imports of
`RelativelyFlatCanonicalModuleBaseChange` and `TensorPullbackStructureSheaf` move to the
fibre-properties module, where they are dependencies of the documented remaining proof.
All original public imports stay unchanged. The new module uses public imports only
for its statement and plain imports for its documented proof dependencies.

## Proved and sorry left

Closed original hole:

- `AlgebraicGeometry.exists_flat_derived_structure_unit`
  (node `lem-sc-flat-derived-structure-unit`): the map construction, the two explicit
  degree-zero comparisons, their compatibility equation, and the combination with the
  fibre-properties lemma are checked Lean proofs.

Added hole:

- `AlgebraicGeometry.flat_derived_structure_unit_properties`
  (node `flat-derived-structure-unit-properties`): negative derived-fibre vanishing
  and the conditional degree-zero fibre isomorphism for the explicit canonical map.

This is a decomposition: one original hole closed and one new hole added, net zero.
The parent still depends on `sorryAx` through the fibre lemma and is not claimed as a
completed axiom-free proof. No other delivered declaration contains `sorry`; no
`axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition is added.
The proposed data hole is not delivered and is not counted as a closed baseline hole.

## No longer needed

No library module is pruned. Every old proof dependency remains in the argument:
`def-pc-ringed-spaces-derived-direct-image` is used for the explicit derived image;
`lem-pc-relatively-flat-canonical-module-base-change` and
`lem-weil-pbc-module-pullback-structure-sheaf` are now dependencies of the fibre lemma,
rather than direct dependencies of the parent proof. The corresponding two plain
imports are removed from the parent and retained in that helper. There is no old
proof dependency silently dropped from the route.

The undelivered proposed `FlatDerivedStructureUnitData` module and its node are removed
from this sandbox; these were never baseline library modules and are not pruning credit.

## Where the brief, the DAG or earlier work was wrong

The first worker's `flat_derived_structure_unit_properties f a` quantified over every
morphism `a : O_S[0] → Rf_*O_X[0]`. Its isomorphism assertion is false: take f to be the
identity on Spec of a nonzero field and a = 0. The canonical map on fibre global
functions is an isomorphism, but the induced map on H0 is the zero map of a nonzero
one-dimensional vector space. A reference to a resolution unit in prose cannot constrain
an arbitrary Lean argument. The corrected statement displays the canonical composite
and has no arbitrary-map argument.

The proposed data node also missed the existing degree-zero canonical comparison.
Searches and inspection located `Picard.CanonicalDirectImageH0Unit`, which is reused.
The first worker's new nodes had vague non-self-contained statements, empty statement
dependencies, and a single proof step saying only to use a resolution/fibre argument.
The surviving node now states every hypothesis and the explicit map, records four
proof steps with existing dependencies, and records the actual second-reader searches.
The parent proof origin now names E4 and its actual route.

Read Stacks Project [0E62](https://stacks.math.columbia.edu/tag/0E62), first proof
paragraph, [0A1D](https://stacks.math.columbia.edu/tag/0A1D), and
[0096](https://stacks.math.columbia.edu/tag/0096). The helper uses the relative-flat
base-change statement to justify the quasi-compact separated flat hypotheses; it does
not silently apply the proper finite-presentation hypotheses of the full 0E62 lemma.

## New nodes

`flat-derived-structure-unit-properties` is the only new node, in
`dag/nodes/sec-abelian-varieties/flat-derived-structure-unit-properties.json`, with its
new module `lean/Sheaf/AlgebraicGeometry/FlatDerivedStructureUnitProperties.lean`.
It states just the fibre properties of an explicitly constructed morphism, not the
parent's existence or degree-zero comparison. It is strictly a part of the argument.
Its chapter and unit are unchanged from the parent. There are no change records because
no published statement, definition, or public import changes.

## Second reading by E4

1. Compared the existing module against the repository version with `diff` and an exact
   substring comparison of the theorem signature through `:=`. Verdict: the sole existing
   declaration's signature and docstring are unchanged byte for byte; only its proof and
   plain imports change. The other delivered module is new. No published interface or
   definition change needs a change record.
2. Compiled both delivered modules in import order using `lcompile.py --all`, then checked
   both declaration names with `#print axioms` in a scratch copy. Verdict: compilation
   passes, and axioms are limited to the three allowed standard axioms and `sorryAx`
   from the explicitly reported helper. The sole delivered `sorry` is the complete proof
   body of that named theorem. Read both proof bodies; the parent constructs its data
   from existing definitions, and its final equation uses the canonical H0 unit theorem
   followed by naturality, not an assumption about an arbitrary map.
3. Tested the new fibre statement on identity maps of field spectra, the empty source,
   and an empty base. Verdict: the original arbitrary-map statement fails for a = 0;
   the repaired explicit-map version agrees with the identity structure map, while an
   empty fibre has no negative cohomology and cannot satisfy the nonzero-field H0-map
   hypothesis. Read the base-change and tensor-unit interfaces and the canonical single
   comparison interfaces. The repaired helper follows relative-flat base change,
   nonnegative injective resolutions, and compatibility of the canonical mate. Repeated
   searches with leanfinder, loogle, and rg/msearch grep using degree-zero right-derived
   normalization and residue-field homology terminology. LeanSearch was unavailable
   (Internal Server Error), recorded as such. Found and reused the existing canonical
   H0 unit theorem; found no existing fibre-properties specialization. The helper's
   docstring now gives the full mathematical argument, including the actual map
   compatibility and the two opens of Spec of a field.
4. Read from the parent down through its construction, the existing canonical H0 unit
   theorem, and the remaining helper. Verdict: the shorter existing degree-zero route
   eliminates the redundant proposed data hole. Original public imports are preserved;
   direct proof-only base-change imports relocate to the helper. Every old proof
   dependency is accounted for above. Read `dag/units/sk-prop-av-cube.json`: its
   `realized.statement` and sole `realized.steps` entry are empty, and this auxiliary
   node is not a designated replacement for the cube theorem's unit step. The new
   proof retains the original resolution/base-change route and does not bypass a unit.
5. Compared both delivered node records against the final Lean. Verdict: the parent
   node retains its original statement and Lean signature; its proof, proof_deps, and
   proof_origin now match the construction and combination. The new node has a
   self-contained statement specifying the canonical map, exact verbatim Lean
   signature, matching chapter/unit, source, origin, creation and blueprint records,
   actual search records, and proof_deps equal to the union of its four steps' uses.
   Verified every referenced node ID exists. The obsolete data node is absent.

Changed on second reading: removed the false universal-map fibre statement, bound the
remaining fibre obligations to the explicitly constructed canonical map, proved the
degree-zero construction and compatibility from the existing canonical unit theorem,
removed the redundant data module/node, corrected the DAG and imports, expanded the
remaining hole's proof docstring, and replaced the inaccurate progress report with the
one-hole-for-one-hole decomposition count.
