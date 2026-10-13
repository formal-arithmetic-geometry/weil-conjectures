## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap` by a concrete family
of coefficient morphisms and a complete proof assembling their generator and face equations.
All existing signatures, definitions, visibility and docstrings are unchanged.
The new construction maps a section by restriction identification, the pullback unit for
`g'`, and restriction to the direct-image support. The coefficient sheaf map is its mate
under the composed tilde/Gamma and two pullback/pushforward adjunctions.
No arbitrary witness is chosen. The theorem supplying linearity determines only a proof
field of this explicitly constructed additive map.

Added proof imports of `CoefficientComparisonMorphismGenerator` and
`CoefficientComparisonMorphismFaces`. Their statements concern this explicit construction,
not an existential family under another name. The generator calculation is proved by
`Equiv.apply_symm_apply`, the formula for the composed unit, naturality of section morphisms,
and composition of restriction maps. Two strictly separate calculations remain.
The sandbox compiles through `lcompile.py --all`; every file stays below its 60-second limit.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.Modules.exists_coefficientComparison_maps`
(node `lem-pc-finite-affine-cech-coefficient-comparison-map`).

Also proved completely:
`AlgebraicGeometry.Scheme.Modules.coefficientComparisonMorphism_generator`
(node `lem-pc-coefficient-comparison-morphism-generator`).
Its only postponed dependency is the linearity proof used in the concrete map.

Added exactly two holes, each in its own new module:

- `AlgebraicGeometry.Scheme.Modules.coefficientSectionAddMap_linear`
  (`lem-pc-coefficient-section-map-linear`, `CoefficientComparisonConstruction`).
  This is only structural scalar compatibility of the specified additive section map.
- `AlgebraicGeometry.Scheme.Modules.coefficientComparisonMorphism_faces`
  (`lem-pc-coefficient-comparison-morphism-faces`, `CoefficientComparisonMorphismFaces`).
  This is only face naturality of specified mates; it asserts neither existence nor
  a generator formula nor invertibility.

This is a decomposition: one original hole closed, two lower holes added (net minus one),
not a claim that the comparison is now axiom-free. There is no sorry in any definition,
private helper, or partial proof. Empty opens give zero sections, the zero module is
preserved, and `r = 0` gives empty tuple families. Identity squares recover the usual
counit calculation. Arbitrary commutative squares are allowed: no cartesian, affine or
quasi-coherent hypothesis is used to claim invertibility.

## No longer needed

No existing import was removed: the item originally had only its statement import
`Sheaf.AlgebraicGeometry.FiniteAffineCechModel`, which is still needed.
The direct composed-adjunction route no longer uses the following planned dependencies:

- `lem-weil-pbc-module-base-change-map-open-restriction`, module
  `Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`.
- `lem-weil-pbc-open-immersion-module-pullback-restriction`, whose Mathlib interface is
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`.

The latter Mathlib module itself remains needed for modules and adjunctions.
The old direct dependencies `lem-weil-pbc-affine-tilde-gamma-adjunction` and
`def-weil-sheaf-of-modules-category` have moved to the new construction and calculation
nodes: they remain transitive dependencies, so their modules are not pruned.
`def-pc-finite-affine-cech-model` remains a direct dependency. This reports pruning from this proof route,
not global unreachability from all targets. The coherence unit's Cech route is retained;
its own statement and proof steps have not been bypassed.

## Where the brief, the DAG or earlier work was wrong

The supplied file did not import its planned proof dependencies. The recorded
`moduleBaseChangeMap_open_restriction` interface is stated for `tensorPullback`, whereas
this item uses Mathlib's `Modules.pullback`; it also concerns open restriction of a
base-change map, not normalization of the coefficient section map used here.
The direct mate construction avoids the extra interface conversion and base-change
restriction theorem.

Read Stacks Tags 02KE, 01I6, 01I9, 01IA, 0096 and 0097. Tag 01I6, Lemma 26.7.1 gives
the mapping property of tilde for arbitrary module sheaves; 01IA concerns the
quasi-coherent counit isomorphism, which this construction does not need. Tag 0096 is
the module pullback adjunction and 0097 its composition, rather than a standalone
open-restriction theorem. The new docstrings cite the relevant places precisely.
The added scalar and face proof sketches supply the omitted adjunction calculations.
No statement was disputed or changed.

Searches: Loogle for `fromTildeΓ`, LeanFinder for associated-module maps induced by global
sections, LeanSearch for unit linearity/naturality (unavailable: internal server error),
and Mathlib grep for adjunction naturality and structural-ring-map identities. Actual
queries and outcomes are in the sandbox search log and new nodes. Blueprint and DAG
searches found no duplicate of these calculations.

## New nodes

`lem-pc-coefficient-section-map-linear`: explicit additive section construction, its
structural scalar compatibility, and the resulting concrete linear map and mate.
Module `Sheaf.AlgebraicGeometry.CoefficientComparisonConstruction`.

`lem-pc-coefficient-comparison-morphism-generator`: the global generator identity for
that specified mate, proved in Lean. Module
`Sheaf.AlgebraicGeometry.CoefficientComparisonMorphismGenerator`.

`lem-pc-coefficient-comparison-morphism-faces`: the separate face equation for those
specified mates, with the tuple support equalities as input. Module
`Sheaf.AlgebraicGeometry.CoefficientComparisonMorphismFaces`.

No change record is needed: no existing definition, statement or public import changed.

## Second reading by N4

1. Compared the entire existing module with the repository by `diff -u`. PASS:
   the only changes are two plain proof imports and the body of
   `exists_coefficientComparison_maps`. All existing signatures, definitions,
   docstrings and visibility are unchanged. Restored the original single space
   before this theorem's `:=`. No interface change record is required.
2. Compiled all four modules in import order with `lcompile.py --all`. PASS:
   6.9, 6.2, 39.5 and 10.0 seconds, without errors or warnings. A separate scratch
   module prints axioms of the additive map, linearity theorem, linear map, mate,
   generator theorem, face theorem and original existence theorem. The additive
   construction uses only propext, Classical.choice and Quot.sound; the others
   additionally use sorryAx, as expected from the two reported open calculations.
   The only literal sorries are the complete proofs of the two public named
   theorems, each with its matching node and source/proof docstring. The linearity
   theorem supplies a proof field, never an arbitrary data witness. No prohibited
   declaration or hollow definition occurs.
3. Read both split-off statements, their docstrings, and all three new nodes.
   PASS as a decomposition: scalar compatibility is one structural equation;
   face naturality is another equation for specified mates, with neither an
   existence conclusion nor a generator-normalization conclusion. Neither is
   a restatement of the original existential family. Checked empty supports,
   zero coefficients, identity squares, r = 0 (no tuples), and r = 1 (no faces).
   Restriction, linearity and mate naturality work without an affine or cartesian
   hypothesis; no unjustified invertibility is claimed. Independently searched
   via msearch grep `restrictAppIso.*smul|unit.*naturality|homEquiv_naturality`
   and LeanFinder for scalar compatibility of restriction and pullback units,
   and searched local Lean/DAG files for coefficient maps and restriction mates.
   Read Mathlib's smul_restrictAppIso_hom, map_restrictAppIso_hom and the
   moduleSpecGamma/adjunction interfaces. These supply ingredients rather than
   an exact duplicate. The remaining coercion and scalar-transport calculation
   is not a quick application of any found theorem; no further hole was closed.
   Checked the cited primary sources: [0096](https://stacks.math.columbia.edu/tag/0096)
   supplies module adjunction, [0097](https://stacks.math.columbia.edu/tag/0097)
   composition, and [01I6](https://stacks.math.columbia.edu/tag/01I6), Lemma 26.7.1,
   the mapping property for arbitrary target module sheaves. The explicit
   restriction/mate calculations in the proof sketches follow these identities.
4. Read the proof from the existential statement down through the mate and
   generator calculation. PASS: the construction is concrete, generator
   normalization is proved by the composed hom equivalence, and only face
   naturality and scalar compatibility remain. Every import is used in a
   signature or proof; the new public imports expose definitions used by the
   new statements. The original public import is unchanged. Expanded
   `No longer needed` to identify the two old direct dependencies retained
   transitively as well as the two genuinely unused planned dependencies.
   Read dag/units/sk-thm-picard-coherence.json: its realized statement/step
   lists are empty in the repository; this item is below that unit, and the
   finite Cech route in its recorded proof is preserved. No unit is bypassed.
5. Compared node proof steps and proof_deps with the Lean construction,
   generator application and face application. PASS: the dependency unions
   match the recorded steps, new nodes have the required source, searches,
   blueprint ancestry, creation and Lean records, and the original node's
   statement and stmt_deps are unchanged. The generator node is proved with
   the postponed linearity dependency explicitly recorded. Hole accounting
   remains one original hole closed, two lower holes added (net minus one).

Second reading changed only the theorem's pre-proof whitespace and this report:
clarified dependency pruning and recorded the independent checks. No proof or
statement repair was necessary. This delivery remains a decomposition, not an
axiom-free proof of the comparison construction.
