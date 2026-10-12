## What changed

Reduced `AlgebraicGeometry.Etale.exists_raw_restricted_cohomology_natural_iso` to
invertibility and pullback compatibility of a canonical evaluation morphism. The family
is formed with `asIso`, so its hom is the constructed morphism without a choice of
arbitrary isomorphisms. The original signature and public imports are unchanged. The new construction retains
public imports for the shift and additivity instances used by its public definitions;
privatizing these imports fails instance synthesis in the construction module.

Added `RawRestrictedCohomologyComparisonMap`: a real construction using the represented
identity section, the sheafification and inverse-image units, restriction, derived global
sections, zeroth homology and the shift comparison. Every definition is filled. The
single-complex comparisons are first constructed for abstract abelian categories and
then instantiated; this avoids expensive kernel comparisons of concrete site structures.
Local instance aliases use existing instances and do not install global instances.

Added separate statement modules `RawRestrictedCohomologyComparisonIsIso` and
`RawRestrictedCohomologyComparisonNaturality`. Updated the original node's route and
added three nodes recording the construction and its two outstanding properties.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_raw_restricted_cohomology_natural_iso`
(node `lem-sbc-raw-restricted-cohomology-natural-iso`) by a decomposition, not a net
proof. The complete combining proof constructs the isomorphism family using the
invertibility theorem and applies the compatibility equation to its definitionally
unchanged hom.

Added exactly two holes:

- `AlgebraicGeometry.Etale.isIso_rawRestrictedCohomologyComparison`, node
  `lem-sbc-raw-restricted-cohomology-comparison-is-iso`.
- `AlgebraicGeometry.Etale.rawRestrictedCohomologyComparison_naturality`, node
  `lem-sbc-raw-restricted-cohomology-comparison-naturality`.

There are no holes in the original module or in the comparison construction. Each new
hole is the entire proof of one public theorem in its own module, with its source and
full proof plan in its docstring. The first property asserts invertibility only; the
second asserts compatibility of a fixed, independently constructed map and does not
assume invertibility. Neither asserts existence of the family required by the original
statement. Degree zero, zero coefficients and empty restricted schemes satisfy both
plans: they reduce to the ordinary sections adjunction or the zero sections complex.

## No longer needed

Removed these redundant direct proof imports from the original module:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

The public imports `RawAffineRestrictedCohomology` and
`AbelianHigherDirectImageNaturalComparison` still provide the statement's definitions.
The original node now directly uses only the two new property nodes. These eight
old direct proof dependencies are no longer used directly by the combining proof:

- `def-weil-pbc-sheafification`.
- `def-weil-pbc-inverse-image`.
- `lem-weil-pbc-inverse-image-composition`.
- `lem-weil-pbc-dplus-injective-representative`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `def-weil-pbc-etale-cohomology`.
- `prop-weil-pbc-derived-inverse-image-adjunction`.
- `def-sbc-raw-affine-restricted-cohomology`.

They remain needed below the new property nodes, so this delivery claims no global
pruning of those nodes or modules. No unit statement or realized proof step was bypassed: the
unit `sk-lem-failure-field` has empty realized lists for this part of its argument.

## Where the brief, the DAG or earlier work was wrong

The broad adjunction and K-injective lemmas listed in the parent plan do not already
supply the canonical evaluation map or its pullback compatibility. The new nodes make
those two pieces explicit. The existing étale restriction/injective theorem is stated
for module coefficients; its abelian-group counterpart still needs to be supplied
inside the invertibility proof, using the same exact extension-by-zero argument.

The compile-time issue was kernel checking of concrete derived single-complex
comparison formulas. Abstracting these formulas in the same module addresses it;
no file was split to evade the single-file limit.

## New nodes

`def-sbc-raw-restricted-cohomology-comparison-map` records the explicit evaluation
construction in `Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap`. Its
auxiliary constructions are fully defined or proved and choose no data from an
unproved existence assertion.

`lem-sbc-raw-restricted-cohomology-comparison-is-iso` records the remaining
injective-resolution computation in its own module. Its proof uses the sections
adjunction, exact étale restriction and the K-injective localization bijection.

`lem-sbc-raw-restricted-cohomology-comparison-naturality` records the remaining
calculation of the raw pullback factors after restricted derived sections. It uses
the projection identity, inverse-image coherence, derived adjunction units and the
single-complex/shift comparisons, independently of invertibility.

No change record is needed: no existing statement, definition or public visibility
was changed, and there are no forced adaptations.


## Second reading by D3

1. PASS. Compared the delivered existing module with the repository by `diff -u`:
   only proof imports and the proof body changed. The existing signature and docstring
   are byte for byte unchanged. The other three modules are new; there are no existing
   definitions changed and no forced adaptations or change records required.
2. PASS as a decomposition. Compiled all four modules with `lcompile.py --all` in
   import order without errors or warnings. The only two textual holes are the complete
   proofs of the reported public property theorems. No axiom, unsafe, opaque, extern,
   implemented_by, skipped kernel check or definition containing sorry is introduced.
   Explicit `#print axioms` checks in the scratch review module confirm that the map
   uses only propext, Classical.choice and Quot.sound; the two open theorems and parent
   additionally use sorryAx. The delivery tool also probes every added declaration.
   The map constructs its element by sheafification and adjunction units, with actual
   degree-zero and shift isomorphisms; asIso chooses the inverse of a fixed map, whose
   invertibility determines it uniquely.
3. PASS. Read both split statements and their full docstring arguments. Invertibility
   is a fixed-map resolution computation, while naturality is a fixed-map equality
   independent of invertibility; neither restates the parent's existence of a natural
   family. Degree zero reduces to evaluation in the sections adjunction. Zero
   coefficients give zero Hom and sections groups in every degree. An empty pullback
   gives the zero free source and zero restricted sections complex. Identity pullback
   reduces to naturality in the coefficient map; a zero coefficient map annihilates
   both sides. These are mathematical edge-case checks, not claims that the remaining
   theorems are kernel-proved. Repeated searches using leanfinder (Ext of a free
   representable and slice-site sections), loogle (Sheaf and IsIso), and grep
   (overPullback/injectives and evaluated right-derived cohomology), plus direct source
   searches, found only ingredients, not these comparisons. Mathlib's
   SheafCohomology/Basic still lists the slice-site comparison as a TODO. The existing
   generic abelian siteRestriction_injectives is an ingredient for the first hole;
   its small-site and universe formulation still needs transport to this etale site.
4. PASS. The parent constructs asIso and applies the compatibility equation directly;
   no shorter completed route was found. The public imports provide public definitions
   and instances needed in the construction, including the shift and additive
   structures used by exposed definition bodies. Property modules publicly import the
   map because it occurs in their statements. The parent imports the property modules
   privately. Checked sk-lem-failure-field.realized: the statement and its sole step
   have empty lists, so no realized unit step is bypassed. Expanded No longer needed
   to enumerate all eight old direct proof dependencies; none is globally pruned.
5. PASS. Read all four delivered nodes and compared declaration names, module paths,
   normalized signatures, proof steps, proof_deps and proof_origin with the Lean.
   The parent uses exactly the two property theorems; their plans record the resolution
   and naturality arguments respectively. The construction node has an empty proof
   and explicit data. New nodes include source, searches, created, blueprint ancestry,
   chapter, unit and Lean records. The original node's statement and stmt_deps remain
   unchanged. Source checks of [03Q8](https://stacks.math.columbia.edu/tag/03Q8),
   [072W](https://stacks.math.columbia.edu/tag/072W), and
   [0BKV](https://stacks.math.columbia.edu/tag/0BKV) confirm the cited restricted-sections
   resolution route; the fixed-map compatibility calculation is spelled out in the
   naturality docstring.

Second reading changed only this report: supplied the exhaustive old direct-dependency
list and recorded the independent checks. No Lean repair was needed. One parent hole
is closed by reduction, two lower holes are added: net minus one hole closed, not a
completed proof of the mathematical comparison.
