## What changed

The existing module Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackComparison retains
its declaration signature byte for byte. Its proof now constructs an additive equivalence
from the explicitly defined scalarUnitAbelianComparison and its bijectivity, then applies
pullback compatibility of that same map. The new proof-only import is
Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality.

The new module ScalarUnitCohomologyComparisonFamily constructs scalarUnitAbelianComparison:
moduleExtEquiv, exact forgetting to abelian sheaves, then precomposition with the
constant-integer class of the section 1. Its bijectivity is a separate named theorem.
The new module ScalarUnitCohomologyPullbackNaturality states compatibility only for this
explicit map. The former arbitrary ScalarComparisonFamily and its existence hole were
removed from the unlanded first-worker draft. The invalid assertion that every such
family is natural was replaced, not delivered.

The colimit-preservation import is public in the new comparison module because the
public definition uses its instance. The injective-module acyclicity import is private:
it is needed only for the proposed proof of the bijectivity theorem. The original
module's three public imports remain necessary for its unchanged signature.

## Proved and sorry left

Closed the existing syntactic hole in
AlgebraicGeometry.Scheme.scalar_unit_cohomology_pullback_comparison (one of one).
The declaration remains dependent on sorryAx. This is a decomposition, not a completed
axiom-free proof: one upper hole is replaced by two strictly smaller lower holes.
Relative to the repository baseline, holes closed = 1, holes added = 2, net = -1.
No library-wide or target-closure pruning count is claimed before the pinned ledger runs.

Added holes, both named public theorems with source and full proof docstrings:

- AlgebraicGeometry.Scheme.scalar_unit_abelian_comparison_bijective:
  new-sc-scalar-unit-comparison-family. Only bijectivity, with no pullback assertion.
- AlgebraicGeometry.Scheme.scalar_unit_cohomology_pullback_naturality:
  new-sc-scalar-unit-pullback-naturality. Only equality for the explicit additive map,
  with no existence or bijectivity assertion.

No sorry occurs in a definition or partial proof. The map's data is constructed, not
selected from either new existence theorem. Its upstream moduleExtEquiv uses the
already specified resolution-cocycle characterization, which determines the forward map;
there is no new arbitrary choice of a comparison family. All three delivered files
compile without warnings through lcompile.py --all. A scratch copy with #print axioms
checked the map and all three theorems: each uses only propext, Classical.choice,
Quot.sound, and sorryAx from the open statements/dependencies.

## No longer needed

Removed the proof-only import Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural from the
item, and did not import it in either new module. Its node
lem-sc-module-abelian-zariski-cohomology is no longer a proof dependency of this item:
its arbitrary fixed-scheme natural isomorphism does not specify compatibility across
schemes. The explicit-map bijectivity argument instead uses the already stated
lem-sc-injective-module-abelian-acyclic-zariski.

All four old direct proof-dependency edges were replaced by the two new intermediate
nodes. Of the other three old nodes, def-sc-field-linear-module-cohomology-operations,
def-sc-structure-sheaf-cohomology-pullback, and
lem-weil-pbc-module-pullback-structure-sheaf remain necessary for the unchanged signature
and the intermediate naturality step; their modules remain imported. Only the
ZariskiModuleAbelianCohomologyNatural module is locally pruned from this route; no claim
is made that other targets cease to reach it.

The discarded first-worker comparison-family import is also absent from the item;
its replacement map is available through ScalarUnitCohomologyPullbackNaturality.

## Where the brief, the DAG or earlier work was wrong

The first worker quantified an arbitrary family of additive equivalences and asserted
that all such families commute with all pullbacks. This is false: take two distinct
isomorphic copies of a complex elliptic curve, whose H¹(O) is nonzero. Starting from a
compatible family, postcompose the comparison at one copy with negation but leave the
other fixed. An isomorphism between the copies then violates the naturality square
on a nonzero class. The first draft supplied no normalization preventing this change.

The first draft also had module comments rather than theorem proof docstrings, an
overlong line, an unused proof import, and no update to the existing item's node.
The repair gives a concrete map and two actual parts of its proof. This avoids both
an arbitrary-witness definition and merely renaming the entire upper statement.
The initial report incorrectly called this a proof without reporting its decomposition.

Local literature source files are not installed in this clone. The second reader
checked the primary sources directly at https://stacks.math.columbia.edu/tag/03FD and
https://stacks.math.columbia.edu/tag/01F7. The former gives exact forgetting and
acyclicity; the latter includes the pushforward-resolution comparison needed for
maps between different spaces. The docstring now includes that extra resolution,
rather than assuming pushforward injectives are injective.

## New nodes

new-sc-scalar-unit-comparison-family now records bijectivity of the explicit comparison
map, not existence of an unconstrained family. The map is genuinely constructed from
upstream Ext operations, and the theorem carries the common-resolution argument.

new-sc-scalar-unit-pullback-naturality records pullback compatibility of that explicit
map, not naturality of every equivalence. Its proof plan uses the common-resolution
comparison and the scalar and tensor coefficient maps. Both records include verbatim
Lean signatures, source, proof steps, exact dependency unions, search evidence and
creation provenance. The existing item's proof, proof_deps and proof_origin are updated
without changing its statement or any other owned-by-another-stage field.

No change record is needed: no existing statement, definition or public import changed;
the corrected split statements were new, unlanded sandbox declarations.

## Second reading by Y2

1. Compared the existing module with the repository using diff and an exact substring
   check of its theorem signature. Verdict: byte-for-byte identical signature; only the
   proof and proof-only imports changed. The two additional modules are new on this
   baseline. No existing public definition changed and no forced adaptations are needed.
2. Compiled all three files in import order with lcompile.py. Verdict: clean, no warnings.
   Inspected every sorry and forbidden construct; only the two reported theorem holes
   remain, neither inside a definition. Printed axioms for the constructed map and
   the three theorems in a scratch copy: only the three standard axioms and sorryAx.
   This is not an axiom-free proof of the upper theorem.
3. Read both split statements and their word proofs, and tested their mathematical
   edge cases: empty scheme and affine schemes have zero degree-one groups; the
   naturality equality is tautological on the zero class; an identity morphism uses
   the same map on both sides. Verdict: the repaired statements are true, strictly
   separate bijectivity from compatibility, and add no hypotheses. Independent
   Lean Finder, Loogle, and source grep found Ext construction/composition lemmas and
   fixed-scheme coefficient comparisons but no matching explicit-map result.
   LeanSearch returned an Internal Server Error, recorded as unavailable.
4. Checked the downward reduction, imports, all four original dependency edges and
   dag/units/sk-prop-av-cube.json. Verdict: the route is retained below the unit level;
   the item's node is absent from realized.statement and realized.steps, so no unit
   realization is bypassed. No shorter ready theorem proves the explicit-map
   naturality. Only the fixed-scheme Zariski natural-isomorphism route is pruned.
5. Read the two new records and the existing item's updated record beside the Lean.
   Verdict: the signatures agree verbatim, proof_deps equals the union of step uses,
   and proof_origin describes the repaired construction and reduction. Sources,
   blueprint provenance, chapter, unit, searches and creation metadata are present.

Changes made by the second reader: replaced the arbitrary equivalence family and false
universally quantified naturality with an explicit Ext comparison map, its bijectivity,
and its pointwise pullback equality; gave both holes full source/proof docstrings;
updated all three node proof records; pruned the unused fixed-scheme comparison import;
and corrected the accounting to one upper hole closed and two lower holes added.
