## What changed

The original module's declaration signature and docstring are byte for byte unchanged.
Its proof combines the dimension-localization lemma with the polynomial presentation
lemma at the same existentially chosen h. The generic presentation helper is now fully
proved by explicit polynomial evaluation, quotient lifts, localization lift, unit
cancellation and extensionality. It uses only Mathlib, with no new data definitions.

The dimension helper retains the first worker's existential h correction: arbitrary h
avoiding q does not suffice. Its source proof remains open. Its private proof imports now
include the original dimension/presentation modules and the Mathlib tools named by its
plan, so moving the proof obligation preserves these dependencies in the import closure.
The presentation node's proof and dependencies now describe the universal-property proof;
the dimension node's presentation step now precedes its fibre comparison. No existing
statement or definition changed, and no change record is necessary.

## Proved and sorry left

Closed original hole:
`Algebra.exists_localization_relativeGlobalCompleteIntersection`
(node `lem-weil-pbc-equation-count-localize-relative-global-complete-intersection`).
This is a decomposition, not an axiom-free proof: it still depends on the dimension hole.

Closed the first worker's new presentation hole:
`Algebra.exists_localization_presentation`
(node `new-equation-count-localize-presentation`). Its proof contains no sorry and its
axioms are only the three permitted foundational axioms.

One new hole remains:
`Algebra.localized_presentation_is_relativeGlobalCompleteIntersection`
(node `new-equation-count-localize-rgci`). It is a named public theorem with a complete
source proof in its docstring. It supplies the dimension and RGCI clauses, without the
algebra equivalence or its generator formulas; the latter have been proved separately.

Relative to the repository item: one hole closed and one new hole added, net zero.
Relative to the first worker's sandbox: one additional hole closed and none added.
No original item theorem is yet independent of sorryAx. No sorry appears in a definition.

## No longer needed

The main module removes its direct private imports of
`Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`,
`Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`,
`Sheaf.RingTheory.PolynomialQuotientDimensionAtPointHeightDifference`, and
`Sheaf.Topology.DimensionSupremumLocalDimensions`. These four modules are now privately
imported by the remaining dimension helper; none is claimed globally pruned.

Every original proof dependency below is removed from the main node's direct proof_deps:

- `def-weil-pbc-mv-polynomial-ring`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`
- `lem-weil-pbc-spec-localization-away-basic-open`
- `lem-weil-pbc-polynomial-scalar-extension`
- `lem-weil-pbc-tensor-quotient-base-change`
- `lem-weil-pbc-localization-away-polynomial-quotient`
- `def-weil-ring-localization-away`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-polynomial-quotient-dimension-at-point-height-difference`
- `lem-weil-pbc-noetherian-height-quotient-bound`
- `def-kun-topological-dimension-at-point`
- `lem-weil-pbc-localization-away-tensor-iso`
- `def-weil-pbc-module-localization-away`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-dimension-at-point-open-subspace`
- `lem-weil-pbc-fibre-ring-primes-bijection`
- `lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`
- `lem-weil-pbc-dimension-supremum-local-dimensions`
- `def-weil-pbc-relative-global-complete-intersection`

The main proof now uses only `new-equation-count-localize-presentation` and
`new-equation-count-localize-rgci`. The mathematical dimension steps still occur inside
the latter's plan. Definition dependencies still occur in the main statement.
`lem-weil-pbc-localization-away-polynomial-quotient` is no longer used by either new
proof plan: the presentation proof constructs the maps directly using
`lem-weil-pbc-localization-away-universal-property`. Its Mathlib module was not a direct
import of the original item, so no additional module pruning is claimed.
The old false universal-h helper is replaced by the existential helper. No unit-level
node or module is pruned, and `dag/units/sk-thm-p1.json` and its realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker repaired the saved helper's false assertion for arbitrary h avoiding q.
For R=k[t], n=c=1, f=t*x, q=(x), and h=1, the generic fibre has dimension zero while
the fibre at (t) has dimension one. Choosing h=t avoids q and removes the bad fibre.
This validates the need for existential h and agrees with Stacks 00ST (3).

Second reading found that the report claimed the removed dimension modules remained
needed, but the dimension helper did not import them. This was repaired. The presentation
hole could also be closed directly with the universal properties already in Mathlib.
The presentation node listed unused dimension/RGCI statement dependencies; those were
removed. Its old tensor/one-variable-quotient plan was replaced by the proof actually used.
The dimension node formerly invoked the presentation before its named presentation step;
that step was moved before the fibre comparison. LeanSearch's prior service failure remains
recorded as unavailable, not evidence of absence.

## New nodes

`new-equation-count-localize-presentation`: now proved, for every polynomial h, including
h=0. It constructs an equivalence and proves both generator formulas. Its node records
polynomial and localization universal-property dependencies.

`new-equation-count-localize-rgci`: one remaining dimension/RGCI obligation covering original
steps 1, 2, 4--7, using the proved generic presentation for original step 3. Its existential
choice and exact fibre equality are needed; no equations or dimensions were weakened.
No change records or forced adaptations were added.

## Second reading by E1

1. PASS. Read all three delivered modules and compared the existing module with the
repository using diff. Only its private proof imports and theorem body differ. Its full
signature and original docstring are byte for byte identical. Both other modules and
nodes are new. No existing definition, public import, declaration visibility or target
statement changes. No change record is required.

2. PASS, with the reported dimension hole. All three files compile locally through
lcompile.py without errors or non-sorry warnings. Explicit #print axioms probes verify
the presentation theorem has only propext, Classical.choice and Quot.sound; the dimension
helper and main theorem additionally use sorryAx. Text inspection finds exactly the
one public named theorem with sorry, and no axiom, unsafe, opaque, implemented_by, extern,
or hollow definition. The presentation proof constructs both homomorphisms, checks all
relations, and proves both composite identities. No arbitrary unproved witness supplies
definition data; choosing h inside the proof of an existential proposition is legitimate.

3. PASS. The presentation helper is strictly the algebra-presentation part and is now
proved. The remaining helper omits the equivalence and its specified generator identities,
and isolates the dimension argument. Its detailed source docstring and matching node
state a true part of the argument. Checked Stacks
[00ST (3)](https://stacks.math.columbia.edu/tag/00ST),
[00QH](https://stacks.math.columbia.edu/tag/00QH), and
[0B7I](https://stacks.math.columbia.edu/tag/0B7I).
For n=c the expected dimension is zero; for c=0 it is n; for n=c=0 a prime gives a
nonzero residue field and h=1 works. Over a zero base ring or a zero quotient there
is no q, so the dimension lemma has no instance; the independent presentation proof
still covers h=0, nilpotent g, redundant equations and zero rings. The universal-h
counterexample above was checked. Independent LeanFinder searches used inverse-generator
universal-property and finite-type/basic-open/fibre-dimension wording; Loogle searched
MvPolynomial.aeval/rename and topologicalKrullDim; rg inspected both library roots and
Mathlib. Existing localization presentations are over S, rather than the displayed
Option quotient over R. Existing relative-GCI localization theorems assume S is already
RGCI, which is unavailable here. FibreDimensionNeighborhood is a genuine useful upper
bound sublemma, but neither it nor GlobalCompleteIntersectionEquidimensional supplies
the entire remaining statement. No duplicate exact theorem was found.

4. PASS after repair. The generic presentation takes the direct Mathlib universal-property
route. Its public imports serve its signature; the dimension helper's additional imports
are private and serve the still-open proof plan. The original four dimension modules
remain reachable, so the change does not accidentally prune obligations. The exhaustive
list above accounts for every old direct proof dependency. All seven original argument
steps remain in the new proof or the dimension plan; sk-thm-p1's realized statement and
steps are unchanged. No global module pruning or net decrease in holes is claimed.

5. PASS after repair. The main node's proof is the two-lemma assembly and its dependency
union matches those two imports. Both new Lean statements agree with their node's
lean.statement record. The presentation node now records the actual evaluation/lift/
extensionality proof and its used dependencies. The remaining dimension node records
the complete still-open source plan, with the proved presentation used before base change.
Both new nodes have source, proof_origin, three kinds of recorded searches, created item
and group, chapter/unit and blueprint ancestry. Existing node fields outside stage-3
ownership are unchanged.

Second reading changed: proved the polynomial presentation; restored the dimension
plan's private imports; corrected presentation-node dependencies and proof, dimension
step order, and exhaustive pruning/hole accounting. The item remains a decomposition.
