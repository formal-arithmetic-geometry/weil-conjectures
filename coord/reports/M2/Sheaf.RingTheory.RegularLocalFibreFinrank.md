## What changed

Replaced the proof of `Algebra.regularLocal_iff_fibre_finrank_eq_dimension`, preserving
its existing signature and all public imports byte for byte. The proof obtains d and r
from `AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_add_trdeg`, uses Mathlib's
regular-local cotangent criterion, rewrites the additive differential-fibre formula,
and cancels r using injectivity of natural-number casts.

The new proof-only module `Sheaf.RingTheory.RegularLocalFibreFinrankComparison` states
`Algebra.fibre_finrank_eq_cotangent_finrank_add`. Its only hole is the additive formula,
strictly the conormal-sequence dimension part of the original argument. Its docstring
contains the complete source proof. It says nothing about regularity or point dimension.
No definitions or existing interfaces were changed; no change record is required.

## Proved and sorry left

Hole closed: `Algebra.regularLocal_iff_fibre_finrank_eq_dimension` (1 of 1 original holes).
Hole added: `Algebra.fibre_finrank_eq_cotangent_finrank_add`, node
`lem-weil-pbc-regular-local-fibre-finrank-comparison` (1 split off).
The first worker's undelivered iff comparison was removed entirely.
This is a decomposition, not a complete proof: one upper hole closed and one genuinely
partial lower hole added, so the delivery's hole net is zero. The target still depends
on `sorryAx` through the additive formula and open imported dimension ingredients.

## No longer needed

Removed the direct proof imports `Sheaf.FieldTheory.SeparablyGeneratedDifferentialsDimension`
and `Sheaf.Paper.SeparableResidueCotangentInjective` from the item's module. Both remain
proof-plan imports of the new additive formula, so no module or old proof-dependency node
is globally pruned. Restored `Sheaf.RingTheory.DimensionAtPointLocalRingTrdeg` as a direct
proof import. All eight original proof-dependency nodes remain needed either directly
or through the additive formula's proof plan. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The first worker moved essentially the full criterion into an iff comparison with the
same hypotheses, rewriting regularity using Mathlib. This retained the full difficulty
and was not a genuine partial step. Its docstring also lacked a complete proof.
The second reading replaced this with the additive fibre formula and a real reduction
using the already stated dimension-at-point theorem. The formula is exactly the first
equality in the proof of Stacks Tag 00TV, checked at
https://stacks.math.columbia.edu/tag/00TV and with injectivity at Tag 00TU.

## New nodes

`lem-weil-pbc-regular-local-fibre-finrank-comparison` now records only the additive
fibre finrank formula. Its fields include source, complete proof plan, dependency union,
three independent search kinds, creation metadata and verbatim Lean statement. No
change records or forced adaptations.

## Second reading by M2

1. Compared the delivered original module with the repository using diff: the existing
declaration signature, docstring and public imports are unchanged byte for byte. Only
its proof and proof-only imports differ. No data or definitions were introduced.
2. Compiled both modules in import order using lcompile.py. The only explicit sorry is
in the named additive formula. No axiom, unsafe, opaque, implemented_by or extern occurs.
Scratch #print axioms checks show only propext, Classical.choice, Quot.sound and
sorryAx for both final declarations; the latter is expected from the listed open holes.
The delivery probe checks every declaration again.
3. Rejected the first comparison as a disguised full criterion. The replacement is the
source's additive conormal formula, independent of point dimension and regularity.
For S=k and q=0 it gives 0=0+0; for k[X] at its generic prime it gives 1=0+1;
at (X) it gives 1=1+0. For k[X]/(X^2) at (X), including characteristic 2,
it gives 1=1+0; regularity is then correctly false since local dimension is zero.
No zero-ring prime exists. These cases check the r=0 case and nonregular cases.
Leansearch was attempted but returned Internal Server Error (recorded as unavailable).
Independent leanfinder and loogle searches, plus rg on Mathlib, the upstream library
and lean/Sheaf found only special cases and ingredients, not the additive formula.
Closing the new hole requires the conormal scalar identifications and exact-sequence
finrank argument, so it is left with its complete proof and node.
4. The top-down reduction uses the existing finite point-dimension formula and Mathlib's
criterion. The retained imports cover the statements and the lower proof plan; proof-only
imports use plain import. No old dependency is globally discarded. Read
`dag/units/sk-thm-p1.json`: this helper is not a realized unit statement or step, and
no unit route or realized record changes.
5. Updated both nodes' proof steps, proof_deps and proof_origin to match the actual
reduction and the additive lemma's source proof. The new node's lean.statement is copied
verbatim from its module. Existing node statements and statement dependencies are untouched.

Changes made by this reading: replaced the iff hole with an additive formula, supplied
its full proof docstring and actual searches, restored the point-dimension reduction,
corrected the dependency records and pruning report, and classified the delivery as a
decomposition with zero net holes closed.
