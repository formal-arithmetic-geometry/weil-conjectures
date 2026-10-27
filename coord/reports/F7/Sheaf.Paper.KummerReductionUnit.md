## What changed

Replaced the original `exists_kummerReductionUnit` hole by a proof from the
coefficient-resolution unit triangle, with four proved private helpers:

- `forget_faithful` proves faithfulness from the supplied section/morphism specifications.
- `boundary_comparison` compares the actual-unit triangle with the rotated Kummer
  short-exact triangle. The triangulated five lemma produces an isomorphism carrying
  the unit to the positive boundary, entirely in the derived category of whole towers.
- `lift_shifted_single` reflects degree-minus-one concentration through exact faithful
  forgetting, obtains a module object from the existing pure-object theorem, and uses
  full faithfulness of the shifted single functor to recover its underlying roots
  isomorphism. This does not assert that derived forgetting is fully faithful.
- `assemble_reduction` combines the generic triangle and purity arguments with the
  adjunction formula, leaving only its specialization to the actual tower categories.

Added `Sheaf.Paper.PowerSystemReductionTriangle`, isolating only the variable-exponent
coefficient resolution and its compatibility with the supplied adjunction unit.
Its statement assumes neither a Kummer sequence nor invertibility of the prime and
mentions no roots or linear cohomology comparison. Its conclusion is a distinguished
triangle; the parent supplies the Kummer exactness and proves the resulting comparison.
The parent statement and every existing public interface are unchanged. No source-library
file or shared dependency was modified. Local irreducibility attributes prevent
unnecessary unfolding of the standard derived-category construction during elaboration;
these attributes do not change any imported module or exported interface.
The generic assembly takes its three endpoints explicitly, so specializing it does
not repeatedly convert projections of a concrete Kummer short complex. Profiling
confirmed kernel checking fell from 96.6 seconds to 25.1 seconds, with the entire
item compiling in 34.3 seconds. The coefficient-triangle module also passed its
individual compile. Profiling settings and diagnostic modules were removed.

## Proved and sorry left

Original holes closed: `AlgebraicGeometry.ProEtale.SpTowerClasses.exists_kummerReductionUnit`
(1 of 1), by a complete assembly proof from the remaining coefficient calculation.

Holes added and remaining: exactly one,
`AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_reduction_triangle`, in its own
new module, with its own node, source and proof in words. This is a decomposition
with zero net hole reduction, not an axiom-free proof of the complete Kummer calculation.
No other declaration contains `sorry`; no definition contains a proof hole.

Edge cases: the coefficient triangle does not require powers on units to be epic,
so it also makes sense when the prime is not invertible. The parent uses the supplied
short exact Kummer sequence to identify its cone. The concentration and full-faithfulness
argument allows the zero roots object, including the empty scheme. Level zero still
uses the positive exponent one; no argument uses oddness of the prime. Neither proof
reconstructs derived morphism equality from their individual evaluations.

## No longer needed

No original import was removed: the item originally imported only
`Sheaf.Paper.TowerClassCoefficients`, which its statement still requires.
The redundant explicit `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
proof import was removed during development; the exact-functor API publicly exposes it.
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle` is a private proof import of
the parent; its redundant public import was removed from the coefficient-triangle
module, whose statement needs only the tower coefficient API.

The parent proof no longer needs `lem-pur-torsion-sheaf-constant-module`
(`Sheaf.CategoryTheory.TorsionSheafConstantModule`) to construct or compare roots actions:
the module object already comes from linear cohomology and the pure-object representation.
It therefore does not import that module for its proof. This is a dependency removed
from this item's plan, not a claim that this module has no other consumers.

`lem-pur-derived-change-of-rings` remains needed by the new coefficient-triangle item;
it was moved below that precise calculation, not pruned from the entire argument.
The existing constant-exponent reduction-normalization and constant p-adic strict-target
interfaces were read but not imported: they have different endpoints and do not supply
the variable-exponent triangle here. No existing module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The previous DAG combines coefficient resolution,
linear cohomology reconstruction and the positive-boundary sign in an unproved existence
statement. The delivered assembly separates these: once the actual-unit triangle is
known, TR3 fixes the boundary sign and exact faithful forgetting reflects purity.
There is no need for an additional two-term homotopy calculation or for a new
quotient-action existence theorem in this assembly.

The new remaining statement is strictly the coefficient-resolution portion of the
old first proof step. It cannot replace the parent by direct application: it has no
roots object or comparison isomorphism, and makes no assertion about cohomology.
The parent uses Kummer exactness, triangulated five-lemma reasoning, reflection of
homology concentration and full faithfulness of shifted single objects to obtain all
three existential witnesses and the prescribed equation.

## New nodes

`lem-sfb-power-system-reduction-triangle`: the variable-power coefficient calculation,
with actual derived-adjunction unit, in `Sheaf.Paper.PowerSystemReductionTriangle`.
Its source is the coefficient-resolution part of clause (2) of the latest geometric
classes blueprint and the original parent proof step 1. Search provenance records
LeanSearch, LeanFinder, Loogle, local source inspection and the blueprint search.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
