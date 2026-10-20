## What changed

Proved `AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField` with its original
signature, universes and public imports. Added the proved public tool
`DiscreteModule.subsingleton_H_of_dense_generator_cyclic_quotients` in
`Sheaf.RepresentationTheory.ProfiniteCyclicTorsionCohomology`. No other existing Lean
module or public interface changes.

The algebraically closed case uses the existing separably closed torsion bound and
étale/pro-étale comparison. For finite fields, use the proved source additive
field/Galois comparison, obtain density and every cyclic quotient from the completion
universal property, and apply the new torsion vanishing theorem. Transfer sheaf H to
the Ext-derived convention before using the torsion bound.

The new proof is constructive at each finite cyclic stage: a smooth function has finite
period a and a finite-image exponent e; at order ae its norm vanishes and cyclic partial
sums give a primitive. The coinduced exact sequence gives H²=0 and torsion dimension
shifting gives all higher degrees. Zero coefficients, order-one quotients, the wraparound
equation, and torsion coefficients without a common exponent are included.

Both files compiled together through `lcompile.py --all`. Kernel axiom inspection of the
new theorem gives exactly `propext`, `Classical.choice`, `Quot.sound`. The item still
inherits `sorryAx` from pre-existing dependencies; its own hole is closed and no new
holes are introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.cohomologicalDimension_baseField` (`sk-lem-base-field-cd`).

Added 0 holes. No `sorry` remains in either delivered Lean file. The new public theorem
and all five private helper proofs are complete. This is a proof, not a decomposition
into holed intermediate statements. No theorem is split off with `sorry`.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules` (`lem-exc-abelian-sheaves-gmodules`);
- `Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants`
  (`lem-exc-field-sections-stalk-invariants`);
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
  (`def-weil-pbc-etale-cohomology`); its API remains transitively available through the
  actual sheaf-H/Ext-derived bridge;
- `Sheaf.RepresentationTheory.BaseFieldContinuousCochains` (`det-base-field-cd-cochains`);
- `Sheaf.GroupTheory.CyclicInflation` (`det-base-field-cd-inflation`).

The additive field/Galois comparison already exists in the adopted source for all
abelian sheaves, so the first two statement modules need not be imported for this proof.
The coinduced argument directly uses the proved source Ext/coinduced API; it does not
need the auxiliary presentation of continuous cochains or the explicit periodic
inflation comparison. Norm multiplication under cyclic refinement is proved directly
by summing a-periodic functions on ae terms. The auxiliary directed-union and
quotient-colimit constructions of the old plan are not used.

Removed the two obsolete top-level tool approvals for
`lem-exc-abelian-sheaves-gmodules` and `lem-exc-field-sections-stalk-invariants`, retaining
all other approvals in their original order. No module is withdrawn and no adopted
source declaration, signature, attribute or public import is altered. These are local
dependency removals; other consumers may still need the removed modules.

## Where the brief, the DAG or earlier work was wrong

No statement was disputed or changed. The old proof of the reverse algebraically closed
inequality unnecessarily built a nonzero degree-zero sheaf: the dimension is in
`WithTop ℕ`, so `zero_le` suffices.

The source already contains the exact additive comparison needed, in
`Scheme.sheafHAddEquivGaloisH`; the existing finite-ring field-equivalence node is not
its general all-abelian-sheaf cohomology statement. A new node records that existing
proved declaration without editing its source.

The unit's Galois comparison, Frobenius completion, coinduced acyclicity, and finite cyclic
norm cancellation are retained. The implementation changes below the vanishing step:
finite cyclic partial sums and torsion dimension shifting replace the unit text's
explicit filtered colimit of periodic resolutions and inflation maps. This difference
is made explicit here and in the revised node rather than attributing a periodic
resolution argument to the Lean proof. The unit record currently has empty `realized`
entries for its statement and all four steps; no unit record is changed in this packet.

## New nodes

`lem-base-field-etale-galois-cohomology` records the existing proved source declaration
`AlgebraicGeometry.Scheme.sheafHAddEquivGaloisH`, with Stacks Tag 03QU as its source.
It adds no Lean declaration or hole and is a tool for the opening field comparison.

`lem-base-field-profinite-cyclic-torsion-cohomology` records the new, completely proved
compact-group torsion vanishing theorem. It is strictly the group-theoretic part of the
finite-field argument and does not restate the assigned field theorem. The node includes
the finite cyclic primitive, invariant lifting, and dimension-shift proof in words.

Both new nodes have three-kind Mathlib searches, the item's chapter and unit, and
blueprint ancestry. No change record is required: existing public statements and data
are unchanged, and all new public API is in a new `Sheaf` module.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
