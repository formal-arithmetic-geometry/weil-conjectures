## What changed

Proved `SheafOfModules.shiftedTensorCanonicalComparison_exists` by descending the
natural two-input shift isomorphism through the resolving presentation. The second
shift is moved first, retaining the coefficient (-1)^(bp) in shifted first degree p.
Closure under shifts and extension/uniqueness are taken from the already proved
`Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`.

The normalization formulas are factored through generic categorical definitions so
that elaboration does not repeatedly expand the concrete sheaf tensor's total
coproducts. The original quantifiers, representative squares, summand equations,
associator, Koszul signs and exact pullback equation are retained. This is a partial
proof delivery: the local and full calculus theorems are still open.

The implementation and consumer audit are recorded in
`coord/changes/U3-shifted-tensor-normalization-api.md`.

## Proved and sorry left

Closed one of the four original holes, with no holes added:
`SheafOfModules.shiftedTensorCanonicalComparison_exists`.
This proof uses no new unproved theorem. Its descent and closure lemmas are already
proved in `DerivedTensorAdditiveConstraints`.

The three unchanged named theorem holes are all attached to
`lem-pur-shifted-tensor-morphism-calculus`:

- `SheafOfModules.derivedTensorAssociator_exists`.
- `SheafOfModules.shiftedTensorMorphismCalculus_local`.
- `SheafOfModules.shiftedTensorMorphismCalculus`.

The existing proofs of the published model, derived symmetry and exact tensor
pullback are preserved or refactored as complete proofs. No definition contains a
hole. No split-off theorem is added.

## No longer needed

The separate fully faithful resolving-restriction proof and its direct imports
`Sheaf.Paper.ResolvingRepresentativeWhiskering` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` are unnecessary:
the existing binary extension and uniqueness lemmas provide precisely the descent
used for shift and symmetry. These are import removals, not module withdrawals;
the dependency may remain in the transitive closure of the descent library.

No DAG dependency is pruned from the unfinished portions. In particular
`lem-pur-total-tensor-signed-coherence` remains needed for the local associativity
and symmetry equations, and `lem-pur-exact-pullback-signed-comparison` remains
needed for the final coherence and pullback clause. No adopted source declaration
or unit route is removed.

## Where the brief, the DAG or earlier work was wrong

The retained large draft was not verified. Its additional associator and local
calculus proofs have been kept in scratchpad, rather than reported as completed.
Repeated compilation failures in this session were definition elaboration costs,
not a missing mathematical dependency. Generic normalization predicates and
explicit endpoints on tensor maps avoid several such expansions.

The previous session's disk-space failure no longer prevents Lean from starting.
The current delivery still requires its server preflight and independent review.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
