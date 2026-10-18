## What changed

Proved `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek` in the assigned source module.
The current statement already assumes `[CompactSpace Y]`; it is true as stated. Its proof
uses the chosen compactification, the existing uniform fibre-dimension theorem, proper base
change and torsion direct-image vanishing, a new proved general upper-amplitude theorem,
and the existing proved adjunction/orthogonality criterion. Moved that criterion before the
instance so the instance can use it. Added two proof-only imports. Every existing public
signature and data construction is unchanged; no caller requires adaptation.

The new module `Sheaf.CategoryTheory.RightDerivedFunctorUpperBound` proves
`CategoryTheory.Functor.isLE_rightDerivedFunctor_obj_of_dimension` from dimension shifting
on cycles and the existing K-injective comparison. It applies to arbitrary Grothendieck
abelian source coefficients, not just étale sheaves. The private cycle helper is fully proved.

Validation: the server compiler compiled both delivered modules together in import order,
with no errors or warnings (3.2 seconds for the new module, 16.8 seconds for the assigned module).
The final instance-field form also compiled without errors or warnings (13.3 seconds).

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek.plus_rightDerivedUpperShriek_obj`,
inside the instance `AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek`.
Added zero holes. There are zero `sorry` tokens in either delivered Lean module.
This is a proof, not a decomposition into new unfinished statements.
The proof uses existing stated dependencies, including the project's proper base-change
and geometric torsion vanishing results; no claim is made that all their dependencies are closed.

## No longer needed

None. No import, module, or blueprint unit route is pruned. The finite-amplitude criterion
and the existing proper base-change route are retained. No unrelated dependency is imported.

## Where the brief, the DAG or earlier work was wrong

The route note describes the old unrestricted finite-coefficient instance. The published file
now has `[CompactSpace Y]`, which excludes the disjoint-union counterexample in that note.
It contains no `STATEMENT-DISPUTED` comment. The current theorem is true: the quasi-compact
proper target bounds the fibre dimensions uniformly. Therefore changing its statement would
be unnecessary; this delivery proves it unchanged. The earlier C4 delivery left this exact
one hole open while proving the explicit-amplitude interfaces.

The existing DAG attachments covered the amplitude criteria and left-adjoint theorem but
not the remaining quasi-compact bounded-below instance. A new node now records that instance
with its actual proof dependencies. No target statement or definition changes.

## New nodes

`lem-etale-derived-functor-upper-amplitude`: the fully proved abstract upper-amplitude theorem
in `Sheaf.CategoryTheory.RightDerivedFunctorUpperBound`. Its source is Stacks Tag 07K7,
part (4)(c). The proof works without boundedness below, including d=0 and negative input bounds.

`lem-etale-upper-shriek-quasicompact-bounded-below`: attaches the previously unrecorded source
instance to the quasi-compact proof route. The source is Stacks Tags 0A3V, 095U, 07K7 and
SGA 4 XVIII 3.1.7. Empty fibres, zero coefficients and empty schemes are covered by the
existing fibre-dimension, zero-sheaf and t-structure APIs. No new statement is left to prove.

The instance-body completion is documented, as requested by the delivery gate, in
`coord/changes/C1-upper-shriek-instance-proof.md`, including every direct importer's effect.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
