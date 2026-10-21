## What changed

Filled all five theorem proofs in
`Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit`, preserving every existing
statement and both definitions. Added proved private helpers for changing right
adjoints, transporting compactification adjunctions, inverse exchange pasting, and
mate pasting around a cube. The double-counit equation is Mathlib's conjugate
counit equation for the two composite adjunctions. The support-mate identity and
injectivity of the sum-adjunction hom bijection give the single-counit equation;
the remaining adjunct assertion follows from the second hom bijection.

The compositor formula follows by contravariant conjugation and the two whiskering
identities. The exchange description then reduces refinement compatibility to
the existing compactification cocycle, and open restriction to the two existing
base-change pasting formulas for the same outer square. No evaluation counit is
cancelled as an isomorphism. Updated the node's proof route and dependencies. Documented the module-local
irreducibility attributes and theorem-scoped elaboration/linter options in
`coord/changes/T7-etale-horizontal-double-counit-proof-environment.md`.
The consumer check reports zero downstream modules; no public interface or
consumer adaptation changes are needed.

Validation: the complete module compiled on the project server through
`lcompile.py` in 12.5 seconds, with exit code 0 and no warnings. A source comparison
confirmed that all five existing theorem signatures and both definition bodies
are identical to the originals. The node dependency list equals the union of the
updated proof steps, and every Lean line is at most 100 characters. The delivery
tool performs the final compilation, axiom probes, preflight, and push.

## Proved and sorry left

Closed all five original holes:

- `AlgebraicGeometry.Etale.etaleHorizontalDoubleCounit`.
- `AlgebraicGeometry.Etale.etaleHorizontalDoubleCounit_compositors`.
- `AlgebraicGeometry.Etale.etaleHorizontalDoubleCounit_exchange`.
- `AlgebraicGeometry.Etale.etaleHorizontalDoubleCounit_refinement`.
- `AlgebraicGeometry.Etale.etaleHorizontalDoubleCounit_openRestriction`.

All five realize `lem-pur-etale-horizontal-double-counit`. No holes remain in the
item's source, and no holes or new modules are added. Existing imported statements
are used as the brief permits. This is a proof delivery, not a decomposition.

## No longer needed

Removed the private proof imports
`Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`, and the
redundant `Mathlib.CategoryTheory.Adjunction.Basic` (already public through Mates).
The left-adjoint module is already supplied by the public dependency chain, and no
left-adjoint existence theorem is applied here. Removed
`lem-pur-etale-support-map-compatibility` and
`lem-sfb-quasifinite-compact-support-exact` from the node's proof dependencies and
obsolete tool approvals: their theorems are not used in these proofs. The
quasi-finite comparison remains a statement dependency because it specifies the
comparison data. No public import, declaration, module, or unit route is removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The planned extra support-map normalization
calculation for open restriction is unnecessary once the single-counit theorem
identifies the horizontal comparison with the mate of the specified inverse
exchange. Its compatibility is then a formal consequence of the already proved
base-change pasting identities. Likewise refinement does not require expanding
the normalization family twice: both families give the same exchange mate.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
