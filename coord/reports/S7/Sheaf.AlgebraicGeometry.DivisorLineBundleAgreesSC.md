## What changed

Proved `AlgebraicGeometry.Scheme.divisorLineBundle_agrees_sc` without changing its
signature or any public import. Three fully proved private helpers show that a rational
function with orders cancelling a divisor is a free generator, identify the ideal product
with the explicit module O(-D), and identify O(0) with the tensor unit. The stated tensor-addition
isomorphism and the proved ideal-dual evaluation isomorphism then give the result by an explicit
composition of associators, unitors and the symmetry.

Added proof imports of `WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf` and
`Sheaf.AlgebraicGeometry.DivisorModuleTensorAdd`. Updated the existing node's proof and
proof dependencies to this argument. No public declaration, definition, instance or statement
was changed, and no consumer adaptation is needed. The static checker requires a change record
for the added file-local open namespaces; it is
`coord/changes/S7-divisor-comparison-proof-namespaces.md`, with all five consumers checked.

Validation: the complete item compiled through lcompile.py with exit code zero, in 7 seconds,
without warnings. Both added import directions were checked and introduce no cycle. The
proof handles the empty open by subsingleton sections, zero sections separately, and D=0;
it never assumes properness or excludes negative divisors in its private generator criterion.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.divisorLineBundle_agrees_sc`
(node `lem-pc-divisor-line-bundle-agrees-sc`). Zero holes remain in the item. Added zero holes
and split off zero statements. All three new private helpers are fully proved.

The proof uses the pre-existing theorem
`AlgebraicGeometry.Scheme.Divisor.nonempty_module_tensor_add_iso`
(node `lem-sc-divisor-module-tensor-add`), which still has its existing sorry. This delivery
proves the assigned statement from that named dependency; it does not claim an axiom-free
transitive proof or a proof of tensor addition.

## No longer needed

Removed direct imports of `Sheaf.AlgebraicGeometry.DivisorModuleLocal` and
`Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`, and replaced the direct import of
`WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint` with its stronger existing
`Curve.DivisorIdealSheaf` API. The proof directly uses neither
`lem-sc-divisor-module-local` nor `lem-sc-smooth-connected-curve-local-rings`; it computes
rational generators from the already-proved regular-section criterion instead. Removed their
obsolete tool_uses approvals from the item node. These modules remain transitive dependencies
of the existing tensor-addition theorem; no whole module is withdrawn or claimed pruned from
the targets' import closure. The effective-Cartier and divisor-module definition imports stay.

## Where the brief, the DAG or earlier work was wrong

The original DAG describes a direct Hom-of-principal-ideal comparison but supplies no API
for its overlap calculation. The adopted source now supplies the ideal-product order and
regular-section criteria, which make the negative-divisor comparison direct. Tensor addition
then avoids constructing a separate dual-section map. The current blueprint states a Picard-class
comparison already proved upstream; the assigned stronger explicit-module statement is preserved
verbatim here. The upstream Picard equality alone does not identify the explicit rational-function
sheaf, and DivisorPicRepresentative depends on this item, so neither was used circularly.

The new dependency `lem-sc-divisor-module-tensor-add` is used as a tool from sk-def-pic: its
statement is precisely the needed O(-D) tensor O(D) comparison. No statement or step of the
fixed sk-thm-picard-rr unit is bypassed. No tool_uses approval was added by this worker;
the independent reviewer can record one if required. The source dual evaluation theorem realizes
the existing `lem-sc-invertible-dual` node.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
