## What changed

Proved `AlgebraicGeometry.Scheme.pulled_torsor_normalization_model` in
`Sheaf.AlgebraicGeometry.Morphisms.PulledTorsorNormalizationModel`, with its statement
and public imports unchanged. All supporting lemmas retained in this packet are proved
private helpers in the same module. No other module or definition is changed.

The proof constructs the actual pulled actions and both affine projections, bridges
`GaloisCoverAction` to the categorical torsor interface using the existing section
trivialization theorem, and applies the existing field-torsor classification twice.
It proves the field quotient refinement, total fractions and normality, finiteness
of the integral closures, the common-denominator image equality, and the final
isomorphism over the specified base. The DAG proof records this route.

The returned duplicate `AlgebraicGeometry.Scheme.isIso_sigmaSpec_fin` has been
removed. Its existing upstream counterpart is private and cannot be imported as
a usable theorem. Instead the proof applies Mathlib
the finite `IsIso (sigmaSpec R)` instance to a universe-correct `ULift` index
(the instance in `Mathlib.AlgebraicGeometry.Limits`, line 641). It composes that
isomorphism with the reindexing and product-ring equivalences, and checks the
structural map on each coprojection. No duplicate theorem is retained, and the
unused `sigma_structure` helper is removed as well.

The group universe is handled by `Shrink` before applying the field classification;
the finite spectrum coproduct comparison is reindexed through `ULift`. The arguments
include empty product cases internally; surjectivity over a field excludes an empty
field decomposition. Unit denominators and further splitting after extending K to E
are allowed throughout.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.pulled_torsor_normalization_model`
(node `lem-sfb-pulled-torsor-normalization-model`).

Holes closed: 1. Holes added: 0. Holes left in delivered modules: 0.
Validation: the repaired full module compiled without errors or warnings in
30.7 seconds using `lcompile.py`. Delivery preflight also checks every declaration. `#print axioms` lists `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`: the last is inherited through the
existing library dependencies, not a new hole in this packet. Thus this is a proof
from the existing stated library inputs, not a claim that the entire transitive
closure is already axiom-clean.

No split-off statements or new axioms are introduced. Existing imported theorems
remain dependencies; in particular the geometric-to-categorical torsor bridge uses
`AlgebraicGeometry.finite_etale_torsor_section_trivialization`
(node `lem-sfb-finite-etale-torsor-section-trivialization`).

## No longer needed

Removed proof imports
`WeilConjectures.AlgebraicGeometry.Morphisms.GaloisCoverBaseChange` and
`WeilConjectures.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`.
Their nodes `lem-sbc-galois-cover-base-change` and
`lem-sbc-finite-affine-tensor-base-change` are not used by this proof: pullback
universal properties, section trivialization and Mathlib `pullbackSpecIso` supply
the required constructions directly. Their two obsolete top-level `tool_uses`
approvals are removed in the node copy; the other approvals retain their order.
No source-library declaration is removed or changed.

The node `lem-weil-pbc-integral-closure-commutes-localization` is unnecessary here:
`IsIntegral.exists_multiple_integral_of_isLocalization` directly clears a common
denominator, and `IsIntegral.of_mul_unit` proves the reverse inclusion. All other
original declared proof dependencies are used. The duplicate private helper
`isIso_sigmaSpec_fin` and unused `sigma_structure` are removed; Mathlib supplies
the finite coproduct comparison directly. No Lean modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned source torsor base-change theorem uses a
different torsor interface and a constrained group universe. Directly pulling the
action, using the existing section-trivialization result for its categorical
comparison, and shrinking the group resolves this mismatch without changing any
signature. The total-fraction step also simplifies to the Artinian-unit theorem.
The blueprint unit and its route are unchanged.

The return correctly identified the duplicate finite-index comparison theorem.
The referenced upstream theorem is private, so direct reuse of the public Mathlib
instance with universe reindexing is the available existing-library route. The
public statement and all public imports remain unchanged.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
