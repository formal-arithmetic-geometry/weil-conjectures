## What changed

`Sheaf.Paper.TwistedPullbackTowerDomain.twisted_pullback_tower_domain` now assembles
all fields of the original Conclusion, with its original signature unchanged.
It tensors the given orientation to identify P with Q, transports constructibility
and intervals through the actual level-comparison isomorphisms, obtains independent
origins and ambient lower bounds, and applies the existing tower compact-support
projection formula to the specified projection map. The supplied hF preservation
hypothesis gives the target domain; the projection isomorphism gives its source domain.
The geometric adjunction and the unit route are retained, without reconstructing purity.

The proof privately imports `TowerCompactSupportProjectionFormula`,
`ProEtaleConstantModuleConstructibility`, `BoundedFlatIndependentCoefficients`,
`KFlatResolutionGeneral`, and Mathlib finite-field characteristic facts. The origins
module privately imports finite-ring origin comparison, ComparisonTorInterval and
exact derived-functor homology compatibility.

The original nine definitions are extracted, with identical signatures and bodies,
into `TwistedPullbackTowerDomainDefinitions`, publicly reexported by the item.
This permits the two smaller lemmas to import the data without an import cycle.
It is not a split to avoid the compiler time limit. The change record is
`coord/changes/f8-twisted-domain-data-extraction.md`.

`TwistedPullbackTowerOrigins.uniform_bounds_origin_lower` is proved from the existing
finite-ring bounded-constructible comparison and comparison Tor-interval equivalence.
It constructs the actual Origin fields, then proves the ambient lower bound by
exact evaluation of cohomology and extensionality of the identity of a tower sheaf.
Private helpers prove interval/isomorphism transport and the coefficient-unit Tor test.
No source-library module, target statement, or definition body is changed.

## Proved and sorry left

Original holes: 1. Closed original hole:
`AlgebraicGeometry.ProEtale.SpTwistedTowerDomain.twisted_pullback_tower_domain`
(node `lem-sp-twisted-pullback-tower-domain`). Its assembly proof has no sorry.

New proved theorem:
`AlgebraicGeometry.ProEtale.SpTwistedTowerDomain.uniform_bounds_origin_lower`
(node `lem-sp-uniform-bounds-origin-lower`). All private helpers are proved. The final main-module compile succeeds with exit
code 0; all four sandbox modules compile, with no remaining linter warnings.

Holes added and left: 1, namely
`AlgebraicGeometry.ProEtale.SpTwistedTowerDomain.pullback_ordered_tate_bounds`
in `Sheaf.Paper.TwistedPullbackTowerBounds`
(node `lem-sp-pullback-ordered-tate-bounds`). This contains just the finite pullback,
Tate-line and ordered tensor bounds, before any orientation or adjunction. The same
local tensor calculation is stated with both factor orders, to avoid requiring an
unprovided symmetry structure on the abstract tower tensor. It omits the origins,
ambient lower bounds, orientation, membership and projection conclusions, whose
combination is real Lean in this delivery. Its proof docstring gives the finite
pullback, scalar-extension, local-trivialization and shift induction argument.
Edge cases checked: d=0, a=z, K=0, empty schemes, the first positive quotient n=0,
and ramified coefficient extensions. No hollow definitions or axioms are added.

This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero holes. It is not a claim of an axiom-free proof of the original result.

## No longer needed

Removed original private proof imports:
`Sheaf.Paper.PullbackTorAmplitude`,
`Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`,
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`,
`Sheaf.Paper.ProEtaleFixedModuleConstructible`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Sheaf.Paper.PurTwistSheafLocallyFree`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
The public statement imports are retained in the extracted data module.
The geometric bounds split still requires the mathematics of PullbackTorAmplitude,
PurTwistSheafLocallyFree and the recorded finite tensor/level comparisons; these are
not claimed as globally pruned modules.

The original direct proof dependencies
`lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-qcqs-over-affine`,
`def-weil-l-adic-coefficient-extension`, `lem-weil-valued-dvr-finite-quotients`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`, `def-sbc-smooth-morphisms`,
`def-weil-finite-type-morphism`, `lem-sf-pullback-tor-amplitude`,
`lem-pur-twist-sheaf-locally-free`, `def-coefficient-twists-detailed`,
`def-weil-proetale-constructible-sheaf`, `det-sp-tower-shriek-levels`,
`det-pe-finite-tor-comparison-noetherian`, `det-sp-coefficient-towers-abelian`,
`lem-sp-compact-support-tower-reduction`, and `det-sp-tower-gluing` are no longer
needed directly by the main theorem proof. Definitions and many of these inputs
remain needed by its smaller lemmas and/or unchanged statement. The main node now
records its actual bounds/origin/projection dependencies.

In particular, `det-pe-finite-tor-comparison-noetherian` is replaced for origins by
`lem-weil-pbc-finite-ring-constructible-derived-origin` and
`lem-exc-comparison-tor-interval`; the former legacy module is not imported.
`lem-sp-compact-support-tower-reduction` is unnecessary for domain membership because
the original hypothesis hF already states the needed preservation.
`lem-weil-valued-dvr-finite-quotients` is not invoked: the existing Base coefficient
instances supply finiteness and Noetherianity. Its and the legacy comparison's
obsolete top-level tool_uses approvals are removed; remaining approvals stay ordered.
No entire module is withdrawn, and no globally unreachable module is asserted.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is sound. Its suggested origins route is less direct than the
currently available finite-ring comparison API. The existing tower projection-formula
node already supplies exactly the specified SpTowerShriek.projection isomorphism
for arbitrary given base/operations, as the earlier review advisory observed.
The orderedLine tensor needs care: symmetry is not separately supplied for the
abstract tower tensor at arbitrary schemes. The bounds lemma therefore retains the
same finite local computation for both factor orders, rather than inventing a symmetry.

The source and statements are unchanged. The current blueprint gamma proof (2) and
the unit `sk-prop-sp-integral-adjunction` were checked; the unit route is preserved.
A textual comparison verifies that the extracted definition signatures and bodies
are identical apart from docstring blueprint ids. The downstream tool reports zero
existing importers, so no forced consumer adaptations are needed.

## New nodes

`def-sp-twisted-pullback-tower-domain-data` attaches the nine extracted original
definitions; it has the original statement prerequisites and no postponed data.

`lem-sp-pullback-ordered-tate-bounds` is the one remaining geometric bounds step,
with no exceptional adjoint, diagonal orientation, origins or projection formula.
Its docstring and node contain the finite pullback and local Tate-line proof.

`lem-sp-uniform-bounds-origin-lower` is the proved general step extracting independent
finite etale origins and the ambient lower bound from uniform actual level bounds.

Blueprint searches for uniform Tor, etale origin and twisted pullback found no
duplicate of these statements; the ancestor tool confirms the integral-adjunction
bijection. All three nodes stay in `sec-smooth-purity`, unit `sk-prop-sp-integral-adjunction`,
and cite the original gamma paragraph (2). Dependency traversal of their statement,
proof and proof-step uses finds no path back to the parent. The change record is
`coord/changes/f8-twisted-domain-data-extraction.md`.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
