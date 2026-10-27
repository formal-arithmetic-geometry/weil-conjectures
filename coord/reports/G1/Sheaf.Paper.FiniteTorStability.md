## What changed

Replaced the `sorry` in `WeilConjectures.finiteTor_stability` by a proof of all five
conjuncts from the declared preservation results. Pullback uses uniqueness of ordinary
left adjoints and its derived natural isomorphism to compare the two implementations.
Tensor uses actual complex representatives, a proved K-flat resolution, and the
normalized one-K-flat tensor comparison. General internal Hom and ordinary direct
image use their existing dimension-dependent preservation declarations. Compact
supports use `FiniteExceptional.operations_preserve` for the given compactification.
Three proved private helpers transport Tor amplitude and constructibility across
isomorphisms and compare pullbacks. All added imports are private proof imports;
existing public signatures, definitions, and imports are unchanged.

The site-perfect Hom formula and sharper Tor interval are isolated in the new module
`Sheaf.Paper.IntrinsicSitePerfectHomWindow`, with its own node. This is a strictly
smaller part of clause (ii), independent of morphisms, constructibility preservation,
finite-field geometry, tensor preservation, and direct images. The original node's
proof and dependencies now describe the implementation. No source-library files or
consumers need adaptation. No definition or existing statement was repaired.

## Proved and sorry left

The original item contained 11 holes. Closed the body of
`WeilConjectures.finiteTor_stability` and added one split-off hole:
`WeilConjectures.finiteIntrinsic_sitePerfect_hom_window`
(node `lem-sf-intrinsic-site-perfect-hom-window`). This is a decomposition, with
one upper hole closed and one lower hole added, not a net hole reduction.
The private helpers `sfStabilityTorOfIso`, `sfStabilityFiniteTorOfIso`, and
`sfStabilityPullbackComparison` are fully proved.

The following 10 original holes remain unchanged, all attached to
`thm-sf-ctf-stability`:

- `WeilConjectures.finiteTor_stability_exceptional_verdier`
- `WeilConjectures.finiteTor_stability_verdier_intrinsic`
- `WeilConjectures.finiteTor_stability_constructible_adjunction`
- `WeilConjectures.finiteTor_stability_origin`
- `WeilConjectures.finiteTor_stability_quotients`
- `WeilConjectures.finiteTor_stability_geometric_quotients`
- `WeilConjectures.finiteTor_stability_integral_images`
- `WeilConjectures.finiteTor_stability_integral_adjunction`
- `WeilConjectures.finiteTor_stability_rational`
- `WeilConjectures.finiteTor_stability_algebraicClosure`

Total remaining holes in the delivery: 11 (10 original, one new). The existing
integral Hom, Verdier and Verdier-reduction proofs are preserved.

## No longer needed

No existing import or module is withdrawn. The proof of clauses (i)-(iv) does not
need separate imports of `lem-sf-etale-direct-image-vanishing`,
`thm-sf-direct-image-tor-amplitude`, `lem-trf-open-ctf`,
`thm-nagata-compactification`, `lem-sf-proetale-constructible-origin`, or
`prop-compactification-coherence-detailed`: the declared pro-etale direct-image
and compact-support preservation results already assemble those arguments.
Some of these nodes remain necessary elsewhere in this multi-declaration node or
transitively in the preservation results, so no global pruning is claimed.
The local perfect-model steps remain in the new site's Hom-window node rather
than being bypassed. The blueprint unit route is preserved.

The complete list removed from the parent node's direct `proof_deps` is:

- `def-compact-support-direct-image-detailed`
- `def-pur-derived-internal-hom`
- `def-pur-hom-complex`
- `def-weil-finite-tor-amplitude`
- `def-weil-site-perfect-complex`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-pc-bounded-exact-term-hom-quasi-iso`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sf-etale-direct-image-vanishing`
- `lem-sf-flat-model`
- `lem-sf-site-perfect-tor-window`
- `lem-sfb-ringed-site-perfect-duality`
- `lem-trf-open-ctf`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `prop-compactification-coherence-detailed`
- `thm-nagata-compactification`
- `thm-sf-direct-image-tor-amplitude`

The definition dependencies remain in `stmt_deps` where applicable. The local
perfect-model dependencies remain below the new Hom-window node; this list
is removal of direct parent edges, not withdrawal of those mathematical results.

## Where the brief, the DAG or earlier work was wrong

The preservation declarations use different presentations of the same pullback
and tensor than the paper module. Applying their results directly does not typecheck.
The proof explicitly supplies the ordinary-adjoint comparison, derived localization,
K-flat tensor comparison and transport along isomorphisms. This is presentation glue,
not a mathematical statement change. No false statement was found.

The site-perfect argument requires both comparison with the specified closed tensor
unit and transport of the precise reversed Tor interval. Neither the general Hom
preservation theorem nor the ringed perfect-duality formula alone states both facts
for these intrinsic functors. The new node retains exactly that unfinished part.

## New nodes

`lem-sf-intrinsic-site-perfect-hom-window` in
`dag/nodes/sec-six-functors/lem-sf-intrinsic-site-perfect-hom-window.json` states the
coefficient-dual tensor formula and interval `[c-b,d-a]` when the first input is
site-perfect. Its proof is the local bounded-projective-model calculation from the
first paragraph of the current blueprint, transported to the specified intrinsic
tensor. Edge cases checked mathematically: empty site slices, zero objects, level
one, arbitrary ramification, and degenerate ordered intervals. There is no
geometric dimension hypothesis or dimension-free assertion for non-perfect inputs.
Mathlib searches and the source proof are recorded in the node and docstring.
No change record is required because no existing definition or signature changes.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
