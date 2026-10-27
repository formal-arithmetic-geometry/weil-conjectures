## What changed

Reduced `finiteFreeSystemRestriction` along its existing proof plan. The integral
coordinate bijection descends modulo every uniformizer power by a proved generic
quotient argument; associated uniformizers give the actual ramified ideal equality.
The final proof uses separate scalar-normalization and geometric-generator steps
and pastes their preserved generators into the compactification word.

The existing declarations from `quotient` through `levelwiseCtf` move with the same
names, signatures and visibility into `FiniteFreeSystemRestrictionData`.
`U` keeps its body, with its definitionally equal functor type written explicitly
using the proper/open system categories. It is a reducible definition, retaining
normal unfolding by consumers while sharing the category types in the coherence proof.
The two compactification operations instantiate the fully constructed generic
`compactScalarIso` and `compactWord`, with the same component arrows and directly
proved naturality, instead of nested associators and whiskering. This resolves
expensive unfolding in the compactification proof; other data bodies are unchanged.
The original module publicly re-exports them. This permits the two new statement
modules to import the data without an import cycle. Existing public imports stay
in the original module; the data module imports only what its own declarations need.
The change record is `coord/changes/H3-finite-free-system-proof-decomposition.md`.

Validation: all four delivery modules compile without warnings. The normal
consumer batch also passes for the five current projection modules
(`SystemScalarProjectionData`, `SystemScalarBasisDistributivity`,
`SystemScalarRefinementRestriction`, `SystemScalarTensorConstituents`, and
`SystemScalarProjectionIdentification`) and current
`Sheaf.SixFunctors.RamifiedScalarExceptionalLimit`. The unchanged
`IntegralScalarIsomorphismExchange` consumer also passes against the final code. No consumer source is adapted or included in the delivery.

The final `RamifiedScalarSystemTranspose` check has no type error but exceeds
the limit (69 seconds); its exact original source also exceeds the limit against
the published item in an isolated baseline (67 seconds). This existing consumer
is held by B4 and is not adapted in this delivery.

## Proved and sorry left

Original holes: one, `WeilConjectures.FiniteFreeSystemRestriction.finiteFreeSystemRestriction`.
Its body is replaced by a complete reduction, with the original statement unchanged.
The proved private `generic_compact_preservation` composes the generator squares
using `paste_inner`, `paste_outer` and functor-mapping lemmas. The concrete
`compact_composition_of_compatibility` applies it to the system functors.
This avoids repeatedly unfolding the concrete localization categories. The private generic `quotient_basis_bijective` proves the finite quotient basis step;
`ramifiedIdeal` is proved using equality of associated principal ideals and powers.

Two holes added, each the whole proof of a public theorem in its own module:

- `WeilConjectures.FiniteFreeSystemRestriction.scalarAssertions_of_reducedBasis`,
  node `lem-coef-finite-free-system-scalars`: only the scalar assertions from
  compatible reduced bases (original Steps 2--5).
- `WeilConjectures.FiniteFreeSystemRestriction.geometryCompatibility_of_scalars`,
  node `lem-coef-finite-free-system-geometry`: only normalized geometric data and
  generator compatibility from the scalar assertions (original Steps 6--12).

This is a decomposition: one original hole replaced by two strictly smaller
obligations, not a claim of net proof progress. No hole remains in a definition.
The already proved `levelMap_transition` and `inverse_compatibility` are retained.
The generic component constructors and coherence theorem compile with no holes;
only the two listed scalar/geometric public theorems contain `sorry`.

## No longer needed

Removed the private import `Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis`:
the theorem already receives the integral basis bijection as a hypothesis, so no
existence-of-basis theorem is used. The node `lem-sfb-local-field-integral-basis`
is not a proof dependency of this reduction; its statement citation is retained.

The proof no longer needs `def-coef-normalized-dvr-tower`: its coefficient
arithmetic is proved directly with quotient rings and associated principal ideals.
It also does not use `lem-sf-ambient-clopen-restriction-uniqueness` or
`lem-sf-semilinear-proper-open-mate-pasting` as proof lemmas: the geometric step
uses section identities and general mate pasting, and the final compactification
calculation is a proved generic categorical argument.

The nodes `def-pc-sheaf-restrict-scalars`,
`def-sp-semilinear-constant-ring-operations`, `def-weil-finite-tor-amplitude` and
`def-weil-finite-torsion-constructibility` remain definition/statement dependencies
of the extracted data or new scalar statement. Removing their redundant direct
proof edges does not remove their constructions. The other original proof
dependencies appear in the scalar and geometric intermediate proof plans.

No existing module is withdrawn. The public imports of `NormalizedDVRTower` and
`SemilinearProperOpenMatePasting` stay for the original module's consumers and
published data. No globally pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed. The original plan's broad scalar and
geometric steps do not directly match a single library theorem with the specialized
`ScalarAssertions` / `Geometry` signatures. Those specializations are now explicit,
separate work items with source, proof text and dependency records. The supplied
basis should be used directly rather than chosen again independently.

The source node points at an older blueprint path whose rational-operations file
has since moved or disappeared from `latest`; the existing agent-expanded proof
is retained as its source, and the current scalar-six proof was also checked
for the finite-sum and adjunction-map argument. No unit route is bypassed.

## New nodes

`lem-coef-finite-free-system-scalars` states scalar normalization, constructibility,
Tor amplitude [0,0], exact extension and K-injective preservation from the one
compatible quotient basis. Its edge cases include the empty site and rank zero;
no independent finite-level basis is chosen.

`lem-coef-finite-free-system-geometry` states the specified section-normalized
ordinary and derived comparisons and their generator equations, assuming the
scalar assertions. It includes all the required mates, clopen projectors and
proper/open comparisons; it does not assert the compactification word equation
or the coefficient arithmetic. Its proof uses entire systems before evaluation.

The existing definition-owner node is reattached to the extracted data module;
the original theorem node's proof and proof dependencies follow this reduction.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
