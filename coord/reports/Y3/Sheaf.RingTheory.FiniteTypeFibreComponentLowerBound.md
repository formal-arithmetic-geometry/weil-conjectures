## What changed

Proved `Algebra.finiteType_fibre_component_lower_bound` in
`Sheaf.RingTheory.FiniteTypeFibreComponentLowerBound`, preserving its signature,
universes, hypotheses and public imports. Updated its proof documentation and the
existing DAG node `lem-zl-finite-type-fibre-component-lower-bound` to the shorter
height-theoretic argument.

For a component `V(qbar)` of `C/J`, its inverse image `q` contracts to `m`.
Passing to `A = B/ker φ`, the contraction `p` satisfies `pC = J`. Mathlib's
`Ideal.height_le_height_add_of_liesOver` (Stacks 00OM) and minimality of
`qbar` give `height q ≤ height p ≤ dim A`. The finite-type dimension formula
supplies `d = height q` and `r = trdeg_k κ(q)`; the existing minimal-component
bound applied to the zero prime of `C` gives `dim C ≤ d+r`.
The fraction-field and third-isomorphism equivalences identify `dim V(qbar)`
with `dim(C/q) = r`. Natural-number subtraction finishes the proof.

Added proof imports of
`WeilConjectures.RingTheory.MinimalComponentDimensionMaximumCore`,
`WeilConjectures.RingTheory.KrullDimension.FiniteType`, and
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`. The first is an existing
proved generic algebra tool (node
`lem-weil-pbc-minimal-component-dimension-maximum-bound`); the second supplies
the proved dimension-of-point-closure theorem. No unit statement or unit step
is bypassed: the item's unit has no `realized` attachment for this auxiliary
node, and the affine fibre-component bound used by Bertini is unchanged.
The new cross-unit tool use is requested for maintainer review; no approval
was added to `tool_uses`.

Searches run through `msearch.py`: LeanFinder for the component lower bound
returned eight related results including the height inequality; Loogle for
`"ringKrullDim", Algebra.FiniteType` returned no hits; grep for
`height_le_height_add_of_liesOver|height_eq_zero` located the needed height
APIs. Read Stacks `varieties.tex`, the proof of 0B2L (2)(a), and
`algebra.tex`, the statements/proofs of 00OM and 00P1. This is a shorter
algebraic proof of the same consequence of 0B2L.

The module compiles cleanly using `lcompile.py`. Edge cases are handled by
the same argument: a zero fibre has no component to choose; for a nonempty
fibre all selected ideals are prime and proper; `dC < dA` causes no issue
because the conclusion uses natural-number subtraction. The rationality
hypothesis is retained and destructured but is not needed by the argument.

## Proved and sorry left

Closed the single original hole:
`Algebra.finiteType_fibre_component_lower_bound`
(node `lem-zl-finite-type-fibre-component-lower-bound`).

Proved 1 of 1 original sorries. Zero sorries remain in the delivered module;
zero holes added, zero statements split off. All auxiliary results are
existing declarations; no new theorem or definition was introduced.

## No longer needed

Removed these direct proof imports:

- `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.RingTheory.Localization.BaseChange`
- `WeilConjectures.RingTheory.DimensionAtPointComponents`
- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`

The following former planned proof dependencies are no longer directly used:

- `lem-kun-transcendence-degree-tower`: no generic-field tower is constructed.
- `lem-weil-pbc-generic-fibre-localization-domain-irreducible`: no generic
  fibre localization is constructed.
- `lem-weil-pbc-dimension-at-point-components`: no local dimension of a fibre
  at its component generic point is evaluated.
- `def-weil-affine-spectrum`: removed from proof dependencies; the unchanged
  public Scheme import remains available to the signature.
- `def-kun-topological-dimension-at-point`: removed as a direct proof input;
  local-dimension expressions occur only inside the existing formula used
  to obtain the finite height and residue transcendence degree.
- `lem-weil-pbc-fibre-dimension-bounded-open-upstairs`: the height inequality
  replaces the upper-semicontinuity argument.

Removed the obsolete top-level tool approvals for
`lem-weil-pbc-dimension-at-point-components` and
`lem-weil-pbc-fibre-dimension-bounded-open-upstairs`; retained the other two
in their original order. Some removed direct imports remain transitive
imports of existing dimension theorems; no claim is made that these modules
leave the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The seven-step generic-fibre proof plan was
unnecessarily long for this affine assertion: the Noetherian height
inequality at a minimal prime of the fibre gives the bound directly after
the finite-type dimension computation. This also shows that the retained
rationality assumption is unnecessary for this particular conclusion.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
