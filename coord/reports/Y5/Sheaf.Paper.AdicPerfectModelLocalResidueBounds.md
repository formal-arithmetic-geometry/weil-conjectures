## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.adicPerfectModel_localResidueBounds`
with a direct calculation on the actual pro-etale site. Private proved helpers compare
its chosen ordinary scalar extension with the existing scalar-realization presentation,
prove flatness of the completed model, apply the bounded-above flat K-flat criterion,
and compute zero homology after derived reduction and exact fixed-scalar restriction.
The existing `pbcComplexCounit` and `pbcExtensionCounit_isIso` API supplies the
K-flat derived-reduction comparison.
The original public statement is unchanged.

Added `Sheaf.Paper.ProEtaleLocalScalarHomologyIso` for the local scalar-extension
comparison used in the first step of the original plan. It concerns arbitrary ring
sheaves and arbitrary derived objects, with no model, projectivity or interval.
It isolates the compatibility step; it does not assert the item's residue bound.
The original argument combining that comparison with the model calculation is Lean.
The proof uses a local irreducibility attribute on the chosen scalar-extension data
to avoid repeatedly unfolding its large existence proof. No definitions, consumers,
source-library declarations or target statements changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicPerfectModel_localResidueBounds` (one of one).
Added one hole:
`AlgebraicGeometry.Scheme.proEtaleLocalScalarHomologyIso`, node
`lem-sfb-proetale-local-scalar-homology-iso`.
This is a decomposition, with net hole count zero, not a sorry-free proof.
The bounded-flat model calculation, zero-term argument, fixed-scalar exactness transport,
and the composition proving the original declaration have no sorry.

## No longer needed

The original module had only its public data import; no original import was removed.
The direct model calculation does not use:

- `lem-sfb-adic-perfect-model-complete-reduction`, module
  `Sheaf.Paper.AdicPerfectModelCompleteReduction`: termwise zero is enough, so no
  tensor-associativity identification or transport from the smaller site is needed.
- `lem-pc-bounded-above-flat-kflat-site`, module
  `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`: replaced by the proved
  independent-universe bounded-flat criterion on the actual pro-etale site,
  `lem-weil-pbc-independent-bounded-flat-kflat`.

The original local restriction, tensor/pullback and restriction-K-flat dependencies
remain needed by the new comparison node. They have not been pruned from the argument.
The proof imports `Sheaf.Paper.AdicConstructibleTriangulated` only for its proved private
fixed-scalar exactness lemma; its constructibility result is not applied.
No module is withdrawn and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned complete-reduction comparison is unnecessary for this weaker zero-term
conclusion, and its smaller-site coefficient presentation would require extra transport.
The generic tensor/pullback API is not itself a ready-made scalar-extension comparison
for the arbitrary completed-ring-to-residue map on the actual inverse-image slice.
The new node makes precisely that compatibility step explicit.

## New nodes

`lem-sfb-proetale-local-scalar-homology-iso`, in the same chapter and unit as the item,
records local invariance of derived scalar-extension cohomology. Its natural-language
proof uses flat-term K-flat resolutions, exact actual inverse image, K-flat slice
restriction, the ordinary tensor comparison, and localization counits. It is valid
for zero rings, empty slices, unbounded objects and arbitrary scheme morphisms.
The item separately proves every bounded-model and cohomology-vanishing step.
No change record is necessary: no existing statement or definition changed.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
