## What changed

Implemented the compatible compactification construction, finite projection substitution,
ordinary identities and associativity, and the intrinsic system equation and identity transport
in `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly`. The public statements and existing definition bodies are unchanged apart from explicit implicit
arguments in `canonical`. The existing `candidateCompositor` declaration moves verbatim into the
new normalization module and remains public through the original module's public import.
This avoids duplicate expressions with different inferred compactification instances.

The tensor input only needs a bounded-below etale-origin witness. A proved private helper
constructs the etale tensor witness using comparison monoidality, bounds its image using the
finite Tor interval of the second factor, and reflects boundedness by exact faithful comparison.
No finite Tor condition on K is added. The private `canonical_eq` helper unfolds only the canonical specialization of the shared
compositor. Private adjunction lemmas transport the canonical system
identity equations through `canonicalBridge`; no detection by evaluations is used.

Retained and connected the earlier attempt's isolated Cartesian normalization statement as
`Sheaf.SixFunctors.CartesianCompactSupportCompositor`. It is the original argument's steps 2–3,
with no tensor, projection, geometry-existence, associativity or system conclusion. Updated the
parent node to the actual reduction. Local irreducibility of derived-functor and compositor constructions, explicit candidate
indices, and direct scalar-ring parameters avoid expensive definition unfolding, without
changing those APIs. The latter matters for the definitionally identified system categories:
local scalar abbreviations otherwise trigger a large comparison of their transition maps.

## Proved and sorry left

One original hole is reduced: `AlgebraicGeometry.ProEtale.ProjectionTriangleAssembly.
projectionCompatibleTriangleAssembly` has a complete proof from the recorded dependencies and
one split-off theorem. Its signature is unchanged.

One hole is added/left: `AlgebraicGeometry.ProEtale.cartesianCompactSupportCompositor`, node
`lem-sf-cartesian-compact-support-compositor`. Its proof is exactly `by sorry` and its docstring
and node give the proper/open adjunction normalization and site-tower cancellation argument.
This is a decomposition (one hole closed, one added), not a net proof closure. There are zero
holes in definitions or private helpers.

## No longer needed

Removed direct imports of `Sheaf.Paper.QcqsCompactSupportRealization`,
`Sheaf.SixFunctors.OpenTensorNormalization`,
`Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction`,
`Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange`, `Sheaf.Paper.FiniteSiteTowerPaste`,
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
`Sheaf.Paper.ProperOpenCoefficientMate`, `Sheaf.Paper.PullbackTorAmplitude`,
`Sheaf.Paper.FiniteCoefficientTensorCtf`, and `Sheaf.Paper.ProEtaleConstructibleOrigin`.

The normalization tools remain dependencies of the new Cartesian compositor node; they are
not globally pruned. The tensor-ctf node `lem-sf-tensor-ctf` is unnecessary on this proof route:
boundedness and an etale-origin witness suffice, so constructibility of the tensor is not proved.
The nodes `lem-sf-pullback-tor-amplitude` and `lem-sf-proetale-constructible-origin`
are replaced here by their source-library APIs and the existing etale-origin definition. Removed the parent's direct tool-use approvals for
`lem-weil-pbc-locally-noetherian-quasi-separated`, `def-weil-proper-morphism`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`, the normalization tools above,
`lem-sf-pullback-tor-amplitude`, `lem-sf-tensor-ctf`, `lem-sf-proetale-constructible-origin`,
`def-exchange-projection` and `thm-sf-comp-composition`. The definitions remain statement
imports, and the normalization tools remain under the split-off node. No library module is
withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The separated-structure-map tower normalization does not directly cover the present ambient
spaces. The isolated Cartesian comparison follows the non-separated site-tower route instead.
The previous report described unfinished work; this packet now connects the split-off lemma
and completes the combining argument. The previous disk-space failure no longer occurs.

System identity equations require transport through `canonicalBridge`: the ambient canonical
system calculus is not definitionally the arbitrary `realizedSystems` presentation.

## New nodes

`lem-sf-cartesian-compact-support-compositor` isolates proper/open normalization and equality
with the independently defined canonical origin compositor, on every bounded-below origin
input. Its edge cases include identity and empty schemes, and impose no separated structure
map, finite Tor input or projection invertibility hypothesis. It has its own module, source,
proof in words and recorded Mathlib searches. The declaration move is recorded in
`coord/changes/c2-shared-candidate-compositor.md`. No public signature or mathematical definition
has changed, and no other module is adapted.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
