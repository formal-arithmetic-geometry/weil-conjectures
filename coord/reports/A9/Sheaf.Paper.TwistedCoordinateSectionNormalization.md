## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.CoordinateSectionNormalization.twistedCoordinateSectionNormalization`
with a reduction to four separate coordinate-comparison statements. The original theorem,
`NormalizationAt`, all existing definitions, signatures, universes and public imports are unchanged.
The proof constructs the affine Cartier witness directly using the relative Cartier criterion,
obtains Noetherianity from finite type, and proves that the projective zero section is closed from
its section equation and the separated projective projection. This avoids constructing a trivial
vector-bundle presentation solely to get its geometry.

The actual first ordinary equation is supplied by `coordinateSectionProjectiveTrace`. The proof
postcomposes it with the projective trace and unfolds the specified `CoordinateLine.integration`
to obtain the second equation. `Etale.projectiveLineTrace_chern` then proves the scalar identity.
Only after this does `coordinateSectionTensorTrace` supply the tensor/coprojection and exceptional
transpose consequences. `coordinateSectionSiteTransport` takes these ordinary equations as
hypotheses and transports them, including the prescribed Cartier realization.
`coordinateCartierBoundarySign` supplies just the signed orientation clause.
For each exponent, `primeUnit.pow` supplies the base invertibility witness explicitly.

Added proof imports of these four modules and the existing relative-Cartier, relative-smooth and
Noetherian interfaces. Added four statement-only modules, one named theorem per module, with source,
complete proof in words and edge-case discussion. Updated the parent proof and proof dependencies,
and supplied matching new DAG nodes. No existing dependency module was edited; no forced adaptation
or definition/statement repair is involved. The unit record has no realized nodes, and the existing
rank-one integration, even-twist and finite-site route is retained.

## Proved and sorry left

Original holes: 1. The body of
`AlgebraicGeometry.ProEtale.CoordinateSectionNormalization.twistedCoordinateSectionNormalization`
is complete from the four intermediate declarations; the item module contains zero `sorry`.
This is a **decomposition**, not a proof closing the mathematics: 1 upper hole removed and 4 lower
holes added, for net -3 holes closed before accounting for other import-closure changes.

The four remaining holes are exactly these public theorems (each proof is `:= by sorry`):

- `AlgebraicGeometry.ProEtale.CoordinateSectionNormalization.coordinateSectionProjectiveTrace`
  — node `lem-pur-coordinate-section-projective-trace`, module
  `Sheaf.Paper.CoordinateSectionProjectiveTrace`.
- `AlgebraicGeometry.ProEtale.CoordinateSectionNormalization.coordinateSectionTensorTrace`
  — node `lem-pur-coordinate-section-tensor-trace`, module
  `Sheaf.Paper.CoordinateSectionTensorTrace`.
- `AlgebraicGeometry.ProEtale.CoordinateSectionNormalization.coordinateSectionSiteTransport`
  — node `lem-pur-coordinate-section-site-transport`, module
  `Sheaf.Paper.CoordinateSectionSiteTransport`.
- `WeilConjectures.PurityFiniteSetting.coordinateCartierBoundarySign`
  — node `lem-pur-coordinate-cartier-boundary-sign`, module
  `Sheaf.Paper.CoordinateCartierBoundarySign`.

Each is a strict part of the original argument. The projective statement has no exceptional or
site conclusions; the tensor statement assumes only the scalar equation and has no site or sign
conclusions; the site statement assumes the ordinary and coprojection equations; the sign statement
has none of the integration or twisted-isomorphy conclusions. Their combination in the original
module is a real Lean proof, including the scalar trace calculation and direct Cartier geometry.
No definition contains a hole, and no axiom or nonstandard kernel bypass was introduced.

Validation: single-file compilation of the direct geometric construction succeeded. The complete
sandbox is being validated through `lcompile.py --all`; final delivery runs the required compiler,
preflight and independent-review classification.

## No longer needed

No original public import was removed and no library module is withdrawn or claimed pruned.
The parent no longer directly follows its original ten-step proof: the projective, tensor, site and
sign dependencies are allocated to their respective smaller nodes. These remain needed there and
are **not** claimed as pruning. In particular the existing Cartier map, root-line pullback, closed
counit/source transport, site coherence, principal-torsor sign and relative cone remain part of the
route. `lem-pur-line-zero-geometry` is not used for the parent's own affine Cartier witness: the
proved finite-flat relative Cartier criterion does this directly; its general geometry remains
available to the smaller sign node. Existing modules imported publicly by the supporting arrow
modules are retained. No source-library declaration, signature, attribute or public import changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The broad original statement combines coordinate-specific
comparisons whose general dependencies do not directly expose these literal arrows. The four
intermediates isolate that glue rather than assuming arbitrary orientations or merely object-level
isomorphisms. The geometric fibre-only `origin_class_projective_comparison` was inspected but cannot
supply the relative statement over arbitrary T. The direct relative Cartier criterion is shorter
than adapting a general vector-bundle presentation. Its cross-unit use is a generic proved
relative-Cartier criterion, not a replacement for a blueprint unit's statement or route.

There is no prior return for this item in the current local rework/return records. Edge cases checked
mathematically: empty base, zero ring, N=1 in the generic tensor lemma, nonreduced bases, ramified
coefficient levels, and characteristic two (negative and positive agree there). No coefficient
flatness or ramification divisibility assumption was added.

A read-only walk of the existing DAG also encounters a pre-existing cycle between
`lem-pc-ring-hom-extension-differential` and its adjacent-differential node, reached through
coefficient conventions. This delivery does not edit those records or introduce that cycle.

## New nodes

`lem-pur-coordinate-section-projective-trace` realizes original Steps 1–3: projective Cartier dual
ideal O(1), actual supported forgetting-support equation and its normalized source. It is deliberately
relative over an arbitrary Noetherian base, unlike the existing geometric-point comparison.

`lem-pur-coordinate-section-tensor-trace` realizes the ordinary parts of Steps 6, 8–9: given the
scalar normalization, prove the closed coprojection mate formula, its invertibility and the tensor
and exceptional transpose equations. Its ordinary coefficient ring A is arbitrary finite and N is
any positive annihilator invertible on T.

`lem-pur-coordinate-section-site-transport` realizes Steps 5–6 and 10: exponent-independent Cartier
realization, bounded-origin/site unit applicability, and transport of the assumed ordinary and
coprojection equations to the actual pro-etale gamma and composition.

`lem-pur-coordinate-cartier-boundary-sign` realizes Step 7 only: the signed Yoneda/relative-cone
calculation in the published affine-line support chart, with no integration assertion.

All four have one new module, the parent's chapter and unit, exact Lean attachment, source and proof
steps with existing dependencies, and recorded natural-language, type/name and Mathlib grep searches.
No change record is needed because no pre-existing definition or statement changes.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
