## What changed

Proved `CategoryTheory.first_quadrant_row_collapse` in
`Sheaf.CategoryTheory.FirstQuadrantRowCollapse` with its statement unchanged.
The proof privately imports and assembles the already proved
`SpectralPageZeroPropagation`, `StationaryBottomRow`, and
`FiniteFiltrationLastPiece` modules. The cycle lifts are the stationary
comparison maps followed by inverse cycle inclusions. Convergence transports
positive-row vanishing to the earlier graded pieces, and finite-filtration
collapse supplies the required lift and its invertible edge composite.
The same filtration comparison proves the vanishing corollary.
Updated the item's proof plan and dependencies to match this assembly.
Validation: the delivered module compiled cleanly through `lcompile.py` in
13.4 seconds, with no compiler errors or warnings. Import-direction checks
permit all three new private imports.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.first_quadrant_row_collapse`
(node `lem-weil-pbc-first-quadrant-row-collapse`).
Added 0 holes; no `sorry` remains in the delivered module.
No new statements or modules were required. The three imported dependency
modules also have complete proofs in the current source.
The degree-zero case uses the initial stationary identity and the empty
range of earlier graded pieces; no positive-degree premise is used there.

## No longer needed

Removed the private import `WeilConjectures.CategoryTheory.PBCFiltration`:
the theorem uses the official `DecreasingFiltration` API and needs none of
the separate PBC filtration definitions.
Removed the redundant private import
`WeilConjectures.CategoryTheory.Abelian.Filtration`; the existing public
`CanonicalFiltration` import already supplies this API.
Removed `lem-weil-pbc-short-complex-zero-homology` as a direct proof dependency:
`StationaryBottomRow` already supplies invertibility of the cycle inclusion
and its comparison square. The short-complex results remain used inside the
recorded dependency proofs; this does not withdraw their node or module.
No other planned dependency is unused. No unit route is bypassed and no
existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Step 2's separate short-complex
citation was redundant once its stationary-comparison dependency was used.
No signatures, definitions, instances, attributes or public imports changed.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
