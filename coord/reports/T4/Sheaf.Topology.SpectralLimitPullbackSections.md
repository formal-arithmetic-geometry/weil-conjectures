## What changed

Proved `TopCat.Sheaf.spectralLimit_pullback_sections` in
`Sheaf.Topology.SpectralLimitPullbackSections`, preserving its complete signature.
The proof establishes canonical-map coherence by adjunction uniqueness, proves the
unit stalk comparison with its germ formula, descends equality through a compact
open in the equality locus, and descends and glues finitely many local unit sections.
All helpers are private and proved; the two private constructions use the existing
composition isomorphism, which is determined by its unit equation.

Added the proof import `Mathlib.Topology.Sheaves.Sheafify` and updated the node's
proof, proof dependencies and proof origin to describe the implemented route.
The unit `sk-thm-p1` and all target statements are unchanged.
The namespace-opening command is documented in
`coord/changes/T4-spectral-limit-pullback-proof-scope.md`, as requested by preflight;
no consumer requires adaptation.

## Proved and sorry left

Closed: `TopCat.Sheaf.spectralLimit_pullback_sections`
(node `lem-weil-pbc-spectral-limit-pullback-sections`): 1 of 1 original holes.
Added: none. Remaining in the delivered module: none. This is a proof from the
existing declared dependencies, not a decomposition into new holes.

Validation: the complete module compiles cleanly through `lcompile.py` in 10.6 seconds,
with zero textual holes. The main theorem signature was compared verbatim against
the original and is identical. The delivery preflight checks declarations and axioms.

## No longer needed

Removed direct imports:

- `Sheaf.Topology.SpectralLimitConstructibleClosedNonempty`;
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.

Removed direct proof dependencies:

- `lem-sc-left-adjoint-composition-iso-associativity`: the unit equation and the
  injective adjunction bijection prove all composition laws directly;
- `def-weil-pbc-constructible-topology` and
  `lem-weil-pbc-spectral-limit-constructible-closed-nonempty`: eventual equality uses
  a finite union of compact opens in the equal-germ locus and inclusion descent;
- `def-weil-pbc-sites-and-cohomology`: ordinary topological sheaf gluing uses the
  existing Mathlib API, without the project's separate site-covering convention;
- `def-weil-pbc-category-colimit`: the displayed result consists of the canonical
  identities, section descent and eventual equality; no separate colimit object
  is constructed. Its statement dependency remains unchanged.

The constructibly closed nonempty-limit theorem remains a transitive dependency
of compact-open descent; this delivery removes its direct use only. No module is
withdrawn. The short-route searches (LeanFinder, Loogle and grep) found the existing
inverse-image and stalk APIs but no theorem giving the whole spectral-limit result.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned direct constructible-topology argument
and the separate associativity theorem are unnecessary given compact-open descent
and adjunction uniqueness. Empty opens are handled by empty finite families, and
all later-stage bounds use only the given preorder and directedness.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
