## What changed

Proved `AlgebraicGeometry.sections_morphism_to_proj_polynomial_ring` in
`Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing` without changing its signature
or its public imports. All construction helpers are private and fully proved.

On the generating opens, the proof constructs ratios with free-generator coefficients,
evaluates polynomials, constructs local maps with `Proj.fromOfGlobalSections`, and glues them.
It proves the exact inverse-image, fraction, and base-map equations. It glues the map from the
ordinary pullback of the twisting module using `Scheme.Modules.glueHom`, proves that map
locally bijective, and compares the ordinary and tensor pullbacks through uniqueness of left
adjoints. Compatibility of adjunction units proves the statement's exact final equation.

Added proof imports of `WeilConjectures.Mathlib.AlgebraicGeometry.Gluing`,
`WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`, and
`WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus`. Updated the existing node's
proof, proof dependencies and proof origin to describe this implementation. No public
interfaces, source-library files, target statements, or definitions used by targets changed.

Validation: the complete final proof compiles without errors or warnings through `lcompile.py`
(37.7 seconds for Lean after import cleanup). A preceding axiom probe of the complete proof
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The theorem's signature is
byte-for-byte identical to the original. The construction introduces no nonempty-scheme,
nonzero-ring, or positive-dimension assumptions; empty opens, the zero ring, and `m = 0`
are covered by the same free-generator and polynomial arguments.

## Proved and sorry left

Closed the original and only hole:
`AlgebraicGeometry.sections_morphism_to_proj_polynomial_ring`
(node `lem-weil-pbc-sections-morphism-to-proj-polynomial-ring`).

Proved 1 of 1 original sorries. Added 0 holes; split off 0 statements. There are no sorries
left in the item or elsewhere in this delivery. This is a complete proof, not a decomposition.

## No longer needed

Removed these unused private imports:

- `Sheaf.Topology.GlueSheavesOfModules`: the proved source `Scheme.Modules.glueHom` directly
  constructs the compatible map from local free generators. Its locally bijective criterion
  proves the isomorphism, so no packaged gluing of local modules or local inverses is needed.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: already publicly supplied by the
  unchanged `TensorPullbackAdjunction` public import.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: already publicly supplied by the
  unchanged nonvanishing public import.
- `WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes`: already publicly
  supplied by the unchanged `Sheaf.Paper.NonvanishingSectionTrivializes` public import.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the existing chosen adjunction
  is compared directly with the ordinary pullback adjunction by `leftAdjointUniq`, including
  its unit compatibility. No additional section-normalized adjunction is used.

Removed direct proof dependencies `lem-weil-pbc-glue-sheaves-of-modules` and
`lem-weil-pbc-invertible-pullback-invertible`. Freeness of each pulled-back basis suffices;
there is no need to prove invertibility of the whole pullback first.

Replaced the direct proof dependency and removed the obsolete `tool_uses` entry for
`lem-weil-pbc-nonvanishing-section-trivializes` with the existing proved
`lem-sc-nonvanishing-iff-generates-at` and generating-locus API. Its statement dependency
and the original public re-export stay, because the mathematical statement still mentions
nonvanishing and the interface is preserved. No global withdrawal of that module is claimed.

No module is deleted. The named pruning is of this proof's dependencies; other parents or
upstream declarations may still need the corresponding modules. The unit's realized route
is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The earlier search correctly observed that
Mathlib has no single theorem for the full invertible-module construction. Nevertheless,
its structure-sheaf `fromOfGlobalSections` construction applies separately on every generating
open, and the source library already proves its invariance under homogeneous unit rescaling.
That API supplies the local construction and overlap compatibility directly.

The DAG's module-gluing and pullback-invertibility packages are stronger than this argument
needs. The source free-generator API supplies the precise gluing, pullback-basis, and local
isomorphism facts. The DAG copy and theorem proof docstring now record this route. No new
node is required: all new helpers are proved parts of the existing argument. The change record
`coord/changes/X3-sections-proj-private-proof-settings.md` documents the scoped proof commands
flagged by static preflight and the two unchanged consumers; no public statement or definition
is repaired.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
