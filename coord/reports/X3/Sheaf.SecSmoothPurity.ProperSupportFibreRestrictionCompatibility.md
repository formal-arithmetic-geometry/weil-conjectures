## What changed

Proved `AlgebraicGeometry.Etale.properSupport_fibre_restriction_compatibility` in
`Sheaf.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility`, with its statement unchanged.
The proof obtains the two normalized geometric-stalk restrictions from
`properSupport_geometricStalk`, constructs the canonical Cartesian fibre and coefficient
transport, proves that transport preserves proper support, and restricts it to the two support
submodules. The composition-unit calculation gives the ambient representative formula. The
adjunct unit equation, germ naturality, and the stalk colimit universal property give the final
commutative square after cancelling the submodule inclusion.

All auxiliary constructions and proofs are private to the item module. Local irreducibility
keeps the canonical transport and pullback constructions from expanding during rewriting;
their projection and normalization equations provide the proof interface. Restriction of a
module isomorphism to matching submodules is a generic private construction with a proved
subtype equation, avoiding repeated elaboration of fibre pullback terms. Added proof imports of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`,
`Sheaf.AlgebraicGeometry.ProperSupportSectionLocality`, and
`Sheaf.AlgebraicGeometry.EtaleModuleSectionClosedSupport`. Updated the existing node's proof,
proof dependencies, and proof origin to describe the direct ModuleCat argument. No public
statement or definition was changed; no consumer adaptation is needed. The public-import
pruning is documented in `coord/changes/proper-support-fibre-restriction-imports.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.properSupport_fibre_restriction_compatibility`.
Added 0 holes; split off 0 statements; 0 sorries remain in the delivered Lean file.
Every private helper is proved, and every private definition has a concrete construction.
The required single-file `lcompile.py` check passed without errors or warnings. The final
proof uses the default transparency settings, with explicit pullback projection rewrites and
a proved normalization equation for the private terminal-section pullback isomorphism.
The delivery dry run passed compilation, the appended axiom probe, and project preflight
(dry-run commit `41122f35eb`).
The unchanged direct importer `Sheaf.AlgebraicGeometry.ProperSupportExchangeRange` also
compiled against the overlay (7.4 seconds); no consumer was edited.
The original theorem statement was compared verbatim with the shared source and is identical.

## No longer needed

Removed the direct imports:

- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already exposed by the required imports).

Removed these planned proof dependencies and their obsolete top-level `tool_uses` approvals:

- `lem-weil-pbc-inverse-image-stalk-germ`: the ModuleCat germ equation is proved directly
  from the point-comap unit and uniqueness of left adjoints.
- `prop-weil-pbc-inverse-image-modules-exact`: no exactness or reduction to abelian sheaves
  is needed in this calculation.
- `lem-weil-pbc-sets-etale-inverse-image-composition-units`: replaced by the existing
  `upperStarComp_hom_app_unit_app` directly for ModuleCat coefficients.
- `lem-weil-pbc-etale-inverse-image-algebraic-structures`: no passage through underlying
  set or abelian sheaves is needed.

The proper-support section-map module stays because its concrete section-map definitions occur
in the statement and calculation. Its existence theorem is not reapplied: the given `hα` is used.
The normalized proper-support geometric-stalk theorem, fibre-product construction, inverse-image
adjunction, and geometric-stalk colimit remain necessary. No entire module is withdrawn or
claimed to be globally unreachable; the removed modules may remain transitively required by
other proofs. The blueprint unit `sk-prop-sf-cbc` has no realized statement or proof steps bypassed
by this change.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient reductions were unnecessary because the library already proves the
composition-unit coherence for ModuleCat-valued sheaves. The support-preservation check implicit
in the planned fibre identification is made explicit using zero geometric germs and properness
under scheme isomorphisms. No disputed statement, target change, or definition repair was needed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
