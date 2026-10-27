## What changed

Replace the resolution-choice argument by the canonical adjunction-mate calculation. The
ordinary exchange is the mate of inverse open base change. Its composite with the support
inclusion is the ordinary direct-image square. The analogous derived mate carries the
right-derived unit to the termwise ordinary mate followed by the target derived unit.

Paste this identity with the right-derived direct-image composition unit identity and the
exact-derived open composition factorization. Monicity of the compactification inclusion
identifies the resulting ordinary sheaf map with the supplied map `a`. The assigned
module keeps its public statements and imports. Fully proved supporting calculations were
extracted to new modules after local irreducibility improvements: the single-file proof
checked but took 74 seconds. No shared definition is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Etale.exactCompactificationUnit_tower`. Added zero holes; zero remain in
this delivery. The three new supporting theorems are fully proved, so this is a proof rather
than a decomposition. `lcompile.py --all` passes for all four modules. The complete theorem was also checked
with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur. Temporary
profiling options and axiom-print commands have been removed.

## No longer needed

The proof does not choose resolutions or invoke
`AlgebraicGeometry.Etale.properOpenTowerDerivedUnit` from
`Sheaf.Paper.ProperOpenTowerDerivedUnit`. It also does not choose comparison families from
`Sheaf.Paper.UnboundedProperOpenInterchange` or
`Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`. The canonical exchange already has
an explicit mate definition, which suffices for this forward identity.

The unused planned dependencies are `lem-sfb-proper-open-tower-derived-unit`,
`lem-amb-unbounded-proper-open-interchange`, and
`lem-cbc-proper-support-sheaf-composition`. Their modules were not imported by the original
file, so no original import is removed. The exploratory direct proof import of
`Sheaf.CategoryTheory.MixedDerivedMateUnit` was replaced by the specialized exchange module;
that specialization remains a consumer of the generic mate theorem. No source-library declaration is removed and no
module is withdrawn. The original public imports remain necessary to state the result.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically usable but introduces resolution comparisons and
existential families that the forward unit identity does not need. The canonical mate
normalization follows formally from the derived adjunction unit and counit factorization
identities. The implementation uses that shorter argument.

## New nodes

- `lem-sfb-mixed-derived-mate-unit` in `Sheaf.CategoryTheory.MixedDerivedMateUnit` proves
  `AlgebraicGeometry.Etale.mixedDerivedMateUnit`, the normalization of a mixed derived mate.
- `lem-sfb-normalized-derived-unit-pasting` in
  `Sheaf.CategoryTheory.NormalizedDerivedUnitPasting` proves
  `AlgebraicGeometry.Etale.normalizedDerivedUnitPasting`, the generic pasting calculation.

A third fully proved node, `lem-sfb-open-exchange-derived-unit`, is in
`Sheaf.AlgebraicGeometry.OpenExchangeDerivedUnit` and proves
`AlgebraicGeometry.Etale.openExchangeDerivedUnit`. It specializes the generic mate identity
to the canonical open exchange.

All three are strictly parts of the tower argument and contain no holes. Their proofs use
naturality, adjunction factorization and homotopy localization, with no nonemptiness or
nonzero-object assumptions. Empty categories when admitted by the hypotheses, zero objects,
identity functors and the zero coefficient ring require no exceptions. The public signatures
of the new theorems contain no private definitions.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
