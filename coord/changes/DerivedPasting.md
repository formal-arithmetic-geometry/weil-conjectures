# Private localization pasting helpers

## Reason

The two varying-ring alpha pasting proofs use private, proved helpers for generic
exact functors and localization. Preflight detects their sections, variables and
local attributes as a context change. The private scopes supply the proof only;
every existing public signature and public definition is identical.

## Old

The file had only `mate_whisker` as a private helper. The ordinary and derived
pasting declarations followed directly in the original scheme-variable context.
`alpha_vertical` and `alpha_horizontal` had proof `by sorry`.

## New

Three generic variable sections, `DerivedMaps`, `DerivedPasting` and
`DerivedHorizontal`, enclose only private definitions and proved private lemmas.
Each section ends before the existing public declarations. Local irreducibility
attributes prevent repeated unfolding of derived localization constructions
while rewriting their factorization equations. Both derived alpha pasting proofs
specialize the generic localization lemmas to the ordinary module arrows.

No target, public definition, source-library module, public import, global
attribute or instance was changed.

## Users

The only direct importer is
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`. It needs no adaptation:
`properOpenPasting` and every other existing declaration retain their signatures.
The imported proof APIs now depend on two fewer local holes. No consumer module
was edited, and there are no forced adaptations.

## Status

landed 20261020T211836-L-3509627 2026-10-20 (merge of deliver/U2/Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting)
in the same file, without profiling options, compiler-limit changes or warnings.
