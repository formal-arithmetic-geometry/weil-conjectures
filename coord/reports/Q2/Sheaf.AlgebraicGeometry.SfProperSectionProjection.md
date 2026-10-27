## What changed

Replaced the proof hole in `SfProperSectionProjection.properSectionProjectionUnit` by the
complete section specialization, tensor-unit cancellation and canonical-symmetry argument.
The two existing definitions, the target statement and its docstring are unchanged. The
proof uses the specified compact-support compositor and identity comparison throughout.

Added `SfProperProjectionComposition` and `SfIdentityProjectionNormalization`. These isolate
two separate coherence laws: composition for arbitrary proper maps and normalization for
one identity map. Neither mentions a proper section, its tensor isomorphism or the desired
unit-insertion equation. Each has its own node, source and full proof in words.

Functor-category calculations are proved first for abstract categories and isomorphisms,
then specialized using explicit equalities of the defining isomorphisms. This avoids
unfolding large concrete derived-functor definitions during the tensor-unit calculation.
No existing public import, statement, definition or source-library module was changed.

## Proved and sorry left

Closed the original body hole of
`AlgebraicGeometry.Etale.SupportedTrace.properSectionProjectionUnit` by a complete proof
from the two named intermediate statements. This is a decomposition, not an unconditional
proof of the target: 1 original hole closed, 2 new holes added, 0 holes left in the item
module. The new holes are:

- `AlgebraicGeometry.Etale.SupportedTrace.properProjectionCompositionOfEq`, node
  `lem-sf-proper-projection-composition`.
- `AlgebraicGeometry.Etale.SupportedTrace.identityProjectionNormalization`, node
  `lem-sf-identity-projection-normalization`.

The item proves the section projection square from those two independent laws, computes
the inverse section tensor isomorphism from its actual factors, proves the unordered unit
square by naturality and inverse cancellation, and then obtains the ordered equation by
canonical symmetry and the right-unitor braiding identity. Every private helper is proved.
There are no postponed data constructions or holes inside definitions.

The three intended modules compiled together in dependency order: the identity normalization
module in 35.3 seconds, composition in 37.9 seconds, and the item in 49.5 seconds. The
complete argument with provisional copies of the two intermediate statements also compiled
in 20.7 seconds. The tensor-isomorphism inverse calculation alone compiled in 5.5 seconds,
and its axiom check returned only `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

No original import was removed and no existing module was withdrawn. The proof no longer
uses the abstract ringed-topos presentation dependencies
`lem-sfb-ringed-projection-tensor-composition` (`Sheaf.Paper.RingedProjectionTensorComposition`)
or `lem-sfb-ringed-derived-monoidal-comparisons`
(`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`). Their normalization is replaced by
the two concrete coherence obligations above. This removes these edges from this node;
it does not claim that those modules are globally unused. The blueprint unit route is
preserved: composition, identity specialization, unit insertion and symmetry cancellation
are all still performed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no signature was weakened. Existing source declarations
supply the native projection composition and proper-coincidence squares, but they do not
immediately have the normalized functor presentations of the section data. Attempts to
convert their concrete dependent types exceeded the file limit. In particular, the
native composition type uses the symmetric-category-induced coefficient braiding in
left-derived-functor parameters, while the section pullback abbreviations use the
`ModuleCat` braiding instance. An inferred-type wrapper around the native theorem itself
compiled in 5.3 seconds with only the permitted axioms; this confirms that the native
result is available. The remaining work is the canonical normalization, rather than a
missing source theorem. No compiler time limit was increased.

## New nodes

`lem-sf-proper-projection-composition`: the forward projection square for two arbitrary
proper morphisms and a specified equal composite. Its proof plan identifies the native
compactification compositor, cancels inverse comparisons, and transports along equality.
It is needed before the proper-section specialization and involves no unit or section.

`lem-sf-identity-projection-normalization`: identity projection normalized by the precise
pullback and compact-support direct-image identity comparisons. Its proof plan transports
the ordinary adjunction calculation through proper coincidence. It involves neither a
section nor a pair of nonidentity morphisms. No change records are required: all other
existing module interfaces and node statements are unchanged.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
