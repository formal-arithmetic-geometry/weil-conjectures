## What changed

Proved `AlgebraicGeometry.Scheme.sfbNormalizedLocalRestriction_iso` by comparing ordinary
module functors first, then using their exact derived functors. Its statement and original
public imports are preserved. Added two ordinary comparison modules and their DAG nodes.

The immersion comparison constructs its target coefficient isomorphism from the normalized
ring adjunction unit. Operation graph compatibility supplies the ring map and the module
adjunction. Uniqueness of left adjoints compares the scalar extensions and the actual
specified module pullback. The slice comparison constructs the transport functor by
continuous module pushforward along `Over.post` for AsSmall, with its explicit scalar map.

The main proof uses the invertibility and computation lemmas already proved in
`AdicStratumCompletionUnit`, compares the derived functors by cancellation of localization,
and removes every chosen localization representative through its canonical isomorphism.
It applies the transported exact slice functor to the given local isomorphism.

All added imports in the original item are private proof imports. The new modules
publicly import the interfaces needed by their statements. No existing declaration
signature or public import changes, and no consumers need adaptation. No data are chosen in definitions from
unproved mere existence statements.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.sfbNormalizedLocalRestriction_iso`
(`lem-sfb-normalized-local-restriction-iso`).

The new comparison declarations are
`AlgebraicGeometry.Scheme.sfbOrdinaryImmersionNormalization`
(`lem-sfb-ordinary-immersion-normalization`) and
`AlgebraicGeometry.Scheme.sfbOrdinarySliceNormalization`
(`lem-sfb-ordinary-slice-normalization`).

There are no written `sorry` terms in the delivery. No split-off holes are added.
The server compiled all three modules together successfully: the ordinary immersion
comparison in 45.3 seconds, the ordinary slice comparison in 53.0 seconds, and the
assigned module in 19.0 seconds. Earlier isolated checks also compiled the ordinary
comparisons in 21.6 and 30.1 seconds. Development profiler options and traces were
removed before delivery. The delivery tool records its independent validation.

## No longer needed

No original public import was removed, and no module is withdrawn.
The planned direct use of `lem-sp-proetale-algebraic-inverse-image`
(`Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage`) is unnecessary here: the
unit-normalized ring presentation and the ordinary module adjunction compare the actual
module functor directly. That node is removed from this node's proof dependencies.

The other original dependencies are retained directly or through the new ordinary
comparisons. The immersion limit-preservation result is used through
`AdicStratumCompletionUnit`'s proved computation lemmas. The algebraic inverse-image
structure is still used in the ordinary immersion comparison. No claim is made that any
of these source modules is globally unused.

## Where the brief, the DAG or earlier work was wrong

The original proof plan required matching completed coefficient maps by their finite
projections. For this theorem's isomorphism conclusion, a target coefficient isomorphism
constructed from the supplied algebraic inverse-image data suffices. This avoids a
separate coherence proof between the canonical target completion comparison and the
transported original inverse-image ring. It changes no statement and assumes no local
completeness, perfectness, points or nonempty slice.

The source arguments were checked in `sites-modules.tex` at
`lemma-pullback-module`, `lemma-adjoint-push-pull-modules` and
`definition-localize-ringed-site`. The new ordinary statements allow zero coefficient
rings and empty slices. Their constructions and adjunction arguments apply in those
cases without a faithful restriction assumption.

## New nodes

`lem-sfb-ordinary-immersion-normalization` records the comparison for arbitrary ordinary
coefficient sheaves and an invertible scalar map. It contains neither a completion nor a
derived category nor a slice. Its Lean module is
`Sheaf.Paper.SfbOrdinaryImmersionNormalization`.

`lem-sfb-ordinary-slice-normalization` records exact ordinary module transport to the model
slice and its compatibility with scalar restriction. It contains no immersion pullback,
completion or derived category. Its Lean module is
`Sheaf.Paper.SfbOrdinarySliceNormalization`.

The new lemmas serve the existing integral-models unit route. No unit statement or realized
step is bypassed. The blueprint and Mathlib searches found transport ingredients but no
exact comparison theorem. No change record is needed because no existing public interface
changes. The proved generic ringed-site adjunction and exact-restriction APIs are used as
tools; their modules were read, and no open theorem from another unit is assumed here.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
