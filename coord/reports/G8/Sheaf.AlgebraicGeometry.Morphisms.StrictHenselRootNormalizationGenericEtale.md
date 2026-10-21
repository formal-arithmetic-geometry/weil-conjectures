## What changed

Complete the zero-hole retirement assigned by `coord/retire-items.tsv`, row 2787,
under the human-approved hand-off `coord/changes/retire-sheaf-twins-20261020.md`.
Withdraw `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale`
and its sole direct consumer
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization` in favor of
both retained upstream twins. Their existing mathematical nodes now attach to
those upstream theorems, with the full affine-neighbourhood strict henselization.

Adapt the first retained small-colimit consumer,
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData`, by replacing its
private tame-normalization import and theorem application. A fully proved private
`small_root_tame_normalization` helper transports the upstream finite model along
the canonical strict-henselization comparison and the explicit induced
`AdjoinRoot.mapRingEquiv`. It checks the structural map, punctured open, Cartier
centre, generic point, finite map, etale restrictions, cover comparison and
projection identity. The public purity-data theorem, all of its public imports,
and its existing divisor construction remain verbatim. This helper constructs
isomorphisms from proved APIs; it introduces no data from an unproved existence.

The source library under `lean/WeilConjectures/` and every target statement are
unchanged. The corresponding three node copies record the actual retained proof
route and canonical transport. The change record is
`coord/changes/G8-retire-strict-hensel-root-normalization-generic-etale.md`.

## Proved and sorry left

The starting item contains 0 local holes. This is a retirement, not another
claimed proof of its already complete theorem. Holes closed: 0 of 0. Holes added:
0. Split off: 0. Holes remaining in delivered Lean files: 0.

The retained upstream declarations are
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_generic_etale`
(node `lem-sbc-strict-hensel-root-normalization-generic-etale`) and
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_tame_normalization`
(node `lem-sbc-strict-hensel-root-tame-normalization`). The preserved consumer
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data`
(node `lem-sbc-strict-hensel-root-purity-data`) and its new private transport helper
have complete proofs. No new statement with `sorry` is introduced.

Validation: `lcompile.py --all` compiled the adapted purity-data module (7.9 s)
and both unchanged downstream consumers, `StrictHenselRootFiniteEtaleModel`
(5.5 s) and `RegularDivisorStrictHenselRootSection` (3.6 s), with no warnings.
The complete importer overlay contains no remaining reference to either withdrawn
module; `import_direction.py may` accepts the upstream proof import. The DAG
overlay has no cycle and all referenced nodes exist. Public signature and public
import comparisons are identical to the original consumer.

## No longer needed

Withdraw these two duplicate modules, listed in `deleted.txt`:

- `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale`.
- `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization`.

The purity-data module no longer imports the Sheaf tame-normalization copy; it
imports `WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization`.
The deleted tame-normalization copy no longer imports either the generic-etaleness
copy or `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite`.
The latter module remains available for its separate retirement assignment; no
claim is made that its mathematical node is unnecessary. The upstream tame
normalization proof still uses both finiteness and generic-etaleness nodes, and
these dependency edges are preserved.

The generic-etaleness node's removed direct proof edges are
`def-weil-pbc-strict-henselization-limit`,
`def-weil-pbc-strict-henselization-structural-map`,
`lem-weil-pbc-etale-algebra-flat`,
`lem-weil-pbc-flat-colimit-presentation-same-universe`,
`lem-weil-pbc-small-strict-henselization-ind-etale`, and
`lem-weil-pbc-strict-henselization-small-closed-fiber-comparison`.
The definitions remain among its statement dependencies. The small-model
flatness argument is replaced by the retained upstream theorem attached to
`lem-sbc-affine-strict-henselization-structural-flat`. Its public
statement uses the full affine-neighbourhood model. The canonical comparison
remains needed by the purity-data transport. No mathematical claim or unit step
is dropped. The only incoming DAG references are the tame-normalization parent
and the purity-data parent, respectively; both nodes remain attached to the
corresponding retained declarations and the changed consumer uses the latter.

## Where the brief, the DAG or earlier work was wrong

The generic worker brief describes a deep holed proof, but the current item has
already been proved and is explicitly a retirement item. Its current theorem
compiled before changes. The upstream twin has the same mathematical statement,
but it uses `strictHenselization` and `strictLocalizationToBase`, whereas the copy
uses `strictHenselizationRing` and `strictHenselizationStructuralMap`. These are
canonically isomorphic constructions, not definitionally equal types. A bare
import swap does not adapt the consumer. The private transport supplies that
missing argument and retains the source-library boundary.

The unit `sk-prop-input-spreading` and its source proof were read. Neither retired
node realizes a unit statement or step. The trait argument still proceeds through
the group-order root, tame finite normalization, generic etaleness and purity.
Stacks `pione.tex`, lemmas `lemma-abhyankar-one-divisor` and
`lemma-extend-tame-covering-normal`, explicitly permit the isomorphic base change
used here. The field/nonunit and n=1 cases require no new assumptions. The transport
preserves empty source schemes whenever the original hypotheses allow them.

Searches actually run with `msearch.py`: LeanFinder for transport of etaleness of
relative normalization under a base isomorphism; Loogle for
`AlgebraicGeometry.Scheme.Hom.normalizationPullback`; grep for restriction and
isomorphism identities. Direct searches found the retained upstream generic and
tame theorems, `AdjoinRoot.mapRingEquiv`, `Scheme.Hom.preimageIso`,
`morphismRestrictEq`, and `pullback.map`. A separate normalization-commutation
proof is unnecessary because the downstream result asks for existence of a
finite model: the existing upstream model itself transports by isomorphism.

The compile server intermittently returned exit code 124 (“no answer from the
compile server”); these were retried while continuing proof and metadata work.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
