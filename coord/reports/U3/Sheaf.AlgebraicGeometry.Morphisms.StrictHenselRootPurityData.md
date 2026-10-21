## What changed

Retire `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData`, the zero-hole
item listed by `coord/retire-items.tsv`, in favor of its retained upstream twin.
The existing purity-data node now attaches to
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData` with the
verbatim signature of its already proved theorem. The old small-colimit theorem
is replaced at its sole direct consumer, `StrictHenselRootFiniteEtaleModel`, by a
fully proved private `small_root_purity_data`.

The private proof constructs the canonical strict-henselization and root-algebra
isomorphisms, checks their structure maps and punctured opens, applies the
upstream theorem, and transports its divisor, finite model, etale restrictions,
generic-point neighbourhood and cover comparison, including the projection
identity. The consumer's public theorem and public imports stay verbatim. Its
unit branch, purity assembly, flatness and density/surjectivity proofs stay
unchanged. No source-library file or target statement changes.

Update the existing consumer node to record that transport. The change record is
`coord/changes/U3-retire-strict-hensel-root-purity-data.md`.

## Proved and sorry left

The starting item has 0 local holes. This delivery completes its listed retirement:
0 of 0 holes closed, 0 holes added, 0 split off. No sorry remains in any delivered
Lean file. The retained declaration is
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data`
(node `lem-sbc-strict-hensel-root-purity-data`). The new private transport and the
preserved public
`AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model`
(node `lem-sbc-strict-hensel-root-finite-etale-model`) have complete proofs.

Validation: `lcompile.py --all` compiled the adapted finite-etale-model consumer
(7.0 s) and its unchanged downstream `RegularDivisorStrictHenselRootSection`
(2.8 s), with no warnings. Both import-direction checks accept the new proof
imports. The original and adapted consumer have identical public signatures,
public imports and docstrings. The delivery tool performs the axiom probe and
full preflight before pushing.

## No longer needed

Withdraw `Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData`, listed in
`deleted.txt`. Its only direct consumer replaces that private import by the
upstream twin and directly imports the colimit-comparison module needed for
transport. The retired copy's duplicated root-quotient construction and
small-to-full tame-normalization and regular-quotient transport helpers disappear.
No further module is withdrawn.

The reattached purity-data node no longer directly uses
`lem-weil-pbc-small-strict-henselization-ind-etale`,
`lem-weil-pbc-flat-colimit-presentation-same-universe`,
`lem-weil-pbc-etale-algebra-flat`, or
`lem-weil-pbc-strict-henselization-small-closed-fiber-comparison`; the retained
upstream proof uses `lem-sbc-affine-strict-henselization-structural-flat` instead.
The small-model flatness and comparison nodes remain needed by the consumer.
The removed direct definition edges are `def-pc-fibre-product`,
`def-weil-etale-morphism`, `def-weil-finite-integral-morphism`,
`def-weil-pbc-strict-henselization-limit`, and
`def-weil-pbc-strict-henselization-structural-map`; these definitions remain in
the statement dependencies. No mathematical dependency is claimed globally
unnecessary. In particular the regular-divisor quotient and tame-normalization
nodes remain used by the retained upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed obligation; the current item is already
proved and is explicitly a retirement assignment. Its upstream twin uses
`strictHenselization` and `strictLocalizationToBase`; the copy uses
`strictHenselizationRing` and `strictHenselizationStructuralMap`. A bare import
swap would not adapt the consumer. The canonical transport supplies the actual
proof needed to retire the copy, without claiming nonexistent holes closed.

Read the whole module and upstream twin, their regular-quotient and tame-model
dependencies, the existing node declarations, the parent node, the unit record
and current blueprint unit, and Stacks `pione.tex`,
`lemma-abhyankar-one-divisor` and `lemma-extend-tame-covering-normal`. The unit's
root-extension, tame-normalization and purity route remains. The nonunit and
positive group-order hypotheses are unchanged. The isomorphism transport also
works for group order one and preserves empty cover sources; it adds no
Noetherianity, nonemptiness or connectedness assumption.

Searches actually run with `msearch.py`: LeanFinder for transport of a finite
etale normalization model with regular Cartier divisor (eight normalization and
standard-etale API hits, no complete transport theorem); Loogle for
`AdjoinRoot.mapRingEquiv` (three precise API hits); grep for restriction,
Cartier-kernel and preimage-isomorphism identities (16 hits). Direct `rg` found
the existing upstream purity-data theorem and the existing canonical comparison.
No new node or unproved intermediate result is required.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
