## What changed

Implemented the local elementary-generator route for `frameClass_independent`.
`GeneratingTupleChain` applies the existing local generator theorem inside the
common finite span. `GeneratingTupleSpreading` lifts the finite chain to actual
sections on an open neighbourhood, including unit inverses and endpoint equations.
`FrameProductOnSupport` gives the canonical coefficient transport and generic
composition/cancellation identities. `FrameProductElementary` composes the stated
unit/permutation and shear invariances on a fixed closed support. The item combines
these with product pullback and bottom-degree supported-Hom separation.

`frameClassOnPullback` names the same boundary product and support transport as before;
its signature and mathematical value are unchanged. Change record:
`coord/changes/G2-frame-single-transport.md`. No source-library declaration changes.

## Proved and sorry left

The original item has one hole, `WeilConjectures.PurityFiniteSetting.frameClass_independent`.
Its new proof is an assembly from the named elementary-chain, restriction and descent
results. All six auxiliary modules compiled; the item itself compiled cleanly in 35.7 seconds.
The delivery is a decomposition until the two comparison statements below
are proved; it does not claim a net decrease in holes.

Fully proved auxiliary results: `Module.generatingTupleChain`,
`AlgebraicGeometry.generatingTupleChain_neighbourhood`,
`AlgebraicGeometry.generatingTupleChain_of_idealSheaf_eq`,
`WeilConjectures.PurityFiniteSetting.framePresentationPullback`, the generic transport
identities in `FrameProductOnSupport`, and
`WeilConjectures.PurityFiniteSetting.frameProductOnSupport_elementary`.

Two holes are added, both genuinely separate comparison results:

- `WeilConjectures.PurityFiniteSetting.frameProductOnSupport_pullback`
  (`lem-pur-frame-product-pullback`): arbitrary tuples and arbitrary Cartesian squares,
  with no generator-independence or smoothness hypothesis.
- `WeilConjectures.PurityFiniteSetting.frameHom_zariski_separated`
  (`lem-pur-frame-hom-zariski-separated`): arbitrary bottom-degree supported Hom classes,
  with no equality or change of generating tuples assumed.

The item closes one upper hole and adds two lower holes. Existing operation-invariance
and cup-functoriality statements are used as recorded dependencies; their holes are
not newly introduced by this packet.

## No longer needed

The item's original direct proof imports of `Mathlib.AlgebraicGeometry.Sites.Etale`,
`Sheaf.RingTheory.LocalGeneratingTuples`, `Sheaf.AlgebraicGeometry.SupportLongExact`,
`Sheaf.Paper.SupportedAffineLineHomotopy`,
`Sheaf.Paper.RelativeSupportBottomDescent`, and
`Sheaf.Paper.SupportedCupFunctoriality` are replaced by the explicit assembly modules.
They remain needed transitively where the actual arguments use them. No existing
DAG module or source declaration is withdrawn or claimed globally unnecessary.

The local generator matrix witnesses are discarded; the proof uses only their
finite elementary operations. No matrix or Smith-form development is added.

## Where the brief, the DAG or earlier work was wrong

The plan correctly identifies the mathematical route, but its descent theorem is
stated in etale supported cohomology with the ring-characteristic twist, whereas
frame classes are concrete pro-etale supported Hom representatives with the diagonal
annihilator twist. The normalized Hom/site/exponent comparison is therefore a
separate required result, not an immediate application of the final descent clause.
Likewise, the general supported-cup laws require an induction identifying the actual
ordered boundary fold and its specified source/coefficient transports.

Edge cases checked: length zero, zero ideal or unit ideal, empty schemes/supports,
unit germs that only become units after shrinking, and tuples in an ambient module
that is not finite. The common span is finite; the ambient module need not be.

## New nodes

`lem-pur-generating-tuple-chain`: elementary chains inside the common finite span.

`lem-pur-generating-tuple-spreading`: finite chains spread from stalks to open schemes.

`lem-pur-frame-product-support`: actual support transport and its category identities.

`lem-pur-frame-product-elementary`: composition of unit/permutation/shear invariance.

`lem-pur-frame-product-pullback`: naturality of the concrete boundary fold.

`lem-pur-frame-hom-zariski-separated`: separation of arbitrary bottom supported Hom classes.

The unit's Kummer-boundary route is retained. The only change record is
`coord/changes/G2-frame-single-transport.md`.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
