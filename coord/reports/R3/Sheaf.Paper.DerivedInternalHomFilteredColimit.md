## What changed

Prove the two remaining holes in `Sheaf.Paper.DerivedInternalHomFilteredColimit` using
its stated dependencies. The stated strict scalar-Hom identification supplies the
normalized tensor and chain-Hom isomorphisms and the unique scalar comparison. A
canonical single-complex comparison reconciles its termwise tensor convention with
the item's total tensor convention. The restriction square is checked on actual tensor
generators, using normalization and naturality of the resolution augmentation.

The quasi-isomorphism proof establishes exactness of filtered finite-free scalar
extension, preservation of K-injectives by its right adjoint, and cancellation of the
quasi-isomorphisms in this strict square. The final localization argument is unchanged.
All 13 existing public signatures and all existing public definition bodies are unchanged.

The new `Sheaf.Paper.InternalHomRepresentativeAPI` exposes ten declarations for existing
proved calculations. Its definitions are the actual canonical constructions; its eight
theorem proofs are complete. This hides private implementations behind an ordinary proof
import. No existing module besides the item changes, and no source-library file changes.

Validation: the new interface compiled cleanly in 17.0 seconds and the complete item
compiled cleanly in 42.3 seconds through `lcompile.py`, within the unchanged 60-second
file limit. No diagnostic options or temporary proof holes remain. Only the restriction
compatibility theorem uses a scoped elaboration-heartbeat budget; its local generator
argument requires conversions between the two strict chain models. The delivery tool
runs the final packet checks before pushing. Its first attempt timed out at the
unchanged file limit and pushed nothing. The pure-tensor interface now uses sequential
applications of its canonical maps, and the restriction proof uses direct isomorphism
cancellation; the revised interface and item passed a fresh two-file server request
(the service reused its compiled results).

## Proved and sorry left

The original holes are:

- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_restriction`.
- `WeilConjectures.SfbHomFilteredColimit.scalarComparison_quasiIso`.

The candidate contains complete proofs of both and zero remaining holes. The new API has
zero holes. No new unfinished theorem is introduced or split off. The proof reuses the
existing stated theorem
`SheafOfModules.StrictScalarHom.exists_scalarHomChainIdentification`, attached to
`lem-sfb-hom-scalar-chain-identification`; this delivery does not claim to prove that
separate dependency. Whole-closure progress is determined by the project's sorry ledger.

## No longer needed

No module is withdrawn. No original public import is removed. The private helpers
`extensionPresheafUnit_locallySurjective`, `extensionUnit_exists` and
`extensionGenerator_map` are unnecessary after reusing the strict chain model and are
removed from this Sheaf module. The remaining private construction has `no_expose`;
local reducibility attributes keep large canonical constructions behind their proved API.
These private implementation changes do not alter the 13 public signatures or data. The duplicate private
ordinary tensor and chain-Hom constructions of the earlier sandbox attempt are removed;
they are supplied by the stated strict scalar-Hom identification instead. The item uses
ordinary imports of the data, finite-free-stage and filtered-continuity modules through
the new proved interface, rather than private `import all` implementations.

The proof does not use `lem-pc-kflat-resolution`: its representative is already supplied.
It does not need `lem-sfb-hom-kflat-chain-transpose`,
`lem-sfb-hom-flat-evaluation-roof` or `lem-sfb-dc-hom-scalar-adjunction`: the strict
normalized restriction square, exactness and conservative restriction suffice.
`lem-sfb-ind-finite-free-scalar-model` is not used: the ordinary exactness needed here is
proved from the finite-free/filtered-colimit calculations, without constructing its more
general derived counit. The existing unit route remains unchanged.

The generic derived tensor-Hom infrastructure `lem-sc-derived-hom-tensor-total`,
`lem-pur-hom-complex-global-homotopy`, `lem-pur-hom-kflat-into-kinjective`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-pur-quasi-iso-cone-acyclic`, and
`lem-weil-pbc-site-derived-tensor-descent` is not used. Independent-universe Hom invariance
uses `lem-pur-rhom-well-defined-universes`, rather than `lem-pur-rhom-well-defined`.
The existing derived scalar extension and K-flat definitions remain statement infrastructure.
The obsolete top-level `tool_uses` approvals removed are `lem-pc-kflat-resolution`,
`lem-pur-rhom-well-defined`, `lem-sc-derived-hom-tensor-total`,
`lem-pur-hom-complex-global-homotopy`, `lem-pur-quasi-iso-cone-acyclic`,
`lem-weil-pbc-site-derived-tensor-descent`, `lem-pur-hom-kflat-into-kinjective`, and
`lem-pur-derived-change-of-rings`; remaining approvals keep their original order.
Pruning here describes this proof's direct dependencies; it does not withdraw upstream
public declarations or claim that these nodes have no other consumers.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt duplicated the strict scalar-Hom identification already
available as a stated dependency. Reusing it gives a substantially shorter construction.
The arbitrary-coefficient chain identification is separate from the exactness argument:
only the latter needs the filtered finite-free hypothesis. No statement dispute,
weakened hypothesis, target change, hollow definition or source-library repair is needed.

A diagnostic invocation of `leanindex.sorry_count` wrote its automatic cache under
shared `local/`; no shared source file changed. Subsequent static checks use only the
non-writing parser functions. This incidental cache write did not alter the delivery.

The first server preflight requested the separate LeanSearch search category: Loogle
and LeanFinder count as the same category. An actual LeanSearch query has now been run
and recorded alongside Loogle, LeanFinder and the source grep. No mathematics changed.

## New nodes

`lem-sfb-strict-representative-interface` records the ten proved interface declarations,
including their actual pure tensors and the canonical single-complex isomorphism. It
adds no mathematical obligation or unfinished proof. The change record is
`coord/changes/R3-internal-hom-representative-interface.md`.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
