## What changed

Proved `WeilConjectures.SemilinearSections.systemBlockRepetition` using the actual
first-endpoint and repetition functors. The first-endpoint site functor is left
adjoint to the block-index site functor. Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` transfers that adjunction to module
sheaves after checking both coefficient equations. Pushforward composition gives
the evaluation comparison, identity on sections. The existing exactness theorem
and `Adjunction.preservesKInjectiveComplexes` complete the package, including its
specified adjunct formula.

Four proved private helpers handle module-object transport, the section formula
for an adjunct, the coefficient equations for the transported adjunction, and
identity-on-sections evaluation comparisons. The coefficient definitions are
locally irreducible only in the proof of the package theorem.

After abstracting these coefficient transports, server compiles of the combined
module still took 79.2 and 81.8 seconds, over the single-file limit. Extracted the
existing, fully proved generic derived-comparison section into
`Sheaf.Paper.SystemBlockDerivedComparison`, publicly re-exported by the item.
All eight moved public signatures, their definitions and proofs are retained.
Proof-local irreducibility of the complex and coefficient comparisons avoids
unnecessary unfolding without changing their public reducibility.
The support module explicitly publicly imports the derived-adjunction module
needed by its statement. The item retains its existing public imports. Its three
old private proof imports
move with the derived section initially; the geometric section-normalization
import is then removed by proving its two elementary mate identities locally.
The ordinary composition transport is
abstracted into a proved generic private helper.

The ordinary block definitions and coherence lemmas are likewise extracted into
`Sheaf.Paper.SystemBlockConstructions`, publicly re-exported by the item. Their
public signatures, definition bodies and global attributes remain unchanged.
The existing private exactness proof stays with the item. This second extraction
is needed because the first split and further generic coefficient abstraction
still left the item at the 60-second limit.

The item node now describes the proved adjunction construction and cites the
extracted comparison node. The unit route, statement and statement dependencies
are unchanged. No source-library module is changed.

Validation: all three packet files compiled within the single-file limit
(constructions 38.3 s, derived comparisons 4.3 s, item 33.9 s in the first clean
three-file run). A second seven-file run accepted all three plus every unchanged
direct importer: `Sheaf.SixFunctors.NormalizedOpenSections`,
`Sheaf.Paper.EtaleCofinalSupportRealization`,
`Sheaf.Paper.EtaleCofinalSupportComposition` and
`Sheaf.Paper.EtaleSystemCofinalData`. No adaptation was required. All four consumer
copies were byte-identical to the shared sources and were removed from the
packet. All 42 original explicitly named public declarations remain present.
After replacing the cyclic section-normalization citation with local proved
mate identities, all three final files compiled again: constructions 5.2 s,
derived comparisons 37.0 s, and item 37.9 s. This proof-only correction preserves
the public interface checked by the four consumer compiles. Both new nodes have
no dependency path back to the item. Only the two named original obligations
contain `sorry`; the support files are hole-free. The delivery audit checks the
final packet and its axioms.

The previous corrected delivery attempt passed server preflight. Its Git push failed with
`remote: error: unable to create temporary file: No space left on device` and
`remote unpack failed: unpack-objects abnormal exit`. That attempt delivered nothing.
The retry also passed server preflight, but its push was rejected with
`remote unpack failed: unable to create temporary object directory` and
`unpacker error`. Neither attempt delivered. The verified packet remains in the
sandbox for retry after the server object-storage failure is repaired.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.SemilinearSections.systemBlockRepetition`
(node `lem-pur-system-block-repetition`). This is a proof, with no split-off holes.

The two original holes left in the item, both attached to
`lem-pur-system-block-repetition`, are:

- `WeilConjectures.SemilinearSections.systemBlockGeometry`.
- `WeilConjectures.SemilinearSections.blockRepeat_extensionByZero`.

Added holes: zero. The two support modules move existing proved declarations
and definitions
and add no mathematical assertion or `sorry`.

## No longer needed

The explicit dependency `lem-weil-pbc-adjunction-of-natural-bijection` and its
obsolete top-level `tool_uses` entry are removed: the proof directly constructs the
site unit and counit and applies Mathlib's module-sheaf pushforward adjunction.
Its separate natural-bijection argument is unnecessary here.

The original node's direct proof dependencies on `def-sfb-right-derived-functor`,
`lem-sf-kinjective-derived-map-computation` and
`lem-weil-pbc-exact-square-derived-counit` are replaced by the extracted comparison
node. The obsolete top-level `tool_uses` entries for the first and third are also
removed. Right-derived normalization remains needed inside the proved support
module; none of these whole modules is claimed pruned from the library. Existing
historical review records are retained.

Removed from the item the private imports of
`WeilConjectures.CategoryTheory.DerivedExactCompositionComparison`,
`Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison` and
`Sheaf.Paper.SectionDerivedPushpullNormalization`. The first two remain used
privately by the extracted support module. The third is removed from the packet
entirely: its only two used private lemmas are elementary mate identities, now
fully proved locally with their original proofs.

No whole Lean module is pruned. The other categorical and semilinear dependencies
remain needed by the existing comparison proofs or the two remaining geometric
and open-localization obligations. No upstream declaration or unit step is
removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was required. The first two DAG steps admit a shorter
implementation using existing adjunction machinery, rather than manually
constructing a natural bijection on systems and transporting each homotopy.

The combined file did not meet the compile-time limit even after abstracting
coefficient transports. The extracted support sections preserve the existing
argument and public interface while distributing proof checking across files.

The first preflight found a DAG cycle from citing the whole geometric
section-normalization node merely for two private elementary mate identities.
Those identities are now proved locally; that node is no longer a dependency.
The remaining generic derived-comparison dependencies do not reach the item.

## New nodes

`lem-pur-system-block-derived-comparisons` attaches the already proved generic
normalization, derived-adjunction, coefficient-cube, composition and identity
comparisons to `Sheaf.Paper.SystemBlockDerivedComparison`. Its eight declarations
are moved verbatim from the item, with their existing proofs and no new holes.
The source is the existing universal right-derived comparison argument (Stacks
070I, 070Y and 09T5). LeanFinder, Loogle, grep and LeanSearch queries checked the
existing constructions before retaining those proofs. The extraction keeps the
same unit route. The change record is
`coord/changes/V2-system-block-derived-comparison-extraction.md`.

`lem-pur-system-block-constructions` attaches the existing finite-block maps,
endpoint and repetition definitions, package type and ordinary composition,
identity and scalar-restriction coherence to
`Sheaf.Paper.SystemBlockConstructions`. All moved definitions, signatures and
global attributes are retained. Its ordinary section proofs remain complete;
coefficient composition now uses the proved generic transport helper. No hole
is added. The existing block-reindexing Mathlib searches and source proof are
recorded with this extracted node. The same change record above documents both
extractions.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
