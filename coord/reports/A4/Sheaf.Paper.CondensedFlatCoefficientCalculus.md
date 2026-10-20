## What changed

Restored the quarantined `Sheaf.Paper.CondensedFlatCoefficientCalculus` module for its
assigned synchronization repair. Preserved the complete archived proofs and verbatim
signatures of its four public theorems. The repair makes substantive changes: the old
source's private finite-basis helpers are absent after synchronization, so the module
now contains their explicit, fully proved private constructions. The copied Map,
RingIso and continuous-function coordinate constructions come from the quarantined
Compatibility extra. They construct inverse coordinate/basis maps and transport them
through sheafification and inverse image; no witness is chosen from an unproved
existence assertion.

Removed the unrelated Compatibility-extra public import and the obsolete `import all`
of the adopted Compatibility source. Six private cache lemmas omit their now-unused
`MonoidalPreadditive C` parameter, eliminating the new compiler warnings. Existing
coherence and exact-derived-functor proofs remain intact. No adopted source file,
coefficient definition, comparison map, target statement or public theorem type changes.

Updated the existing node's first two proof steps and proof_origin to identify the
restored private constructions accurately. The unit route and dependencies are retained.
The change record is
`coord/changes/A4-condensed-flat-calculus-quarantine-restoration.md`; it records the
archived consumer closure and the effect of pruning the public import.

The item compiles cleanly with no errors or warnings. All four archived theorem
signatures were compared byte-for-byte with the restored source. A fresh consumer
repeats all four archived types and applies the corresponding restored declarations;
this checks the public interface independently of private proof scopes. The artifact-producing
item compile took 44.2 seconds and the independent consumer took 18.4 seconds, both
without warnings. `#print axioms` lists only the three standard axioms and inherited
`sorryAx` for each theorem, consistent with the existing unresolved dependencies.

## Proved and sorry left

This is a zero-hole synchronization repair, not a new hole closure. Original item
holes: 0. Holes closed: 0. Holes added: 0. Split-offs: 0. Item holes remaining: 0.
No declaration in the delivered Lean module contains `sorry`.

The following existing proofs are retained and compile after the repair, all attached
to `lem-weil-pbc-condensed-flat-coefficient-calculus`:

- `AlgebraicGeometry.ProEtale.condensedFiniteCoefficientCalculus`.
- `AlgebraicGeometry.ProEtale.condensedAlgClCoefficientCalculus`.
- `AlgebraicGeometry.ProEtale.condensedCoefficientCoherence`.
- `AlgebraicGeometry.ProEtale.condensedCoefficientTensorColimit`.

All restored private helpers are constructive and fully proved. The exactness
arguments still use the existing source instances
`AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`
and
`AlgebraicGeometry.ProEtale.CondensedRing.preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl`.
Those existing source obligations contain `sorry`; this packet neither adds nor
claims to close them.

## No longer needed

Removed the public import
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
Its current bounded-pushforward theorem is unrelated to these four assertions. Its
quarantined finite-basis constructions, which the item actually needs, have been
restored privately in this module instead. The extra module is not withdrawn: other
consumers may still need its theorem.

Removed the proof-only `import all`
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
The adopted module is already publicly available through the coefficient-comparison
import, and no private helper from that module is now used. The source's public
flatness instances remain needed.

No mathematical node or module is withdrawn, and none of the item's declared proof
dependencies is pruned. In particular, the shared finite-model proof API remains used
for the exact-derived-composition transport and shift lemmas. No new module is added.

## Where the brief, the DAG or earlier work was wrong

The source is absent from live `lean/` because it was quarantined, not because it was
withdrawn. Its rework row and archived attachment are preserved. Once the missing
Compatibility-extra import was removed, the compiler exposed unknown constants
`Profinite.continuousBasisSheafIso` and `Mod.mapFreeRestrictedRegularIso`: the DAG's
old description of reusing these private helpers from the adopted source was stale.
The repaired proof restores the same constructive argument under the item module.

The live downstream query has no importers while the item is quarantined. Reading
quarantined parents reveals three direct proof-only consumers:
`Sheaf.Paper.CoefficientFiniteDescentHom`,
`Sheaf.Paper.GeneralCondensedWeilRealization`, and
`Sheaf.Paper.CompactSupportCondensedRealization`. They retain the identical theorem
API. Their full overlaid archived import closure is listed in the change record;
none is modified, removed or claimed unnecessary. In particular the Hom-descent
parent continues to use the existing second coherence clause.

Mathlib searches using Loogle (`"finiteFree"`) and LeanFinder (continuous maps into
a finite-dimensional p-adic space as a free condensed module) returned only general
free/condensed-module constructions. Direct source searches found no current copy of
the missing finite-basis helpers. Their archived complete construction supplies the
short repair, without adding any intermediate mathematical obligation.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
