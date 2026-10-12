## What changed

Proved `RingHom.IsRegular.comp_of_fiber_noetherian` with its signature unchanged.
Added two fully proved modules: `Sheaf.RingTheory.RegularCompositionExtendedFiber`
and `Sheaf.RingTheory.RegularMapAscent`. Their statements isolate the intermediate
fibre calculation and globalize the existing local regularity criterion, respectively.
Updated the composition node's proof and dependencies and added nodes for these two tools.
All added imports in the original module are proof-only. No definitions or existing
statements changed, and no change record is needed.

The proof constructs the tensor algebra maps and equivalences explicitly. It proves
flat composition, flatness of the intermediate map by two `Flat.lTensor` applications,
and Noetherianity of the extended target fibre by module-finite base change. The fibre
calculation uses the essentially finite-type residue-field instance, 0381 and tensor
cancellation. Local ascent uses the prime–fibre correspondence, `algEquivAux₂` and 031E.
The different universes of B and C are handled by the existing universe-polymorphic
0381 statement, without changing the geometric-regularity definition.

## Proved and sorry left

Closed one original hole: `RingHom.IsRegular.comp_of_fiber_noetherian`
(node `lem-weil-pbc-regular-composition`). Added zero holes; split off zero sorries.

Also fully proved `RingHom.IsRegular.extendedFiber_regular`
(node `lem-weil-pbc-regular-composition-extended-fiber`) and
`RingHom.isRegularRing_of_flat_of_regular_fibers`
(node `lem-weil-pbc-regular-map-ascent`), together with the private, proved
`regular_fibre_baseChange` helper. No `sorry` occurs in any delivered module.

The proof uses two existing stage-3 criteria: `Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular`
(node `lem-weil-pbc-geometrically-regular-finitely-generated-extensions`) and
`IsRegularLocalRing.of_flat_of_regular_closedFiber`
(node `lem-weil-pbc-flat-over-regular-with-regular-fibre`). These are unchanged and
not delivered. At second reading both repository sources have proved bodies, while
local `#print axioms` still reports inherited `sorryAx` through their dependency
closure. This is a proof from the existing named criteria, not a claim that all
its transitive dependencies are sorry-free.

All three modules compile together through `lcompile.py --all`. Checks include
unequal universe parameters, the canonical tensor-map algebra structure, and the
closed-fibre ideal equality. Zero target rings and absent prime ideals are covered
by the proofs; the extended-fibre lemma needs neither regularity of A → B nor
Noetherianity of the composite fibre nor purely inseparability of K.

## No longer needed

Removed the proof import `Sheaf.RingTheory.RegularBaseChange` and the dependency
`lem-weil-pbc-regular-base-change` (07C1). The direct tensor-fibre calculation replaces
its two proposed applications. No claim is made that the module is globally unreachable:
other targets or users may still import it.

Removed the direct import `Sheaf.RingTheory.RegularLocalOfFlatWithRegularClosedFiber`
from the original module, but retained it in `RegularMapAscent`: its node is still needed.
`GeometricallyRegularFieldExtension` remains needed directly and in the new fibre module.

The original node no longer needs `lem-weil-pbc-finite-type-algebra-noetherian`:
module-finite base change and `lem-weil-pbc-finite-algebra-noetherian` suffice.
It no longer needs `lem-weil-pbc-surjective-image-noetherian` for an independent
Noetherianity argument on the intermediate fibres, since 0381 gives their regularity
including Noetherianity. The old finite-type residue-field node is no longer a direct
dependency of composition, but remains a dependency of the new fibre node, using its
recorded essentially finite-type Mathlib generalization. Localization, flat base change,
flat composition and the definition of regular rings remain needed.

No unit realization or unit-level route is bypassed: the unit's realized declarations
are unchanged, and the 0381 and 031E steps of the regular composition argument remain.

## Where the brief, the DAG or earlier work was wrong

The plan's appeal to the trivial purely inseparable extension at one fixed universe
cannot directly handle distinct universes for B and C. The existing 0381 declaration
already permits arbitrary universes and resolves this without any interface changes.
The residue-field finite-generation instance also works for essentially finite-type
maps, so explicit localization followed by two invocations of 07C1 is unnecessary.

The local literature checkout lacks the cited TeX files on this machine. Read the
primary sources online: https://stacks.math.columbia.edu/tag/07QI,
https://stacks.math.columbia.edu/tag/031E and https://stacks.math.columbia.edu/tag/0381.
LeanSearch returned HTTP Internal Server Error for both helper searches; recorded
unavailability honestly. LeanFinder, Loogle, Mathlib source grep and library searches
were available. No tool failure blocks this delivery.

## New nodes

`lem-weil-pbc-regular-map-ascent` records the proved flat ascent theorem in
`Sheaf.RingTheory.RegularMapAscent`. It applies the existing 031E theorem at each
prime, with the closed fibre identified using existing Mathlib equivalences.

`lem-weil-pbc-regular-composition-extended-fiber` records the proved fibre statement
in `Sheaf.RingTheory.RegularCompositionExtendedFiber`. Its private helper treats
essentially finite-type base change; the public result constructs the required
D-algebra equivalence and transports the helper's regularity conclusion.
Both nodes inherit chapter and unit from the original item and have complete
proof steps, source citations, Lean records and three kinds of search. Neither
adds a sorry or chooses data from an unproved existence statement.


## Second reading by D3

1. PASS: compared all three delivered module paths with the repository. Only
   RegularComposition existed there. Its declaration signature is byte for byte
   identical, with the same universes, algebra tower, hypotheses and conclusion.
   No definition changed; no change record is required. The two other modules
   introduce proved intermediate statements, not replacements of the target.
   Restored the original declaration docstring verbatim; the updated route is
   recorded in the node and this report.
2. PASS: compiled the three files together in import order through lcompile.py,
   without errors or warnings. Scratch-copy #print axioms checks for all three
   public theorems returned exactly propext, Classical.choice, Quot.sound and
   inherited sorryAx. No delivered source contains sorry, axiom, unsafe, opaque,
   implemented_by or extern. The private base-change helper is fully proved.
   The prime obtained in ascent is constructed using the explicit Mathlib
   equivalence and its left inverse, not selected from an unproved existence
   theorem. All tensor maps and equivalences are explicit constructions.
3. PASS: no split-off sorry statements exist. Read both new theorem signatures,
   proofs, docstrings and nodes; both are strictly intermediate parts of the
   composition argument. Checked arbitrary prime contractions, the trivial
   field extension, zero target and zero intermediate ring, and independent
   universe levels. The Noetherian target assumption in ascent is necessary;
   the finite field extension ensures essential finite type in the fibre lemma.
   Independent searches used a different LeanFinder wording, Loogle IsRegularRing,
   and Mathlib grep for flat/tensor regularity and essential finite type, plus
   searches of Sheaf and the adopted source library. No exact existing result
   was found. RegularityRkGoesUp requires a bounded Serre condition and is not
   a direct replacement. Verified sources 07QI, 0381 and 031E online.
4. PASS: the target opens its original hole and composes existing flatness,
   geometric regularity, finite base change and the two fully proved glue lemmas.
   The public imports supply symbols in signatures; other added imports supply
   proof tools. No shorter direct theorem was found. No longer needed accounts
   for all five removed old direct proof dependencies: regular-base-change,
   finite-type-algebra-noetherian, surjective-image-noetherian, finite-type
   residue-field-extension-finitely-generated (retained through extended-fiber),
   and flat-over-regular-with-regular-fibre (retained through ascent).
   Read dag/units/sk-thm-p1.json: all realized statement and step nodes are
   unchanged; this is below the unit level and retains the 0381/031E argument.
5. PASS: the existing node changes only proof, proof_deps and proof_origin.
   Every node's proof_deps is exactly the union of its proof-step uses. The new
   nodes match their public Lean signatures, have source and blueprint records,
   chapter/unit, creation metadata and recorded searches. The essentially
   finite-type residue-field generalization is already recorded by its Mathlib
   node. No node or unit statement is weakened.

Second reading changed the original theorem docstring back to the repository
version and corrected the report's stale assertion that the two directly used
criteria still have sorry bodies. No mathematical proof or signature needed
repair. One original hole closed, zero holes added, zero sorry statements split
off; the two new public lemmas and their private helper are proved.
