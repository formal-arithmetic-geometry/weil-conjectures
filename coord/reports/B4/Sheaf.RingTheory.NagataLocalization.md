## What changed

Filled the existing proof of `isNagataRing_localization`, with its signature and public imports
unchanged. A local argument for an arbitrary submonoid proves Noetherianity, contracts each prime,
constructs its quotient as a localization, and applies `localization_isN1_isN2`. The canonical
quotient-localization equivalence is a finite injective algebra map, so the already-proved
`isN2_of_finite_domain_extension` transports the N-2 property to the quotient and its chosen fraction
field. The same local argument gives the prime and principal cases.

Removed the first worker's `NagataLocalizationCore.lean` and proposed core node from the delivery:
they merely repackaged the general assertion as another hole. Added proof-only imports of
`Sheaf.RingTheory.N2AscendsFiniteDomainExtension` and
`Mathlib.RingTheory.Localization.Submodule`; removed the redundant direct proof import of
`Sheaf.RingTheory.JapaneseDomain`. Updated only the existing node's proof, proof_deps and proof_origin.
No statement, definition, public import, new declaration or change record is delivered.

## Proved and sorry left

Closed the existing hole in `isNagataRing_localization` (node
`lem-weil-pbc-nagata-localization`): one of one holes in the item's module. Added zero holes and split
off zero statements. Removed the proposed hole `isNagataRing_localization_core` before delivery.
This is a reduction to existing dependencies, not a decomposition into new holes.

No `sorry` remains in any delivered Lean file. The existing imported theorem
`localization_isN1_isN2` (node `lem-weil-pbc-localization-n2-domain`) still has its original `sorry`;
this delivery does not close it. Consequently `#print axioms isNagataRing_localization` reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The imported
`isN2_of_finite_domain_extension` reports only the three standard axioms. Thus the item's local
hole is closed, but its import closure is not yet axiom-free. Net local holes closed: one; no new
holes enter the target closure, and no library module is pruned. The maintainer's pinned ledger
remains the authority for global progress figures.

## No longer needed

Removed the redundant direct import `Sheaf.RingTheory.JapaneseDomain`, already publicly imported by
`NagataRing`. The module itself remains in the import closure. All seven original proof-dependency
nodes are still used: the Nagata and Japanese definitions, localization Noetherianity,
quotient-localization identification, N-2 localization, and the AtPrime/Away definitions. No original
proof-dependency node or reachable library module was pruned. The proposed new core module and node
were removed from this delivery; they were not part of the repository baseline.

## Where the brief, the DAG or earlier work was wrong

The first worker's claim that no Lean declarations implement the Noetherian and quotient steps was
incorrect: Mathlib supplies `IsLocalization.isPrime_iff_isPrime_disjoint`,
`IsLocalization.map_under`, `IsLocalization.of_surjective`, `IsLocalization.algEquiv`, and the
Noetherian instances. The only substantial open localization result needed here already has the
usable statement `localization_isN1_isN2`. Moving the general localization assertion to a new core
was not a genuine smaller split. The repaired proof follows the original plan and uses the existing
finite-domain N-2 ascent theorem solely to implement transport through a ring equivalence.

## Second reading by B4

1. Compared the complete delivered module with the repository using `diff`. The sole existing
   theorem signature is byte-for-byte unchanged, as are all definitions (none are declared here),
   public imports, module header and exposure. Changes affect only the proof and plain imports.
   No interface change or change record is needed. Verdict: pass after repair.
2. Compiled the repaired module locally through `lcompile.py`, with no errors or warnings. Inspected
   the entire proof: no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by` or `extern`. A scratch
   copy with `#print axioms` confirms only the standard axioms and the documented inherited
   `sorryAx`; the N-2 finite-domain ascent theorem is axiom-free apart from the standard axioms.
   The algebra structure extracted from `localization_isN1_isN2` is determined by its fraction
   formula on all `mk'` elements, which generate the localization; no arbitrary existence witness
   supplies undetermined data. Verdict: pass, with the original imported hole explicitly retained.
3. Rejected and removed the proposed core statement: its arbitrary-localization assertion recovers
   all special cases, so it just moves the item's mathematical content. No new statements or nodes
   survive. Independently searched with LeanFinder for "Japanese condition localization fraction
   fields ring equivalence", inspected the relevant Mathlib localization sources and searched
   `lean/Sheaf` and `lean/WeilConjectures` for Nagata/Japanese/N-2 results. Reused the existing N-2
   localization and finite-ascent declarations. Checked the zero ring, submonoids containing zero,
   `f = 0`, and the identity localization: Noetherianity still localizes; a prime of the localization
   forces its contracted prime to avoid the submonoid. Thus the domain/N-2 argument is used only
   when its zero-avoidance premise holds, and the zero-ring case has no primes. Verdict: pass.
4. Read the proof from the target downward. The repaired proof now performs the Noetherian and
   prime-quotient steps instead of assuming a core copy of the target. All added imports are plain
   proof imports. A removal test showed the direct `Localization.Ideal` import redundant and the
   `Localization.Submodule` import necessary for both Noetherian localization instances; retained
   only the latter. Read `dag/units/sk-thm-p1.json`: this item and its dependencies are below the
   unit's realized statements/steps, all of which stay untouched. All original dependencies remain
   used and the pruning report lists the sole redundant original import. Verdict: pass.
5. Checked the node against the repaired proof: its unchanged statement, lean record, chapter and
   unit still match the theorem; its steps and proof_deps now name the original route plus
   `lem-weil-pbc-n2-ascends-finite-domain-extension` for equivalence transport and
   `lem-weil-pbc-finite-algebra-noetherian` for quotient Noetherianity. No new node remains. Read the
   sources [Stacks 032U](https://stacks.math.columbia.edu/tag/032U),
   [032G](https://stacks.math.columbia.edu/tag/032G), and
   [032I](https://stacks.math.columbia.edu/tag/032I); they justify the localization argument and the
   finite-extension transport. Verdict: pass.

Second reading changed: removed the restated core and its hole; implemented the original reduction
using existing declarations; minimized proof imports; corrected the node and progress report.
