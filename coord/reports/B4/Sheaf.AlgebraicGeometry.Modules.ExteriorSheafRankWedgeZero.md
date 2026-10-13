## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_rank_wedge_eq_zero` with its
original signature and docstring. Added two fully proved private helpers for partial
alternating-map vanishing and its concatenated-tuple specialization. Removed the
duplicate wedge-section naturality helper after the maintainer return. Instead,
`import all Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` makes its
existing private `exterior_section_map` available for direct reuse in the proof.
This import is proof-only; the existing module and helper visibility are unchanged. Added the
proof-only import `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` for
`sectionsLinearEquivOfIsoFree`. The second reading removed the unused proof-only
`WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` import.
Updated the item's DAG proof and dependencies to match this complete proof.

The finite locally free data supplies the covering sieve and invertible free presentation.
The existing proved finite-free section equivalence constructs the local basis. Partial
restriction of an alternating map to the selected r+1 positions and basis extensionality
prove zero; naturality and separatedness finish the sheaf argument. No nontriviality,
flatness, injectivity, or exactness hypothesis is added. Rank zero, empty opens/schemes,
zero rings, and the vacuous s=0 case are handled by the same proof.

Searches run: LeanFinder for alternating multilinear vanishing beyond rank found
repeated-entry vanishing and related alternating-map results; Loogle for
`AlternatingMap.domRestrict` found no declaration; grep for local basis existence found
no sheaf statement. Local source searches found `Module.Basis.ext_alternating`,
`MultilinearMap.domDomRestrict`, and the proved free section coordinates used here.

Recovered and checked the earlier attempt against the current module, the node, the
unit record, and the actual local-freeness and free-section interfaces. The original
public signature and docstring are unchanged.

Second-reading validation: the module compiled cleanly through lcompile.py (exit code 0,
5.1 seconds); the final scratch axiom check compiled cleanly in 5.5 seconds after removing
FreeGenerator. The required deliver3.py --no-push dry run printed OK: compilation and
preflight passed with the completed second reading. Review class: CODEX (node-file
changes and repair of a returned delivery).

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_rank_wedge_eq_zero`
(node `new-j1-exterior-sheaf-rank-wedge-zero`). No holes added or split off.
No sorry remains in the delivered module. Both remaining private helpers are proved; exterior_section_map is reused, not redeclared.
This is a proof, not a decomposition.

## No longer needed

Pruned the planned dependency `lem-weil-pbc-exterior-power-free-basis` from this
node's proof route: finite-basis extensionality of alternating maps suffices, with no
exterior-power basis construction. This dependency is a Mathlib leaf, with no dedicated
Sheaf module imported by the original item. Removed the duplicate local exterior_section_map declaration and the unused added proof-only
`WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator` import. No original imports were removed; both
public imports are required by the unchanged theorem statement. The existing proved ExteriorTensorLiftHomExt module is now needed for its
private naturality helper, and no globally unreachable module is asserted.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified a word-for-word duplicate private theorem
`exterior_section_map` in ExteriorTensorLiftHomExt. The earlier search and second
reading missed it. The repair removes that declaration and directly imports and uses
the existing theorem via Lean's `import all`; no generalization, signature change,
visibility change, or adaptation of another module is required. The previous second
reading applied to the returned version and has been removed pending a fresh reading.

No incorrect statement or forced adaptation was found. The planned exterior-power basis
argument was unnecessary; the direct alternating-map argument implements its underlying
multilinearity and repeated-entry argument. The unit's realized fields contain no node
that this local change bypasses. The source path in the node is absent from this local
checkout; the existing declaration's full proof description and node statement were used,
along with the actual Lean interfaces read in Mathlib and WeilConjectures.


## Second reading by B4

1. Interface: PASS. Read the complete repository/sandbox diff. The existing public
   theorem signature is byte-for-byte identical (also checked by direct substring
   comparison); its docstring, universes, public section, and both public imports are
   unchanged. There are no changed definitions, changed hypotheses, or adapted modules.
   The two added declarations are private proved helpers. The node changes only in
   `proof`, `proof_deps`, and `proof_origin`.

2. Proof and trust: PASS. The delivered module compiled cleanly through lcompile.py.
   In a scratch copy, `#print axioms` on `alternating_zero_on_large_image`,
   `alternating_append_image_zero`, and `exteriorSheaf_rank_wedge_eq_zero` each showed
   exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   Read both helpers: restriction freezes the unselected arguments; composition with
   f remains alternating; basis extensionality reduces zero to the impossibility of
   an injection from t into Fin r. The second helper selects the r castAdd positions
   and the disjoint natAdd position of j, using hc for its image witness.
   Read the sheaf proof: local generators supply an invertible presentation; the
   proved finite-free section equivalence supplies a genuine basis on V; naturality
   restricts hc and the tuple; separatedness on q.coversTop U finishes the equality.
   No forbidden declarations, sorry, or hollow definition occur in the module.
   Local choices occur inside a proof from the given locally free assumption, not
   as data definitions extracted from an unproved existence assertion.

3. Split statements and small cases: PASS. There are no split-off holes or new nodes.
   Both private helpers are fully proved and strictly intermediate. Checked rank zero
   (the selected set has at least one position and no injection into Fin 0), s=0
   (j : Fin 0 makes the assertion vacuous), zero rings, empty opens and the empty
   scheme. No domain, torsion-free, injectivity, nonempty-open, or positivity premise
   is needed. Independent LeanFinder search for vanishing with too many image arguments
   found repeated-entry vanishing and map_linearDependent; the latter requires a domain
   and torsion-free target and is inapplicable here. Source searches in Mathlib's
   Alternating/Basic.lean and Multilinear/Basic.lean confirmed ext_alternating and
   domDomRestrict. Repository searches confirmed the existing exterior_section_map
   in ExteriorTensorLiftHomExt; it is reused directly with import all, so the returned
   duplicate is gone. No shorter matching sheaf theorem was found.

4. Route and pruning: PASS after one import repair. Read the old proof_deps and
   dag/units/sk-thm-picard-rr.json: the only old dependency no longer used is
   lem-weil-pbc-exterior-power-free-basis, already listed under No longer needed.
   The realized statement and sole realized step lists are empty; no recorded unit
   realization is bypassed. The direct partial alternating-map argument replaces only
   the lower-level exterior-basis construction. Import-deletion scratch compilations
   showed Free is necessary (unknown sectionsLinearEquivOfIsoFree without it) and
   FreeGenerator is unnecessary (clean compilation without it), so I removed the
   latter. ExteriorTensorLiftHomExt supplies the actual naturality helper, whose proof
   was read; the other two imports supply the unchanged public signature.

5. DAG agreement: PASS. Read the node statement and its three revised proof steps:
   local free coordinates, partial alternating-map vanishing, then naturality and
   separatedness. They match the Lean argument and the union of their uses equals
   proof_deps. The ExteriorTensorLiftHomExt dependency is used for its existing
   private naturality helper, as the step explicitly says, rather than its public
   hom-ext conclusion. proof_origin describes this route. The original source file
   is not present in this checkout; this reading checked the unchanged statement
   against the node and its complete existing docstring proof, without claiming a
   new source-text review. No new node fields or change records are required.

Second-reading changes: removed the unused FreeGenerator proof import and corrected
its description in this report. The proof itself required no repair. One original
hole is closed, zero holes are added, and zero holes are split off.
