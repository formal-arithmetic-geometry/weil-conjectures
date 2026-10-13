## What changed

Proved `AlgebraicGeometry.universalFirstOrderThickening_open_restriction_core` in
`Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestrictionCore` without changing its
signature or visibility. The existing proved theorem
`AlgebraicGeometry.universalFirstOrderThickening_open_pieces`, clause (1), already provides
all restricted data and universality. The proof reorders its witnesses, reverses one
compatibility equality and extracts `iV ≫ hV' = hV` from the definition of universality.
Replaced the redundant proof import of `Sheaf.AlgebraicGeometry.Thickening` with the
non-public import of `Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`. The public
import and all existing declaration signatures are unchanged. Updated the core node's
proof, proof_deps and proof_origin to record this route. A single-file lcompile check passed
without warnings; the dry run also checks the declaration's axioms.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.universalFirstOrderThickening_open_restriction_core`
(node `lem-weil-pbc-universal-thickening-open-restriction-core`).
No sorry remains in the item, and no new holes or declarations were added. This is a proof,
not a decomposition: the imported open-pieces theorem already has a complete proof.

## No longer needed

Removed direct import `Sheaf.AlgebraicGeometry.Thickening`; it remains available through
`UniversalFirstOrderThickening`, so this does not prune that module from the target closure.
The core no longer directly needs the planned proof dependencies
`lem-weil-pbc-morphism-factors-through-open-subscheme`,
`lem-weil-pbc-formally-unramified-open-restriction`,
`def-sbc-first-order-thickening`, `lem-weil-pbc-thickening-open-restriction`, and
`def-weil-scheme-over-base`. The restriction and factorization work is already proved
inside the open-pieces module; those supporting nodes are not claimed globally redundant.
Formal unramifiedness is unnecessary here and its restriction lemma is unused by this route.
The only direct proof dependencies now are the open-pieces node and the universal-thickening
definition. No whole module is claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The core plan overlooked the existing open-pieces theorem, whose second conjunction is
precisely the geometric content required here. Its formally-unramified-open-restriction
step was unnecessary: the core assumes universality and no formally-unramified hypothesis.
No mathematical statement or definition was changed. The unit's realized statement and
steps are preserved; this replacement operates below the unit level. The import-direction
check confirmed that the open-pieces module does not reach the core. LeanFinder and Loogle
searches ran through msearch, and repository searches found the existing proof.

## Second reading by R4

1. Interface: PASS. Read the entire delivered module and compared it with the
   repository using `diff -u`. The only changes are the non-public proof import
   and replacement of `sorry` by the two-line witness extraction. The complete
   theorem signature, universes, visibility, docstring and public import are
   byte-for-byte unchanged; no definition or target is changed. There are no
   additional delivered Lean modules or change records.
2. Proof: PASS. Recompiled the delivered file through `lcompile.py`, without
   errors or warnings. A scratch copy under `scratchpad/` with explicit
   `#print axioms` checks reports exactly `propext`, `Classical.choice` and
   `Quot.sound` for both the core theorem and the imported open-pieces theorem.
   No `sorryAx` occurs. Inspected the delivered source for forbidden declarations
   and trust bypasses: none, and no sorry or definition is present. The witnesses
   come from a proved theorem within a proposition, not data selected from an
   unproved existence theorem.
3. Split statements: PASS (none). No declaration or node is added and no hole is
   split off. Read the complete open-pieces statement and proof and the definition
   of `IsUniversalFirstOrderThickening`. Its second conjunction supplies every
   witness under exactly H and hVU; hhV.symm supplies the reversed structure-map
   equation, and HV.2.1 supplies iV ≫ hV' = hV. No formal-unramifiedness or affine
   assumption is used. Empty V, empty U (with hVU), and full opens are covered by
   the same universally quantified existing theorem, without extra restrictions.
4. Route and pruning: PASS. The existing open-pieces theorem is the direct proved
   route; there is no construction to repeat or lower hole to move. Searched the
   upstream WeilConjectures source and the local algebraic-geometry modules for
   universal-thickening declarations and read the parent open-restriction module.
   The parent still uses this core and the separate conormal theorem. Both imports
   in the delivered module are needed: UniversalFirstOrderThickening provides the
   public signature, and OpenPieces is used only in the proof and is non-public.
   Compared old proof_deps with the report: all five removed dependencies are
   listed. Read dag/units/sk-thm-p1.json, including its realized statement and all
   four realized step lists. Neither this core nor open-pieces is a realized unit
   step, and both are in sk-thm-p1; this replacement changes only a supporting
   node route. No realized node or whole module is claimed pruned.
5. DAG and source: PASS. The node diff changes only proof, proof_deps and
   proof_origin. Its cited open-pieces node labels the restriction clause (1),
   which is the Lean expression `.2.1`; the other cited node is exactly the
   definition used for HV.2.1. The recorded Lean signature matches the file.
   Read the general restriction argument in
   [Stacks Tag 04F3](https://stacks.math.columbia.edu/tag/04F3), since the local
   literature TeX is absent: universality over X restricts to V over U by
   factoring test extensions through V'. This is the argument already proved
   by open-pieces, and requires no additional formal-unramifiedness hypothesis
   once H is supplied. The node proof is consistent with this source and Lean.

Changes by the second reader: appended this independent reading and recorded the
explicit axiom checks. No Lean or node repair was needed. One original hole is
closed, zero holes are added, and no whole module is pruned.
