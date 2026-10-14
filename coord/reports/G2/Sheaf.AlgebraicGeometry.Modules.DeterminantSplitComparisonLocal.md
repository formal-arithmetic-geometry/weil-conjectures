## What changed

The sandbox simplifies the proof of `determinant_split_comparison_restriction`
from a three-step calculation to `simpa only [hd] using hn W Z hW hZW y`.
All declaration signatures, definitions, visibility and imports are unchanged.
Both declarations already have complete proofs; the assignment's claim that this
module still contains `sorry` is stale. The existing local comparison proof uses
`determinant_split_linear_maps_exists` and
`determinant_split_linear_maps_locally_bijective`, then constructs linear
equivalences with `LinearEquiv.ofBijective`. The restriction theorem substitutes
`hd` into the naturality hypothesis `hn`.

## Proved and sorry left

Already proved (no holes closed in this delivery):
- `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_local`
  (`new-determinant-split-local`).
- `AlgebraicGeometry.Scheme.Modules.determinant_split_comparison_restriction`
  (`new-determinant-split-restriction`).

Holes closed by this delivery: none. Holes added: none. Sorries left in the
assigned module: none. This is validation of an already completed item, not new
proof progress. No new modules or statements.

## No longer needed

None. The local comparison uses both existing proof imports. No dependency or
unit route has been changed.

## Where the brief, the DAG or earlier work was wrong

The brief says the assigned module still contains `sorry`; the current module
contains none. Both nodes record a prior proof landing dated 2026-10-14. The
repair queue still lists the earlier false version of the restriction theorem,
but that version has already been replaced by the natural linear family
hypothesis `hn` and pointwise comparison hypothesis `hd`. The current proof
correctly uses both, so the unconstrained-lift counterexample no longer applies.
No signature, definition, visibility, or target was changed.

## Second reading by G2

1. **Interfaces: pass.** Compared the entire delivered module with the repository
   using `diff -u`: only the restriction proof body differs. Both existing
   declaration signatures are byte for byte unchanged. There are no definitions,
   new declarations, adapted modules, or change records in this delivery.
2. **Proofs: pass.** Compiled the delivered file with `lcompile.py` without errors
   or warnings (4.0 seconds). A scratch copy with `#print axioms` for both public
   theorems compiled (4.2 seconds); each uses exactly `propext`, `Classical.choice`
   and `Quot.sound`, with no `sorryAx`. The file contains no `sorry` or forbidden
   declaration mechanism. The local proof obtains a uniquely specified natural
   linear family, applies the existing local bijectivity theorem, and constructs
   equivalences with `LinearEquiv.ofBijective`; it introduces no arbitrary data
   from an unproved existence theorem. The restriction proof substitutes `hd`
   into the assumed naturality `hn` on both sides.
3. **Split statements: pass, none added.** No statement is split off and there
   are no residual holes to close. The restriction argument also works for
   zero ranks and empty opens because it is equality substitution alone; the
   local proof passes the same ranks and opens unchanged to the existing
   construction and bijectivity results.
4. **Route and pruning: pass.** Read both imported proof declarations. They
   supply precisely the linear construction and local bijectivity required;
   no duplicate helper or detour is introduced. Both plain proof imports are
   used; all public imports provide notions used in the signatures. No old
   proof dependency is dropped, so `## No longer needed` is complete. Read
   `dag/units/sk-thm-picard-rr.json`: its `realized` fields are presently empty;
   this delivery does not change them or bypass its determinant-additivity route.
5. **DAG: pass.** Read `new-determinant-split-local` and
   `new-determinant-split-restriction`. The first node's three proof steps and
   two proof dependencies match the unchanged construction. The second node
   records elementary substitution, no proof dependencies, and the repair's
   proof origin, exactly matching the simplified proof. No node update is needed.

Second reading changed only this report: corrected the inaccurate claim of no
Lean changes and documented the independent checks. Kept the valid proof
simplification. Holes closed: none; holes added: none; net progress: zero.
