## What changed

Proved `AlgebraicGeometry.Scheme.Modules.pullback_free_coordinates_naturality` in
`Sheaf.AlgebraicGeometry.Modules.PullbackFreeCoordinatesNaturality`, preserving its
signature and docstring. Added the proof-only import
`WeilConjectures.AlgebraicGeometry.Modules.HomSection` for `unit_hom_ext`.
Two fully proved private helpers identify the structure-sheaf pullback unit with
`appTop` and prove compatibility of the structure-sheaf comparison with composition.
The main proof projects first, applies composition naturality to `α ≫ freeπ i`,
and then applies unit naturality. Updated the existing node's proof plan to this route.
No definitions, public signatures, or public imports changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.pullback_free_coordinates_naturality`
(node `new-sbc-pullback-free-coordinates-naturality`).
Both private helpers `unit_pullbackΓ` and `unit_comp` are proved without holes.
No holes remain and no holes were added. This is a proof, not a decomposition.
The empty rank has no `i : Fin 0`; the categorical argument makes no nonempty-scheme
or nonzero-ring assumption.

## No longer needed

None. Both original public imports are required by the statement; the sole added
proof import supplies `unit_hom_ext`. No existing dependency node or module is pruned.
The explicit local pure-tensor computation in the earlier plan is replaced by the
proved structure-sheaf comparison and the existing free-projection API.

## Where the brief, the DAG or earlier work was wrong

The proof plan is mathematically correct, but a local pure-tensor computation is
unnecessary. Projecting first reduces the free comparison to a structure-sheaf
comparison, determined by its value on the twice-pulled-back global section 1.
The unit record has no realized step assigned to this node; the unit route is preserved.
At the initial compile, the published compiled library lacked
`Sheaf.AlgebraicGeometry.Modules.PullbackSectionFactorization.olean` despite its
source being in the repository. Scratch testing of the exact unchanged construction
compiled the complete argument in 23.8 seconds; `#print axioms` returned exactly
`propext`, `Classical.choice`, and `Quot.sound`. Final validation must use the
actual imported module. Two delivery dry runs failed with the same missing-object
error, including on the server's published build. The library refresh advanced to
03:09:45 local time while the required object remained absent. This is a missing
published dependency, not a timeout or proof failure. No dependency was copied into
the deliverable, no build or tool was changed, and nothing was pushed.

## Second reading by G4

1. I compared the delivered module with the repository version. The public theorem
   signature and existing declarations are unchanged; only a proof-only import,
   private helpers, and the proof body were added.
2. `lcompile.py` compiles the module and the axiom probe. There are no `sorry`,
   `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. The
   target uses only `propext`, `Classical.choice`, and `Quot.sound`.
3. The two private helpers are real reductions: one identifies the structure-sheaf
   unit on sections with `appTop`, and the other proves its composition compatibility
   by `unit_hom_ext`. No split-off theorem or duplicate library theorem was added.
4. The categorical route keeps the unit route and is shorter than the old pure-tensor
   plan. Both public imports remain required; `HomSection` is proof-only and supplies
   `unit_hom_ext`. No dependency node is pruned.
5. The existing node is proved exactly as stated, including rank zero, zero rings,
   and empty schemes. The node proof and dependencies match the implemented route.

I changed only this report section; no Lean source or node statement was altered.
