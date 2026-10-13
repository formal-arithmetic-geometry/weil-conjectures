## What changed

Verified upstream review #1428 against the current landed repair. The core already states
flat descent for a finite morphism tested by a flat base change meeting the chosen point.
Simplified `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`:
algebraize the actual stalk maps directly, removing five ring/map aliases and two redundant
hypothesis aliases, including the shadowing of the scheme projection by a ring map.
The statement, visibility, docstrings, imports and proof route remain unchanged.
The module compiles without warnings. The delivery axiom probe checks its public declarations.

## Proved and sorry left

The sole theorem `AlgebraicGeometry.Scheme.stalk_normalization_depth_two_section_flat_core`
remains completely proved. Holes closed: zero (the repository already has no sorry).
Holes added: zero. Sorries left in this delivery: none. No decomposition or net proof
progress is claimed. This is verification and simplification of an already landed repair.

## No longer needed

None. No import, node or module is pruned. The proof still uses
`lem-weil-pbc-flat-algebra-faithfully-flat-descent` and
`lem-sbc-finite-flat-target-locus`. The DAG proof and stored Lean signature already match
this argument, so no node update is necessary.

## Where the brief, the DAG or earlier work was wrong

The repair entry quotes a superseded statement. The landed record
`coord/changes/stalk-normalization-depth-two-section-flat-core.md` (2026-10-13)
already replaced the false normalization assertion by the true flat-test core.
Adding a rational-point or dense-fibre assumption to this general descent theorem would
be inappropriate: there is no normalization, smooth family or punctured open in its
signature. Instead `[Flat (pullback.snd p t)]` is an explicit required hypothesis.
Depth two alone does not provide it, so the cone counterexample cannot satisfy all the
current hypotheses. The normalization caller
`GaloisCover.stalk_normalization_depth_two_section_flat` has the rational-point hypothesis
`hZ` and obtains its flat pullback through the formal splitting test. The other caller
`flat_fibre_of_punctured_local_purity` obtains flatness by identifying its local base change
with a finite etale extension. Neither caller needs adaptation, and no target changes.
Empty E is vacuous; an empty T cannot supply b; the flat test need only meet x.
The unit route is preserved: this remains its final descent-and-openness calculation.

The previous delivery was identical to the repository and was rejected for changing no
item module. This attempt makes the explicit proof simplification described above and
replaces the obsolete report. It does not invent another statement change or add a hole.

## Second reading by C3

1. Compared the delivered module with the repository version. The theorem signature and
all existing declarations are byte-for-byte unchanged; only the proof body was simplified.
Verdict: pass.

2. Compiled the module and the sandbox import closure with `lcompile.py`; the axiom probe
reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`,
`unsafe`, `opaque`, `implemented_by`, or `extern` declarations. Verdict: pass.

3. The only theorem is already proved, so no statements were split off. The existing node
is the exact theorem used by the callers, and its statement remains true and unchanged;
the repository search found no duplicate declaration. Verdict: pass.

4. The proof follows the node route: pullback lifting, faithful-flat stalk descent, then
the finite flat target locus and stalk criterion. The direct algebraization removes only
redundant aliases and does not bypass the unit route. Verdict: pass.

5. The DAG proof dependencies remain exactly the two declarations used by the proof, and
no import or node is unused. The unit's realized route is preserved. Verdict: pass.

Changed the proof by algebraizing the actual stalk maps directly, removing five ring/map
aliases and two redundant hypothesis aliases. No statement, import, node, or dependency
was changed.
