## What changed

Proved `AlgebraicGeometry.exists_disjoint_closed_immersion_refinement` without changing its signature or public imports. Added one proved private helper for restricting a closed immersion to a smaller base open. Updated the item's DAG proof to match the implemented ordering: the original finite open pieces are already closed by proper-over-separated, so their overlap images can be deleted before performing a single base change.

## Proved and sorry left

Proved `AlgebraicGeometry.exists_disjoint_closed_immersion_refinement`, the module's sole original sorry, and the private helper `closedImmersion_restrict_of_le`. Holes closed: `AlgebraicGeometry.exists_disjoint_closed_immersion_refinement` (1). Holes added: none (0). No sorry remains in this module; no new modules, nodes or postponed theorems are added. The one-point shrinking theorem is used through its existing proved declaration. Local compilation is clean (about three seconds). The theorem still transitively uses the existing hole `AlgebraicGeometry.exists_isClosedImmersion_restrict_of_fiber` through the one-point theorem; it is not yet an axiom-free target-closure proof.

## No longer needed

None. All four original imports are used and retained. All original proof-dependency nodes remain required, including the open-fibre-product and proper-over-separated Mathlib leaves. The proof avoids a preliminary base change and a second base change; it makes one simultaneous restriction instead.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or unusable dependency was found. The original plan can be shortened because finite pieces have proper inclusions into the separated ambient pullback even before the one-point shrinking. The theorem's docstring remains unchanged; the DAG records the implemented ordering.

Searches: LeanFinder returned coproduct/disjoint-affine-open results, not this shrinking theorem; Loogle found `IsProper.of_comp`; the launcher grep query found no matching disjoint-refinement lemma. Repository searches found the one-point theorem and the existing pullback-pasting pattern in `FiniteUnramifiedEtaleLocalReduction`.

Edge cases: if the dependent index set is empty (including n = 0 or all m i = 0), all finite infima used in B are top, the family assertions are vacuous, and exhaustion follows by applying the original exhaustion hypothesis to the image point in the original pullback. Diagonal pairs are explicitly excluded from deletion, which also handles the singleton-family case. No new statement needs an edge-case check.


## Second reading by N2

1. Compared the sole delivered Lean module against the repository with `diff` and
   checked the existing theorem signature byte for byte with a script: identical.
   Its separatedness, finite/unramified pieces, unique marked fibre points, purely
   inseparable residue extensions, injectivity and exhaustion hypotheses are intact;
   all four conclusion clauses are intact. No definition or public import changed.
   Verdict: pass.
2. Compiled the module locally with `lcompile.py`, cleanly. A scratch copy with
   `#print axioms` for the theorem and private helper shows only `propext`,
   `Classical.choice`, `Quot.sound`, and (for the main theorem) inherited `sorryAx`.
   The existing source of that hole is `exists_isClosedImmersion_restrict_of_fiber`,
   used by the proved one-point theorem. No delivered proof contains `sorry`, and
   no forbidden declaration or attribute occurs. Verdict: pass with that existing
   dependency explicitly recorded, not a claim that the full closure is proved.
3. No statement is split off and no hole is added. Read the private restriction
   helper: pullback cancellation identifies the further restriction square, and
   base-change stability proves the claim. For empty index families the finite
   infima are top and exhaustion is inherited; for a singleton, the diagonal
   overlap is excluded. For distinct indices the unique-fibre and injectivity
   hypotheses exclude their overlap over u. Verdict: pass.
4. Read the proof downward, its one-point dependency and the upstream split
   neighbourhood results. The latter require a finite ambient map/geometric
   neighbourhood and do not replace this theorem for a merely separated ambient
   map. A fresh Loogle search for `morphismRestrict, IsClosedImmersion` finds the
   ordinary restriction instance, which does not directly apply to the further
   restriction helper's input; repository/Mathlib searches found no direct
   replacement. All four imports are needed (the public ones for the signature,
   the private ones for properness and one-point shrinking). No old proof dependency
   is removed. Read `dag/units/sk-thm-p1.json` and its `realized` list: this local
   shrinking argument replaces no unit statement or step. Verdict: pass.
5. Compared the node with the repository: only `proof`, `proof_deps`, and
   `proof_origin` differ. The dependency set is unchanged and equals the union of
   the steps' uses. Each step matches the implemented properness, overlap deletion,
   restriction/pullback and exhaustion argument. No new node is needed. Verdict: pass.

Changes made by the second reader: added an explanatory docstring to the proved
private restriction helper; clarified in the DAG that overlap images are deleted
only for distinct indices and that the closed immersion being restricted is the
one over the chosen neighbourhood; explicitly counted one hole closed and zero
added, and documented the inherited open dependency in this report. No proof
body, existing signature, or import changed.
