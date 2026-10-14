## What changed

Proved `AlgebraicGeometry.affineDerivedPushforwardSheafReverse_unit` in
`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafReverseUnit`, without changing
its statement, visibility, docstring, or imports. The proof follows the existing
DAG plan: choose a K-injective resolution, transport quasi-coherent cohomology,
use the canonical comparison's K-injective characterization, combine the
naturality squares, and cancel pushforward of homology of the resolution
isomorphism. It does not assume termwise pushforward preserves this
quasi-isomorphism.

Seven proved private helpers express localization compatibility, cancellation
of the derived unit on K-injectives, naturality of the unit and the explicit
homology comparison, functoriality of a square, and cancellation of a square.
Keeping these calculations generic avoids expensive rewriting after
specialization to scheme-module sheaves. No definitions or interfaces changed.
The existing node's proof and proof dependencies already describe this argument,
so no node edit is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affineDerivedPushforwardSheafReverse_unit`
(node `lem-pc-affine-derived-pushforward-sheaf-reverse-unit`).
There are zero remaining holes in the delivered module and zero holes added.
This is a proof from the existing stated dependencies, including
`AlgebraicGeometry.existsUnique_affineDerivedPushforwardReverseComparison`
(node `lem-pc-affine-derived-pushforward-sheaf-edge-descent`), whose existing
proof remains postponed; it is not a claim that the transitive closure is sorry-free.
All private helpers are proved.

## No longer needed

None. The sole original public import
`Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCanonical` is needed by
the statement and by the K-injective component formula. All four existing DAG
proof dependencies are used through this import. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The proof works for arbitrary
unbounded representatives and does not introduce nonzero-ring assumptions.
The first compile could not load the recently landed canonical comparison;
waiting for the next published build resolved that temporary availability issue.
The existing naturality theorem in `LeftExactHomologyComparison` supplies the
first step directly. Mathlib searches through leanfinder, loogle and grep found
no shorter specialized reverse-unit theorem.

## Second reading by G2

1. Compared the delivered module with the repository version. The public theorem
   signature, visibility, docstring, and imports are unchanged; only the proof
   and private proof helpers were added. Verdict: pass.
2. Compiled the module with `lcompile.py` and inspected the declarations and
   proof helpers. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`,
   or `implemented_by` declarations in the delivered file. The proof uses only
   the existing postponed descent theorem in its transitive closure. Verdict:
   pass.
3. Checked the target statement and the proof's edge cases, including zero
   complexes, arbitrary unbounded representatives, and the fact that only
   `Q.map s` is inverted. No new statement was introduced and no hypothesis or
   conclusion was changed. Verdict: pass.
4. Checked the route against the node and unit records. The K-injective
   resolution, unit naturality, reverse-comparison naturality, and cancellation
   steps follow the recorded proof dependencies; no shorter applicable library
   theorem was found, and no import or node can be pruned. Verdict: pass.
5. Checked that the existing node's proof, dependencies, and proof origin agree
   with the Lean proof and that the unit route remains realized. Verdict: pass.

Changed only this report by adding the required second-reading record; no Lean,
DAG, or interface changes were needed.
