## What changed
Added the proof-only import of `Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent`.
The target theorem `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility` is now
proved by introducing `ε`, `F`, and the complex data and applying the fixed-component theorem.
Added the corresponding DAG node and module.

## Proved and sorry left
Proved: `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_compatibility`.
Sorry left: `AlgebraicGeometry.affineDerivedPushforwardSheafEdge_component`, in node
`lem-pc-affine-derived-pushforward-sheaf-edge-compatibility-component`.

## No longer needed
None; the original public imports remain needed for the theorem signature.

## Where the brief, the DAG or earlier work was wrong
The earlier statement-disputed objection correctly notes that arbitrary `ε` is mathematically
unusually strong, but stage 3 requires realizing the DAG plan from its admitted dependencies.
The proof therefore decomposes the target into its fixed-component comparison theorem.

## New nodes
`lem-pc-affine-derived-pushforward-sheaf-edge-compatibility-component`: fixed `F,C,hC`
component of the target equality, stated in `Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeComponent`.

## Earlier second reading (a previous round; superseded)
The fixed-component theorem is a strict decomposition of the target; its signature and imports compile, and the target applies it for arbitrary `F` and `C`.


## Second reading by U2

1. **Statements unchanged.** I diffed the delivered compatibility module against the repository version. The target theorem signature is byte-for-byte unchanged; only its proof and a proof-only import were added. The added component theorem has its own new node and does not alter an existing declaration. Verdict: pass.

2. **Proof and axioms.** Both sandbox modules compile cleanly with `lcompile.py --all`. The target has no `sorry`; the only remaining `sorry` is the named component theorem, with a docstring, node, and source. No forbidden declarations or hollow definitions are present. Verdict: pass subject to the admitted component theorem.

3. **New statement.** The component theorem is the target equation with the outer quantification over `F` and `C` fixed, so it is strictly simpler and is exactly what the target proof applies. Its hypotheses and conclusion match the target specialization. The arbitrary-`ε` concern remains recorded by the existing `STATEMENT-DISPUTED` marker on the target; this delivery does not weaken either statement. Verdict: pass as a decomposition, with the component hole left explicit.

4. **Pruning and imports.** The compatibility module keeps its two public imports needed for its signature and adds the component as a plain proof-only import. The component module's public imports are needed for its theorem statement. No old proof dependency or module became unused. Verdict: pass.

5. **DAG and unit route.** The target node now records the component theorem as the proof route, and the component node records the exact fixed-component statement, source, and proof dependency. Both remain in unit `sk-thm-picard-semicon`; no unit route or realized step was bypassed. Verdict: pass.

Changed: added the proof-only import and target proof, added the component module and node, and documented the second reading.
