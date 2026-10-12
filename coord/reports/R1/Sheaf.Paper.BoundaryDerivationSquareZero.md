## What changed

Proved `AlgebraicGeometry.boundary_derivation_square_zero` from the existing horseshoe resolution and horseshoe delta-functor declarations. Added proof-only imports for those declarations and factored the local algebra/Cech derivation step into `Sheaf.Paper.BoundaryDerivationAlgebraicData`.

## Proved and sorry left

The target theorem `AlgebraicGeometry.boundary_derivation_square_zero` is proved. The new intermediate theorem `AlgebraicGeometry.boundary_derivation_algebraic_data` remains a single documented `sorry`, recording the local multiplication, Cech naturality, and Leibniz calculation.

## No longer needed

No stated proof dependency was removed. The target proof uses the horseshoe resolution and horseshoe delta-functor modules; all original imports remain needed for the target statement or the intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan omitted the explicit bridge from degreewise horseshoe rows to the global-sections short exact complex. This delivery obtains it from `exists_horseshoe_rightDerived_deltaFunctor` and isolates the remaining algebraic argument as a strictly smaller theorem.

## New nodes

Added `lem-sc-boundary-derivation-square-zero-algebraic-data`, with declaration in `lean/Sheaf/Paper/BoundaryDerivationAlgebraicData.lean`.

## Earlier second reading (a previous round; superseded)

The split theorem is strictly smaller than the target: it fixes all compatible resolutions and the global-sections short exact map. The target proof supplies those data via existing horseshoe declarations and preserves the original target signature.

## Second reading by R1

1. Compared both delivered Lean modules with the repository versions using `diff`. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports, the proof, and the new auxiliary module changed. The new module is proof support and does not alter an existing interface. Verdict: pass.

2. Compiled the complete sandbox set with `lcompile.py --all`; both modules compile without errors or warnings. The target proof has the expected `sorryAx` only because it invokes the documented split theorem; no `sorry` occurs in a definition and no forbidden declaration form is present. The split theorem is the sole listed remaining hole. Verdict: pass as a documented decomposition.

3. Read the split theorem and its node, and checked that it fixes all resolutions, comparison maps, degreewise exactness, and the global short complex before asserting the algebraic identities. Its conclusion is therefore strictly narrower than the target existential and is exactly what the target proof needs. The theorem's source, proof sketch, declaration record, and statement agree. No duplicate library theorem was found. Verdict: pass.

4. Checked the route against the existing horseshoe resolution and horseshoe delta-functor declarations. The proof uses the unit's compatible-resolution and connecting-map route, then the strictly smaller algebraic step; no unit route is bypassed. The added horseshoe imports are proof-only, while the original public imports remain needed by the target signature. No old import was removed and no pruning is claimed. Verdict: pass.

5. Updated the target node's `proof`, `proof_deps`, and `proof_origin`-compatible route description to match the actual Lean applications, retaining the unchanged statement and source. The new node's fields and split status match the Lean theorem. Verdict: pass.

Changed during second reading: added this independent review, recorded the target node's actual horseshoe-to-algebraic proof route, and made no Lean statement or definition changes.
