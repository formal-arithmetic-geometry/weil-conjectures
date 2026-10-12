## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.DerivedMapLift` with the complete
three-step proof already specified by `lem-pc-ring-derived-map-lift`. The statement,
universes, visibility, and existing docstrings are unchanged. Added the proof-only
import `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective` for
`CochainComplex.IsKProjective.exists_Q_map_eq`, an already proved chain-map
representation theorem implementing the existing representative dependency.

The proof completes alpha to a distinguished triangle. In each degree i >= n,
epimorphy in degree i makes the second homology map zero, and monomorphy in degree
i+1 makes the connecting map zero. Exactness then makes the cone homology zero.
The boundary case i = n uses exactly the given epimorphism, rather than assuming
an isomorphism there. Representing the cone via Q's object preimage and its
isomorphism transfers this vanishing to a complex K. Precise vanishing kills
beta composed with the cone map. Triangle coyoneda exactness produces delta;
bounded-above termwise projectivity gives K-projectivity of P, so the existing
representation theorem supplies the required chain map gamma.

The original DAG proof and its six dependencies remain accurate: TR1, long exact
homology, precise vanishing, Hom exactness, and representation are all used.
The unit record `sk-thm-picard-duality` was read; its route is preserved.
Lean compilation passes without warnings. Search used LeanFinder, Loogle, and
ripgrep in the source library and Mathlib. No shorter exact lifting theorem was
found; ripgrep found the existing representation wrapper. Stacks Tags
[064E](https://stacks.math.columbia.edu/tag/064E) and
[064D](https://stacks.math.columbia.edu/tag/064D) were read online because the
referenced local `literature/stacks-project/derived.tex` is absent on this machine.

## Proved and sorry left

Closed: `RingTheory.derived_map_lift` (node `lem-pc-ring-derived-map-lift`),
1 of 1 original holes. Added: none. No `sorry` remains in the delivered module.
No decomposition or new theorem was introduced.

The proof uses the existing, still unproved `CategoryTheory.precise_vanishing`
(node `lem-pc-ring-precise-vanishing`, module
`Sheaf.Algebra.Homology.PreciseVanishing`). This dependency remains a separate
stage-3 item; this delivery does not claim that the import closure is sorry-free.

## No longer needed

None. No imports removed and no DAG nodes or modules pruned. All original proof
dependencies are used. The single added import is used to represent delta by a
chain map. The original public imports support the unchanged statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The local literature path cited by
the node is absent; the corresponding Stacks pages were read online. The
representative node names Mathlib's homotopy-class comparison, while the source
library additionally offers the proved chain-map wrapper used here. This is the
same argument, with no change to the route or to the node's statement.

## Second reading by S2

1. **Visible changes.** Compared the delivered module with the repository version. The theorem signature, universes, visibility, and docstring are byte-for-byte unchanged; only the proof and one proof-only import were added. No change record is required.

2. **Proof and axioms.** Compiled `lean/Sheaf/RingTheory/DerivedMapLift.lean` with `lcompile.py`; it compiles cleanly with no warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`. The proof uses the existing precise-vanishing and K-projective representation results and introduces no new assumptions.

3. **Statements and dependencies.** No statement was split off or changed. The existing node statement is exactly the theorem statement, and its six declared proof dependencies remain the route used by the proof. The added `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective` import is proof-only and supplies `exists_Q_map_eq`; the public imports remain unchanged.

4. **Pruning and route.** Searched the local library and Mathlib for a shorter lifting theorem; none was found. The proof follows the node route: distinguished triangle, long exact homology vanishing, precise vanishing, triangle exactness, and chain-map representation. No old proof dependency or module can be pruned, and the unit route is preserved.

5. **DAG agreement.** The node's proof, `proof_deps`, and `proof_origin` agree with the proof as written. The unit record and target statement are unchanged. No new nodes or split-off holes were introduced.

I changed only the proof body and added the proof-only K-projective import, then verified the module compilation and delivery checks.
