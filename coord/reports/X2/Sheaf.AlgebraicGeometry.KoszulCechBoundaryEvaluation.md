## What changed

Proved `AlgebraicGeometry.koszulCechBoundary_evaluation` in
`Sheaf.AlgebraicGeometry.KoszulCechBoundaryEvaluation` without changing its signature or docstring.
Added the proof-only import `Sheaf.RingTheory.KoszulGeneratorChainMap` to use its proved
`ExteriorAlgebra.boundary_wedge` theorem. Four proved private helpers identify the erased
increasing enumeration, count its position, reindex the contraction formula, and transport
cochain evaluation through supported degrees. Updated the item's DAG proof to match.

The complete module compiles cleanly with lcompile.py. No public interface changed.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.koszulCechBoundary_evaluation`
(node `lem-sc-koszul-cech-boundary-evaluation`). No sorry remains in the item, and no hole
was added. This is a proof, not a decomposition. The used `boundary_wedge` theorem is proved.
The argument includes two-element subsets (the smallest case allowed by hJ), arbitrary
exponent e including zero, zero coefficients, and arbitrary commutative rings; it uses no
localization or nonzero assumption. All larger-cardinality cases use the same formula.

## No longer needed

Removed from the old direct `proof_deps`: `lem-weil-pbc-koszul-differential`.
No imports or modules are pruned: all three existing public imports supply statement
notation or definitions. The direct use of the uniqueness/formula clauses of
`lem-weil-pbc-koszul-differential` is replaced by the existing `boundary_wedge` tool from
`new-q2-koszul-generator-chain-map`. The Koszul differential module remains transitively
needed, so this replacement does not claim to prune it from the target closure.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's contraction calculation was already available in
the library as `ExteriorAlgebra.boundary_wedge`, so it need not be reconstructed here.
The enumeration and transport steps of the plan have been made into complete Lean proofs.


## Second reading by X2

1. PASS. Compared the sole delivered module with the repository using `diff`, and
   checked the existing theorem signature byte for byte with a script. The signature,
   universes, variables, visibility and docstring are unchanged. The additions are one
   plain proof-only import and four private proved helpers. No definitions or target
   statements changed; no change record is needed.
2. PASS. Independently compiled the delivered module with `lcompile.py`, without errors
   or warnings. Scanned its source: no sorry, axiom, unsafe, opaque, implemented_by,
   extern or kernel-check bypass. Compiled a scratch copy with `#print axioms` for
   `AlgebraicGeometry.koszulCechBoundary_evaluation` and
   `ExteriorAlgebra.boundary_wedge`; both use exactly `propext`, `Classical.choice`
   and `Quot.sound`, with no `sorryAx`. No data construction was added.
3. PASS. There are no split-off statements or new public statements. Read each private
   helper: uniqueness identifies the erased enumeration, the order isomorphism counts
   the lower indices, reindexing gives the sorted contraction sum, and equality
   elimination gives the coefficient transport. At card(J)=2 the tail differential
   is minus the two-term contraction, and both erased subsets are singletons.
   For r=0 or r=1 the hypothesis is impossible. Exponent zero, zero coefficients,
   characteristic two and the zero ring require no extra assumptions. Searched
   Mathlib's finset sorting lemmas and the project's two Lean roots using ordering,
   deletion and evaluation terms, and ran msearch grep for erased enumeration,
   filter/order embedding and boundary_wedge; found no shorter complete theorem.
4. PASS. The proof directly uses the existing proved `boundary_wedge`, then only
   finite-set enumeration, linearity and supported-degree transport. The three
   existing public imports provide the Hom-cochain type, affine sections/degree
   transport and Koszul-tail definitions needed by the signature; the added import
   is plain because only the proof needs it. The No longer needed section now
   explicitly names the sole removed direct dependency,
   `lem-weil-pbc-koszul-differential`; its module remains transitively needed.
   Checked `dag/units/sk-thm-picard-duality.json`: its realized statement list and
   sole realized step list are empty, and none is changed or bypassed by this
   below-unit contraction calculation.
5. PASS. The only changed node fields are `proof`, `proof_deps` and `proof_origin`.
   The proof steps accurately describe the four private helpers and final proof;
   their cited dependencies have the used Lean declarations. The dependency union
   matches `proof_deps`. The original statement, source, unit, chapter and Lean
   statement record remain unchanged. No new nodes were needed.

Second reading changed only this report: made the removed direct dependency explicit
and recorded the independent checks. The Lean proof and node required no repair.
