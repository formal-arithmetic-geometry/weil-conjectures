## What changed

Proved the body of `AlgebraicGeometry.derived_lower_truncation_cycle_formula`, without
changing its signature or existing documentation. Added two proof-only imports:
`Sheaf.AlgebraicGeometry.LeftExactTruncationCycleFormula` and
`Sheaf.AlgebraicGeometry.DerivedLowerTruncationUnitBridge`.

The underived cycle formula is fully proved using Mathlib homology data. Since good
lower truncation has zero incoming differential, kernel preservation and preservation
of the cokernel of zero give its bottom homology comparison. Kernel-lift uniqueness
and homology-quotient naturality prove its action on cycles. The original theorem
combines this comparison with the independent derived-unit bridge: its isomorphism
is `d.symm ≪≫ a`, and the proof rewrites and cancels the bridge before applying the
underived calculation. No data definitions, existing signatures, or visibility changed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.derived_lower_truncation_cycle_formula`
(node `lem-sc-derived-lower-truncation-cycle-formula`) by decomposition, not a
sorry-free proof of its import closure.

Also fully proved `AlgebraicGeometry.leftExact_truncation_cycle_formula`
(node `lem-sc-left-exact-truncation-cycle-formula`), with no derived-category,
enough-injectives, or K-injective assumptions. This proof uses only Mathlib.

Added exactly one remaining hole:
`AlgebraicGeometry.derived_lower_truncation_unit_bridge`
(node `lem-sc-derived-lower-truncation-unit-bridge`). It isolates bottom-degree
invertibility of the actual derived unit, compatibility of complex and derived
truncations, and localization naturality. Its statement has no cycle lift, no
homology quotient, and no comparison with F(H^n(I)); it is strictly the derived
part of the argument. Its complete proof in words is in its docstring and node.
The delivery closes one original hole and adds one hole: net zero by hole count,
with a fully proved underived part and a simpler remaining derived item.

All three modules compile cleanly using lcompile.py. Zero complexes, arbitrary
negative cutoffs, and unbounded complexes were checked in the mathematical
construction: the underived calculation relies only on strict support below n,
and the bridge uses boundedness only for the lower-truncated complex. No
preservation of the original homology quotient by F is assumed.

## No longer needed

No existing imports were removed; the original module had no proof-dependency
imports. The parent proof no longer needs
`new-qcoh-sections-left-exact-bottom` /
`Sheaf.Paper.DerivedSectionsLeftExactBottom`: a Nonempty bottom isomorphism
without a specified normalization does not furnish the action on cycles.

`lem-sp-derived-functor-single-identification` /
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
is no longer a direct dependency of the parent. It remains needed in the plan
of the derived-unit bridge, together with negative vanishing, triangulatedness,
and bounded-below/unbounded compatibility. No global pruning of those modules
is claimed. The unit record has no realized nodes, and the route stays within
the original canonical bottom-comparison argument.

## Where the brief, the DAG or earlier work was wrong

The existing bottom-comparison theorem produces a natural isomorphism under
Nonempty but states no compatibility with the derived unit. Naturality of an
arbitrary isomorphism alone does not give the required normalization. The
original DAG mentions normalization in words; the new bridge makes the
needed property explicit, and the underived cycle part is proved separately.
No statement was disputed or weakened.

The local Stacks TeX file named in the inherited source records was absent.
The official pages https://stacks.math.columbia.edu/tag/05TC,
https://stacks.math.columbia.edu/tag/0AVW, and
https://stacks.math.columbia.edu/tag/08D4 were read directly. The generic
kernel/unit calculation is an expansion of these references, not a claim
that an affine-scheme lemma states this abstract result verbatim.

## New nodes

`lem-sc-left-exact-truncation-cycle-formula`, in
`dag/nodes/sec-picard-framework/lem-sc-left-exact-truncation-cycle-formula.json`,
records the fully proved theorem in
`Sheaf.AlgebraicGeometry.LeftExactTruncationCycleFormula`.

`lem-sc-derived-lower-truncation-unit-bridge`, in
`dag/nodes/sec-picard-framework/lem-sc-derived-lower-truncation-unit-bridge.json`,
records the remaining derived-unit/localization theorem in
`Sheaf.AlgebraicGeometry.DerivedLowerTruncationUnitBridge`.

The parent node's proof, proof_deps, and proof_origin now match the Lean
assembly. No change records are needed: no existing public interface changed.

## Second reading by G1

1. **Interfaces unchanged.** I compared the delivered parent module with the repository version. The target theorem signature, all existing declarations, and visibility are byte-for-byte unchanged; only its proof and two proof-only imports differ. The two additional modules are new split-off declarations and introduce no adaptation of an existing interface.

2. **Compilation and axioms.** I compiled all three sandbox modules with `lcompile.py --all`; they compile without errors or warnings. The parent and the underived theorem contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The bridge is the sole named remaining `sorry`, and its docstring gives the complete derived-unit/localization proof plan. Its node is `lem-sc-derived-lower-truncation-unit-bridge`.

3. **Truth and strength of split statements.** The underived theorem is a strict kernel and homology-map calculation and is exactly the portion required by the parent; it has no derived hypotheses and is fully proved. The bridge states only the bottom derived-unit factorization and invertibility needed to assemble the parent, with no cycle-class or homology-quotient conclusion. It is therefore strictly simpler than the parent and is not a restatement. Both declarations have matching DAG nodes, sources, proof plans, and verbatim Lean statements.

4. **Shortest route and pruning.** The underived proof uses Mathlib's preserved-kernel/cokernel homology interfaces and the truncation projection isomorphism. The parent then composes that result with the bridge and cancels the bridge isomorphism. The parent no longer directly uses the former arbitrary bottom-comparison and single-object nodes; its updated `proof_deps` records precisely the two delivered declarations. No public import was added for proof-only dependencies.

5. **Unit route and edge cases.** The parent continues to realize the canonical bottom-comparison route through the underived calculation and derived-unit bridge; no unit statement or realized step was altered. The construction is uniform for zero complexes, negative cutoffs, and unbounded complexes, as recorded in both proof docstrings and the report above.

I changed only the parent proof, added the two proof modules and their DAG nodes, and added this second-reading record. The remaining bridge hole is the single derived statement described above; no definition contains a `sorry`.
