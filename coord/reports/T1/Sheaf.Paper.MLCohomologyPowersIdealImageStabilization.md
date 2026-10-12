## What changed

Proved `AlgebraicGeometry.ml_cohomology_powers_ideal_image_stabilization` in
`Sheaf.Paper.MLCohomologyPowersIdealImageStabilization`, preserving its signature and all
public imports. The proof constructs the short exact cokernel sequences, uses the existing
cohomological delta-functor from `sheafCohomologyAndHigherDirectImages`, and performs the
naturality and kernel-bound chase explicitly. Only the degree `p + 1` threshold of
`cohomology_powers_ideal_application` is required. A proved private helper identifies the
zeroth ideal-product inclusion as an isomorphism using the image of the left unitor.

Added the proof-only Mathlib import `Mathlib.Algebra.Homology.ShortComplex.ModuleCat` for
`ShortComplex.Exact.moduleCat_range_eq_ker`. Updated the existing node's proof, proof_deps,
and proof_origin to match this route. No statements or definitions changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ml_cohomology_powers_ideal_image_stabilization`
(node `ml-cohomology-powers-ideal-image-stabilization`).

No sorry remains in the delivered module. No holes were added or split off. The result is
proved from the existing bounds and cohomological delta-functor; their downstream proof
obligations are unchanged. The private helper `power_zero_isIso` is completely proved.

The proof handles `c = 0`, `n = 1`, and `k = n + c` without strict inequalities.
For `c = 0`, the kernel comparison is with the identity transition at k; for the boundary
`k = n + c`, the intermediate exponent `k - c` equals n. There are no nonemptiness or
nonzero assumptions on the scheme, module, ring, or ideal.

## No longer needed

Removed the proof-only imports:

- `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
  (node `lem-weil-pbc-horseshoe-delta-functor`).
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
  (node `lem-weil-pbc-scheme-modules-enough-injectives`).

Their direct proof dependencies were removed from the item's DAG node. The existing
`pqf-def-cohomology` already packages the exactness and naturality needed here; no
horseshoe resolution is constructed. This does not assert that those modules are globally
unreachable: other importers may still use them.

The degree-p application and the maximum of two thresholds in the old node's step 2 are
also unnecessary for this image-stabilization clause. No other nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The original node requested both degree-p and degree-(p+1) thresholds although this clause
needs only degree p+1, as already explained in the theorem's docstring. Its explicit
horseshoe and scheme-enough-injectives dependencies are redundant with the existing
cohomology delta-functor interface. The unit route is unchanged: this node does not realize
a separate unit statement or step, and the proof still follows the exact-sequence argument
of Stacks 02OB(3).

The repository omits the untracked literature files. The cited proof was read from the
available local literature copy at
`/home/ubuntu/work-bp/sheaf/literature/stacks-project/coherent.tex`, lines 5550-5650.
No other discrepancy or statement dispute was found.

## Second reading by T1

1. Compared the delivered module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and the proof body changed. The node records only proof, proof_deps, and proof_origin updates.

2. Compiled the module with `lcompile.py`; it succeeds with no errors. The module contains no `sorry`, axiom, unsafe, opaque, extern, implemented_by, or hollow definition. The private helper and target proof use only ordinary kernel axioms (apart from any imported open theorems).

3. Checked the proof route and statement dependencies. The target statement is unchanged and the proof uses the existing cohomological delta-functor and degree-(p+1) power kernel bound. The removed horseshoe and enough-injectives imports are redundant. No new statement or split-off hole was added.

4. Checked pruning and DAG agreement. The imports removed are proof-only imports and the node's `proof_deps`, proof steps, and origin now match the actual route. The unit route is preserved: this node realizes no separate unit statement or step.

5. Checked edge cases and strength. The argument handles c = 0, n = 1, and k = n + c, with no extra nonemptiness or nonzero assumptions. The image equality is proved in both directions from exactness and naturality, with the same conclusion as the original target.

Changed only the proof-only import list, the target proof, matching DAG proof metadata, and this report section.
