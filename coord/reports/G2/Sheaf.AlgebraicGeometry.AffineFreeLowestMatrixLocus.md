## What changed

Proved the body of `AlgebraicGeometry.Scheme.exists_affineFreeLowestMatrixLocus`
without changing its signature or visibility. Added the proof-only import
`Sheaf.AlgebraicGeometry.AffineFreeKernelRankLocus`, whose single statement concerns
an ordinary map between finite-free sheaves and has no complexes, bounds, degree,
or derived-category assumptions. Added proof-only imports for tensor closedness,
bounded-above K-flatness, flat coproducts, and Grothendieck abelianness.

The private helpers `pullback_Q_iso`, `free_flat`, and `lowest_pullback_iso` are
fully proved. The first two use the existing arguments in
`FiniteFreeResidueModelPullback`, without importing its unrelated local-model theorem.
The third composes the derived homology comparison, the zero-incoming-differential
cycles/homology isomorphism, and uniqueness of the kernel limit. The public proof
applies the new ordinary-map locus statement and transports rank in both directions.
Both delivered modules compile cleanly with `lcompile.py`.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_affineFreeLowestMatrixLocus`
(node `lem-sc-affine-free-lowest-matrix-locus`). No sorry remains in the item module.

Added one hole:
`AlgebraicGeometry.Scheme.exists_affineFreeKernelRankLocus`
(node `lem-sc-affine-free-kernel-rank-locus`, new module
`Sheaf.AlgebraicGeometry.AffineFreeKernelRankLocus`). This is a decomposition,
not a net decrease in holes: the homological part is complete, while the ordinary
geometric matrix locus remains. No data definition is added or changed.

Edge cases checked mathematically: empty source and empty affine X, zero codomain,
s=r=0, and s<r. Over a nonempty affine chart its ring is nonzero, so the padded
basis vector in the smaller-domain contradiction is indeed nonzero. No arbitrary
witness of an unproved existence statement is used to define data.

## No longer needed

No original import was removed: all four public imports support the unchanged
statement. The parent's planned dependency `lem-pc-flat-complex-derived-pullback`
(module `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`) is replaced by the
already proved bounded-flat K-flatness theorem and the specified derived counit.
It need not be imported for this item. The two geometric leaves
`lem-sc-square-injective-free-map-dual-coker-zero` and
`lem-weil-pbc-quasi-coherent-ideal-closed-subscheme`, as well as
`def-sbc-locally-finite-presentation`, remain needed in the new ordinary-map node;
they are not pruned from the route. No other node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan names the flat-complex comparison, but identifying its homotopy
representative with ordinary pullback and lowest homology with a kernel requires
additional categorical glue. That glue is now proved explicitly, not postponed.
The two other geometric dependencies are Mathlib composites, not Sheaf modules.

Read Stacks Tags 0BDL and 0EWY directly. The ordinary-map node retains the original
matrix and padding arguments; it does not replace the unit route. The unit record
`sk-prop-av-cube` has empty realized lists, and this delivery changes no unit.
LeanSearch was unavailable (HTTP internal server error); LeanFinder and grep ran,
and found ideal-sheaf and homology/kernel infrastructure but no representing-locus
theorem. Blueprint searches for `kernel finite free` and `kernel` found no duplicate
ordinary-map locus statement.

## New nodes

`lem-sc-affine-free-kernel-rank-locus`: the ordinary finite-free sheaf-map part of
steps 2--4 of the original node. Its proof records the rank-equal matrix quotient,
the smaller-domain empty-locus case, and finite presentation. Its module states
one public theorem with exactly `:= by sorry`, a source and complete proof in words.
The parent now records the actual Lean reduction. No interface change or forced
adaptation is included.

## Second reading by G2

1. **Interface and accidental changes.** Compared the delivered item module with the repository version. The theorem statement and all existing declarations are byte-for-byte unchanged; only proof-only imports, private helpers, and the proof body changed. The added ordinary-map module is a new split-off statement recorded by its DAG node.

2. **Proof and axioms.** Compiled both delivered modules with `lcompile.py --all`; both compile cleanly. The item theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The only remaining `sorry` is the named ordinary-map theorem `exists_affineFreeKernelRankLocus`, whose proof and source are documented in its module and node; it is the intentional decomposition hole.

3. **Statements and split.** Checked the new ordinary-map statement against the finite-free matrix argument, including the equal-rank, smaller-domain, zero-rank, empty-scheme, and zero-ring cases. It is true and strictly simpler than the parent derived-complex statement, and is not duplicated elsewhere in the library. No target statement was weakened or given extra hypotheses.

4. **Pruning and route.** The proof uses the bounded-above flat K-flat comparison, tensor-closed flatness, derived pullback, and the new ordinary-map locus exactly as recorded in the parent node's `proof` and `proof_deps`. No original public import was removable; the additional imports are proof-only. The unit route and its realized list are unchanged.

5. **DAG agreement.** Verified that the parent node records the actual homological reduction and ordinary-map dependency, and that the new node records its statement, source, proof steps, dependencies, and Lean declaration. The remaining hole is named and documented rather than hidden in a definition.

I changed only this report section after the initial worker delivery; no Lean statement or proof was altered during second reading.
