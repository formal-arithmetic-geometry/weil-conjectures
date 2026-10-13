## What changed

The original signature and public imports of
`Sheaf.AlgebraicGeometry.AffineCoverModuleTensorFlatCriterion` are unchanged.
Its theorem `AlgebraicGeometry.affine_cover_module_tensor_flat_criterion` now has
an entirely written Lean proof. A proved private helper
`flat_tensor_right_unit_iff` cancels the redundant ring `T tensor_A A`, including
its specified right A-action. It uses `Algebra.TensorProduct.rid`, localization
at the trivial submonoid, `Module.flat_iff_of_isLocalization`, and a T-linear
tensor equivalence. The proof then uses the existing proved relative-flatness
stalk lemmas. Quasi-coherence transfers from ordinary pullback via uniqueness
of the left adjoint to pushforward. The reverse direction applies the actual
covering hypothesis to the first projection of each pullback point.

One new module, `Sheaf.AlgebraicGeometry.AffinePullbackChartTensorFlatStalks`,
contains the remaining single-chart geometric comparison. This has one affine
open, no cover, and only asserts flatness on its inverse image. Its tensor ring
is T itself, so the redundant ring cancellation is already discharged in the
original module. It does not assert global IsFlatOver.

Both modules compile cleanly with `lcompile.py --all`. Sources read: Stacks
01U4, 00HT, and 01IA, and the actual signatures/proofs of
ModulePullbackAffineSections, RelativeFlatModuleStalk, RelativeFlatOfStalks,
IntrinsicFlatModuleStalkTensorPresentation, and the relevant Mathlib tensor and
localization declarations. Additional base-change coordinate lemmas were read;
their affine-morphism hypotheses or more elaborate comparison interfaces do
not directly give the required arbitrary-source chart criterion.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.affine_cover_module_tensor_flat_criterion`
(node `lem-pc-affine-cover-module-tensor-flat-criterion`).
No sorry remains in the original module. The private algebraic helper is proved.

Added one named hole:
`AlgebraicGeometry.affine_pullback_chart_tensor_flat_iff_stalks`
(node `lem-pc-affine-pullback-chart-tensor-flat-stalks`).
It is exactly `:= by sorry`, in its own module, with its source and complete
proof in words. This delivery is a decomposition, not a net removal of a hole:
one upper hole closed, one strictly local geometric hole added. The proof that
combines the local comparison with the cover and the two existing relative
stalk lemmas is complete Lean.

Edge cases checked mathematically: an empty affine chart has zero sections and
an empty inverse-image chart; T zero makes the tensor module and pullback chart
zero/empty; a zero module is flat. An empty finite cover makes a pullback point
impossible via hcover. No nontriviality, nonempty-index, finite-presentation,
separatedness, or flatness-of-base-change hypothesis is added.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections` from the original module.
It remains a planned proof dependency of the new chart lemma and is imported
there, so this is not a claim that its module is pruned from the target closure.
The original direct proof dependencies
`lem-weil-pbc-fibre-product-affine-spectra` and
`lem-pc-affine-sections-flat-over-base` are now needed below the new chart node;
`lem-weil-pbc-module-pullback-affine-sections` is similarly relocated there.
`def-pc-scheme-module-flat-over` is also removed from the original proof dependency
list: it is used by the unchanged signature, rather than as a proof lemma. Its
public import remains. No entire node or module is proved unnecessary by this
delivery: pruned none.
All original public imports remain, since the original statement uses them.

## Where the brief, the DAG or earlier work was wrong

The old plan correctly identified the mathematics, but did not provide a Lean
interface combining affine spectrum coordinates, pulled-back section modules,
base scalar actions, and relative stalk localization for one specified chart.
The existing affine section comparison concerns extension along the *source*
chart ring, whereas this theorem needs T-flatness; the ring pushout and tensor
reassociation are still required to bridge them. They are explicitly retained
in the new node and docstring, rather than assumed from the existing statement.

The algebraic cancellation is genuinely proved. A local SMul instance matching
the specified right A-module action is necessary while constructing its scalar
tower, because the tensor product also has a default A-scalar instance.
The existing relative stalk lemmas already prove the global localization/gluing
part. There is no statement dispute, interface change, or forced adaptation.
The unit's realized statement/steps are untouched.

## New nodes

`lem-pc-affine-pullback-chart-tensor-flat-stalks`, in
`dag/nodes/sec-picard-framework/`, isolates the geometric calculation on one
inverse-image affine chart. Its Lean declaration is in
`Sheaf.AlgebraicGeometry.AffinePullbackChartTensorFlatStalks`. It inherits the
original chapter/unit and blueprint ancestry. Its proof names the existing
affine fibre-product, module pullback sections, affine stalk tensor presentation,
and local flatness nodes. Actual LeanFinder/Loogle/grep searches found only
ingredients; LeanSearch returned Internal Server Error and is recorded as
unavailable. A whole-blueprint search and direct DAG/library searches found no
equivalent single-chart statement. No change record is needed.


## Second reading by W3

1. Compared both delivered modules with the repository. The original theorem signature,
   docstring and public imports are byte-for-byte unchanged; its only existing declaration
   has a new proof. The other module and its theorem are new. No definition or target
   statement changes, no change record or forced adaptation is needed.
2. Compiled both modules together with lcompile.py, cleanly (5.0 and 6.5 seconds).
   An axiom probe on the original theorem reports exactly propext, Classical.choice,
   Quot.sound and sorryAx. The only textual sorry in the delivered Lean files is the
   named chart theorem, exactly `:= by sorry`. No forbidden declaration mechanism,
   holed definition or arbitrary witness construction is present. The adjunction chosen
   in the original proof determines the left adjoint up to the isomorphism used there.
3. Read the chart statement, its full docstring argument and its node, and checked the
   scalar actions and base stalk in the statement. Stacks 01U4 and 00HT(6) give precisely
   the local flatness equivalence after the stated affine section comparison. Empty U,
   empty pullback, zero T and zero M are consistent; no hidden faithful-flatness or
   finiteness assumption is needed. This is a strict chart-level part of the argument:
   it does not glue a cover or conclude IsFlatOver, and the original proof genuinely
   performs both gluing directions and right-unit cancellation. Independent LeanFinder
   search for relative algebra-module localization flatness, Loogle search for
   Module.flat_of_isLocalized_maximal, Mathlib grep for tensor/stalk, and library rg
   searches found constituent tools, not an existing chart theorem. The remaining
   geometric comparison requires substantial affine coordinate/stalk compatibility
   work and cannot responsibly be closed by a short application of these tools.
4. Read the reduction from the top down. The proved right-unit helper respects the
   specified right A-action; uniqueness of left adjoints transfers quasi-coherence;
   the two existing relative stalk lemmas supply the actual global reductions. The
   imports added to the original module are proof-only. The new module's public imports
   provide notions in its signature; its ordinary imports retain the stated unresolved
   chart proof's ingredients. All old proof dependencies no longer used directly are
   now accounted for in No longer needed. The unit's realized mapping is already empty
   in the repository, and this delivery leaves it untouched; it introduces no bypass
   of a unit step or replacement of its route. Pruned modules: none.
5. Compared the old and new DAG records. The existing node changes only proof,
   proof_deps and proof_origin, and these track the actual Lean reduction. The new node
   has source, proof steps and dependencies, blueprint ancestry, creation metadata,
   searches and a verbatim Lean statement. The existing algebraic flatness leaf is
   correctly reused rather than duplicated.

Second-reading changes: completed the missing No longer needed entry for
`def-pc-scheme-module-flat-over`, recorded the independent Loogle search in the new
node, and added this review. No Lean repair was necessary. The result remains a
one-for-one decomposition (one original hole closed, one chart hole added), net zero.
