## What changed

The signature and docstring of
`AlgebraicGeometry.Scheme.Modules.isInvertible_and_globallyGenerated_positiveTensorFamily`
are unchanged. Its proof now performs an induction for invertibility, chooses finite global
families for the factors, constructs a generating family from the tuple epimorphism, and
combines the four conclusions. The induction uses the already proved source-library
`IsInvertible.tensorObj` instance instead of the large pullback/tensor comparison package.

Added `Sheaf.AlgebraicGeometry.FiniteGlobalGeneratingFamily`, whose theorem is proved from
`finite_sections_cover_of_globally_generated` and
`invertible_generating_sections_fibre_criterion`. It adds a zero section to allow both `Fin 0`
and larger finite covers, and builds compatible sections explicitly by restriction from top.

Added `Sheaf.AlgebraicGeometry.FiniteTensorGeneratingSections` to isolate tensor generation
for arbitrary finite index types, including empty ones. Updated the target node's proof route
and created nodes for both helpers. All three modules compile without warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.isInvertible_and_globallyGenerated_positiveTensorFamily`.
Also proved the new theorem
`AlgebraicGeometry.Scheme.Modules.finite_global_generating_family`
(node `lem-sc-finite-global-generating-family`) from existing declarations.

One new hole remains:
`AlgebraicGeometry.Scheme.Modules.finite_tensor_generating_sections`
(node `lem-sc-finite-tensor-generating-sections`). This is a decomposition: one original
hole closed, one new hole added, direct net zero. The original target module has no `sorry`.
The existing finite-cover and fibre-criterion dependencies remain unproved in the library;
they are used as the stage permits and are not additional holes introduced by this delivery.

## No longer needed

Removed these proof imports from the target module:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: already available through the
  public statement dependency `PositiveTensorFamily`.
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`: replaced by the proved
  `WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` tensor-invertibility instance.
  Node `lem-weil-pbc-invertible-pullback-tensor` is no longer required by this argument.
- `Sheaf.AlgebraicGeometry.TensorGeneratingSections`: the new finite-index tensor lemma
  imports it and uses it in its stated proof plan. It remains needed transitively.

No unit statement or realized unit step was bypassed. The realized route for
`sk-thm-curveestimate` has no intermediate realized steps to preserve here. Tensor products,
positive tensor families, and global generation definitions remain in the statements or
transitive imports. No further dependency subtree is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The existing `tensor_generating_sections` accepts only index types
`ULift (Fin (m i + 1))`, whereas the target quantifies over arbitrary finite generating
families, allowing empty index types. The new intermediate explicitly handles this missing
transport and zero-factor case; it is strictly the tensor-generation part of the target,
with no compactness, invertibility, or existential finite-family conclusion.

The finite-family existence step had no direct named dependency in the target plan. It is
now proved using two existing nodes rather than left as an unnamed gap. Edge cases checked:
zero tensor parameter means one factor; an empty scheme may have a `Fin 0` cover; an empty
index in a generating family forces its factor to be zero; singleton indices give the
original tensor-generation statement. No existing declaration or definition was changed.
Leansearch returned Internal Server Error; leanfinder, loogle, and local searches were used.

## New nodes

`lem-sc-finite-global-generating-family`: the finite-cover and fibre-criterion step,
proved in its own module; no hole added.

`lem-sc-finite-tensor-generating-sections`: the remaining generation assertion for arbitrary
finite index types. Its docstring and node give the enumeration argument and the empty-factor
argument. This is the sole new hole, and does not restate the target.

## Second reading by M2

1. **Signatures and visibility:** diffed the delivered target against the repository. The
existing target statement is unchanged byte for byte; added helper declarations are new
modules with matching DAG `lean.statement` fields. Public imports are limited to statement
dependencies, while proof-only imports are plain `import`.
2. **Compilation and axioms:** compiled all modules with `lcompile.py --all`; compilation
is clean. There is no `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow
definition. The only remaining `sorry` is the named split theorem, as reported above.
3. **Statement review:** `finite_global_generating_family` is the finite-subcover
consequence for an invertible globally generated module. `finite_tensor_generating_sections`
is arbitrary finite-index tensor generation, including the empty-factor case, and is
strictly weaker than the target. Small cases (one factor, singleton indices, and empty
indices) agree with the intended meanings.
4. **Proof and pruning:** the target proof follows the induction, finite-family, and tensor
helper route. Removed imports and the unused pullback-tensor node are listed above; no
shorter proved declaration was found.
5. **DAG and unit:** node proof steps, dependencies, origins, and Lean declarations match
the code, and the realized unit route is preserved.

Second reading changes: corrected the stale mirrored report from an earlier two-hole attempt. No Lean proof or statement changes were needed. Repeated searches with tensor epimorphism and GeneratingSections queries found no applicable proved shortcut; local searches found only the existing nonempty-index tensor statement and tensor-section trivialization lemmas.

