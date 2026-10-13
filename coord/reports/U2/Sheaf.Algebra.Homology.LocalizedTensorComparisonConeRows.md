## What changed

Reduced `ModuleCat.exists_localizedTensorComparison_cone_rows` without changing its
statement. The proof constructs the tensor-Q image of the actual mapping-cone triangle,
identifies it with another cone triangle, and applies the universal-model triangle-row
statement. It proves the ordinary coefficient naturality squares for every chain map,
then composes them with the model squares. The concrete boundary is handled separately
by `ModuleCat.tensorCoefficient_cone_boundary`, using a shift-compatible natural
transformation and Mathlib boundary naturality. Both new statements have their own
modules and DAG nodes. The unit route remains tensor, cone, exact cohomology, comparison.

The rings, complexes, models, maps and all original hypotheses stay identical.
The chain-level operations in this reduction actually need no K-flatness assumptions;
the original hQ, hK₁ and hK₂ are retained, with the unused-variable linter scoped off.
No definition, existing signature or public import was changed.

## Proved and sorry left

Closed the original hole in
`ModuleCat.exists_localizedTensorComparison_cone_rows`
(node `lem-pc-localized-tensor-comparison-cone-rows`).

Proved `ModuleCat.tensorCoefficient_cone_boundary`
(node `lem-pc-tensor-coefficient-cone-boundary`).

One new hole remains:
`ModuleCat.exists_baseDerivedTensorCohomologyModel_triangle_rows`
(node `lem-pc-base-derived-tensor-cohomology-triangle-rows`).
This is the universal derived scalar-extension counit on an arbitrary distinguished
A-complex triangle, with flat localization of its exact cohomology row. It has no Q,
N, t, monoidal coefficient comparison, K-flat hypotheses or coefficient boundary
calculation. The parent constructs its tensor triangle and composes the rows in Lean.
This delivery is a decomposition: one upper hole closed and one lower hole added,
before accounting for import-closure pruning. The concrete coefficient part is fully proved.
There are no remaining sorries in the item or the boundary module.

## No longer needed

Removed the item's proof-only imports
`Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor` and
`Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence`.
The former is replaced by the universal-model triangle-row interface; the latter
belongs to that new node's proof plan, rather than the parent's proof.
The new model-row plan uses the already proved `BaseDerivedExtensionResolution`
and `BaseDerivedTensorCohomologyModelMap` interfaces.
No globally unreachable module is asserted: model independence is still needed
below the new row statement, and other target branches may use the removed imports.
The public `TensorConeFiveTermExact` import remains because its concrete triangle
occurs in the unchanged signature. Its target-exactness theorem is not needed here.

## Where the brief, the DAG or earlier work was wrong

The old proof dependencies did not directly supply the required E-linear universal
model row and its counit boundary square. The new model-row node isolates this exact
missing interface. Tensorator shift compatibility itself already exists as
`HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_flipApp`; it supplies
the concrete coefficient boundary proof without a new open shift-compatibility lemma.
For first-variable shifts there is no extra homogeneous sign, as shown by
`CochainComplex.ι_mapBifunctorShift₁Iso_hom_f`.

The cached library lacked `TensorConeFiveTermExact.olean`, although the assigned source
already imports it. An unchanged copy was compiled in the sandbox solely to check
against that source dependency. It introduces no delivery diff.
LeanSearch returned Internal Server Error; logged LeanFinder, Loogle and grep searches
were used instead. Repository literature contains lists only on this machine, so the
three cited Stacks pages (06Y6, 0BYJ, 0DJA) were read online. The blueprint unit record
`sk-thm-picard-semicon` was read; its realized lists are empty, and its route is unchanged.
Edge cases checked mathematically: zero rings or complexes, zero or split cone maps,
unbounded complexes and arbitrary degrees; neither new statement asserts that the
localized comparison is invertible or that the ordinarily extended row is exact.

## New nodes

`lem-pc-base-derived-tensor-cohomology-triangle-rows` isolates the universal derived
counit row before adding a coefficient tensor comparison. Its source is Tag 06Y6,
and its docstring records the E-linearity, flat extension and boundary-compatibility
argument. It is the sole new sorry.

`lem-pc-tensor-coefficient-cone-boundary` records the proved ordinary boundary equation
for arbitrary scalar extension and coefficient map, independent of derived models
or exactness. Its proof constructs the triangle morphism and applies homology
boundary naturality. No change records or forced adaptations are needed.

## Second reading by U2

1. **Statements and interfaces.** Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are unchanged byte-for-byte. The two added theorems have narrower, independent statements: one isolates the universal triangle-row interface, and the other isolates ordinary coefficient-boundary naturality. Verdict: pass.

2. **Proof checking.** Compiled all three delivered Lean modules with `lcompile.py`; the target and boundary proofs compile without errors. The only remaining `sorry` is the named theorem `ModuleCat.exists_baseDerivedTensorCohomologyModel_triangle_rows`; there are no sorries in definitions and no forbidden declarations. Verdict: pass as a documented decomposition.

3. **Truth and strength of split statements.** The triangle-row theorem assumes exactly a distinguished A-complex triangle, arbitrary prescribed models, and flat E-to-C extension; it does not assume or claim coefficient tensor data or comparison invertibility. The boundary theorem is chain-level and has no flatness, K-flatness, derived-model, or exactness assumptions. Both are strictly smaller than the parent target and their DAG nodes and docstrings record the source and proof obligations. Verdict: pass.

4. **Pruning and route.** The parent now uses the universal triangle-row theorem, ordinary chain-map naturality, and the concrete boundary theorem. The two former proof-only imports are removed; the public signature imports are retained. The tensor, cone, exact-cohomology, and comparison route is preserved. Verdict: pass.

5. **DAG and unit consistency.** Existing target node proof/proof_deps/proof_origin entries match the delivered proof. New node records match their Lean declarations and list the documented decomposition. The unit record was checked; its realized lists are empty in the supplied blueprint, so no realized unit step is bypassed. Verdict: pass.

I changed only this report section after the worker delivery. No Lean statements, definitions, or DAG node contents were changed.
