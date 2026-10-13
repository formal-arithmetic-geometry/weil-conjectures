## What changed

Replaced the hole in `AlgebraicGeometry.Etale.exists_etaleCE_coherent_first_page_lifts` with a
compiled reduction. It chooses the coherent quotient-page presentations, applies the existing
augmented Cartan–Eilenberg comparison, invokes the totalization lemma, and invokes quotient-page
descent; `Classical.choose` assembles the resulting sequence maps while retaining their lift
witnesses. Added the two proof-only modules `Sheaf.Paper.EtaleCEQuotientPageDescent` and
`Sheaf.Paper.EtaleCETotalizeAugmentedComparison`, each with its named intermediate theorem.
The assigned theorem's signature and public imports are unchanged.

## Proved and sorry left

Closed the assigned theorem hole `exists_etaleCE_coherent_first_page_lifts` by the reduction above. Added two lower holes, so this is a decomposition, not a complete proof (one closed, two added).
The following intermediate theorems remain as intentional decomposition holes:

- `exists_etaleCE_quotient_page_descent` in node `lem-weil-pbc-ce-quotient-page-descent`;
- `etaleCE_totalize_augmented_comparison` in node `lem-weil-pbc-ce-totalize-augmented-comparison`.

Both are public theorems with source and proof descriptions in their docstrings; no definition
contains `sorry`.

## No longer needed

The assigned proof no longer directly needs `Sheaf.CategoryTheory.CartanEilenbergFunctorial`,
`Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`, or
`Sheaf.Algebra.Homology.FilteredComplexZBDescription`; their planned spectral-object and
filtered-cycle constructions are bypassed by the coherent quotient-page descent interface.
The proof-only imports retained in the two intermediate modules are exactly those needed by their
statements. The stationary-page module is used for the quotient realization and representative
map interfaces.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was blocked because the shared compiled cache lacked
`EtaleCEStationaryPageNaturality.olean`. Compiling the dependency in the sandbox first and then
compiling all four modules resolves that tool failure; no dependency was restated in the delivery.
The route is a decomposition of the DAG plan: coherent page descent and totalization are exposed
as strictly smaller supplied-comparison statements.

## New nodes

`lem-weil-pbc-ce-quotient-page-descent` is stated in
`Sheaf.Paper.EtaleCEQuotientPageDescent` and factors coherent quotient-page construction and
naturality from the supplied augmented comparison.

`lem-weil-pbc-ce-totalize-augmented-comparison` is stated in
`Sheaf.Paper.EtaleCETotalizeAugmentedComparison` and factors totalization, the augmentation
square, summand formulas, and filtered step restrictions from a supplied comparison.

## Second reading by C4

1. **Visible changes and signatures.** Compared the delivered target module with the repository version. The target theorem signature is unchanged byte for byte; only its proof and proof-only imports changed. The two added modules contain the split theorem signatures recorded in their DAG nodes.

2. **Compilation and axioms.** Compiled all four sandbox modules with `lcompile.py --all`; they compile successfully. The target retains `sorryAx` through the two intentional split theorems and upstream dependencies, including augmented CE comparison; no definitions contain `sorry`, and no forbidden declarations were added.

3. **Statements and split nodes.** Searched the repository for the two new declaration names and found no prior declarations. Their statements are strictly smaller interfaces: quotient-page descent consumes supplied comparison and totalization consumes supplied augmented comparison; neither restates the assigned target. Docstrings give source and complete construction arguments, and matching DAG nodes record the declarations and dependencies.

4. **Route and pruning.** The proof uses the supplied augmented comparison, totalization, and quotient-page descent route while retaining the stationary-page realization required by the unit. Removed proof-only imports for the bypassed direct spectral-object and filtered-cycle construction; the report's no-longer-needed list matches the changed proof dependencies.

5. **DAG agreement.** Checked the Lean declarations against both new node files and the assigned node. The proof dependencies and origins describe the imports and calls actually used; the unit route remains realized through the stationary-page and quotient-page interfaces.

Second-reader changes: scoped the unused-variable linter setting before the existing heartbeat setting, preserving the signature; corrected the assigned node, whose proof fields still described the old route; and expanded this record. Local dry-run delivery passes.

This delivery closes the assigned hole by reduction and adds two named holes, so it is a decomposition (net holes: -1), not a completed mathematical proof. The pre-existing stationary-page module is an unchanged local compile dependency. Independent alternate searches found Mathlib total.map and ιTotal_map, which supply summand functoriality but do not supply the augmented filtered etale comparison or coherent quotient pages. Zero complexes, empty diagonals and identity/zero comparison maps introduce no extra assumptions. The unit realized arrays are empty in the repository, and this delivery does not alter them.

Additional old proof dependencies no longer directly used by the assigned node: lem-sp-cartan-eilenberg-exists, thm-sp-if-e1, lem-weil-pbc-sheafH-ext-derived-comparison, def-weil-pbc-termwise-hypercohomology-presentation, thm-sp-spectral-object-yields, lem-sp-filtered-complex-ZB-description, lem-sp-filtered-complex-associated-spectral-sequence-construction, lem-sp-filtered-complex-page-differential, lem-weil-pbc-cartesian-eilenberg-functorial, def-weil-pbc-inverse-image, lem-weil-pbc-ce-total-sections-comparison, def-weil-pbc-cohomology-pullback. Several remain transitive or statement dependencies; no whole-closure pruning is claimed.
