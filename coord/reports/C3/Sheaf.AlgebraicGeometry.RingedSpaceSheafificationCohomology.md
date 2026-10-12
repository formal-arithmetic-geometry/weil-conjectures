## What changed

Proved `AlgebraicGeometry.RingedSpace.sheafification_cohomology` in
`lean/Sheaf/AlgebraicGeometry/RingedSpaceSheafificationCohomology.lean`, preserving its entire
signature, universes, visibility, and existing docstring. All existing public imports remain.

Two fully proved private helpers carry the construction. `resolvedCohomology_inverts` uses
naturality of the resolution map and two-out-of-three to obtain a quasi-isomorphism between
K-injective resolutions. Its homotopy equivalence survives the additive underlying-presheaf
functor; homology factors through the homotopy category, so localization produces the desired
presheaf-valued derived functor and its factorization.

`complexSheafificationHomologyIso` commutes exact abelian sheafification with homology, applies
the sheafification counit termwise, and commutes the exact underlying-abelian-sheaf functor
with homology. The finite-colimit preservation needed here is already proved in
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`; the natural
comparison for complexes is already proved in
`WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`. No new intermediate hole is needed.

The resolution map induces a natural homology isomorphism. Combining its inverse with the
complex-level comparison and `DerivedCategory.homologyFunctorFactors`, then applying
`Localization.liftNatIso`, constructs the derived-category sheafification comparison. Define
the requested transformation exactly by the unit formula. Its stalk map is an isomorphism.
Surjectivity and `TopCat.Presheaf.exists_germ_eq` give local representatives; injectivity and
`TopCat.Presheaf.germ_eq` give local zero detection. The last clause follows from naturality
and `TopCat.Presheaf.stalkFunctor_map_germ_apply`.

Added three proof-only imports: `Mathlib.Topology.Sheaves.Sheafify`,
`Mathlib.Topology.Sheaves.Abelian`, and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`.
The homology comparison is already available through the existing public imports. Updated the
existing node's proof, proof dependencies, and proof origin to describe the implemented route.
The unit route is preserved; its realized arrays are empty and no unit statement is bypassed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.RingedSpace.sheafification_cohomology`
(node `lem-pc-ringed-space-sheafification-cohomology`).

No `sorry` remains in the item, and no hole was added or split off. Both private helpers are
fully implemented. The complete theorem compiled successfully, without warnings.
`#print axioms AlgebraicGeometry.RingedSpace.sheafification_cohomology` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The declaration comparison reports no changed
existing statement. The proof is general in X, q, and the chosen derived-category universe;
it requires no nonempty-space or boundedness assumption.

## No longer needed

Removed the proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor`. The proof needs
abelian-group stalks and their Mathlib germ lemmas; it does not use the bundled module-stalk
functor or its linearity and functoriality proof obligations. The conceptual dependency
`def-weil-pbc-module-stalk` remains only for its underlying abelian stalk description and
Mathlib match, not for that node's bundled Lean module.

Removed `lem-weil-pbc-ringed-site-module-sheafification-exact` from the node's proof dependencies.
The implemented proof uses exact abelian sheafification and exact forgetting from module
sheaves; no module sheafification comparison is used. No import of the generic
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful` package is needed: the relevant
preservation instances are already proved in the source library.

Second reading removed the redundant proof-only direct import
`WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`: its comparison declaration
is already available through the existing imports. Removing each of the other three new
imports separately fails compilation, confirming their necessity.

All remaining direct imports supply statements, constructions, or instances actually used.
These pruning claims concern this proof, not the reachability of these modules from other targets.

## Where the brief, the DAG or earlier work was wrong

The original argument is mathematically sound. Its module-sheafification route is unnecessary
for the abelian-presheaf conclusion: exact abelian sheafification and the existing exact
forgetful functor give a shorter implementation of the same cycles/boundaries argument.
Likewise, module-stalk linearity is unnecessary for the three abelian-group germ clauses.

The local `literature/stacks-project/cohomology.tex` file is absent. Read the source statement
and proof directly at https://stacks.math.columbia.edu/tag/0BKJ; the existing source record is
retained. No statements, definitions, other modules, or target signatures were changed.

## Second reading by C3

1. **Unchanged interface — pass.** Compared the sole delivered Lean module with the
   repository using `diff`; independently extracted the existing theorem signature and
   checked byte-for-byte equality through `:= by`. Its docstring, universes and visibility
   are unchanged. No existing definition changed and no change record is needed.
2. **Kernel proof — pass.** Independently compiled the module with `lcompile.py`, without
   warnings. A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`
   and `Quot.sound` for `AlgebraicGeometry.RingedSpace.sheafification_cohomology`.
   There are no holes or forbidden declarations. The private isomorphism definition is
   constructed from explicit natural isomorphisms, not from an unproved existence witness.
3. **Split statements — pass, none.** No statement was split off and no new hole or node
   was added. Read both private helpers: the first uses naturality, two-out-of-three and
   K-injective homotopy equivalence; the second uses exact functor homology comparisons
   and the sheafification counit. Neither assumes boundedness, nonemptiness, or any extra
   hypothesis. Empty-space stalk clauses are vacuous; zero complexes and arbitrary degrees
   follow from the same functorial argument.
4. **Route and pruning — pass after one repair.** Read the resolution construction and
   existing exact-functor comparisons; searched `lean/Sheaf`, `lean/WeilConjectures` and
   Mathlib via `msearch.py` with homotopy, homology and stalk-unit terms. No existing
   declaration supplies the whole result. The proof uses existing comparisons and germ
   lemmas directly. Independently checked the unit's `realized` arrays and the source
   [Stacks Tag 0BKJ](https://stacks.math.columbia.edu/tag/0BKJ); the unit route is preserved.
   Removed the redundant proof-only `PreservesQuasiIso` import after a successful scratch
   compile without it. Separate omission checks for the other three new imports each
   failed on the expected missing declaration or instance. `No longer needed` lists the
   sole removed old proof dependency and the removed module-stalk import.
5. **DAG agreement — pass.** The node changes only `proof`, `proof_deps`, and `proof_origin`.
   Its proof steps describe localization, the exact abelian sheafification comparison,
   descent of the natural isomorphism, and the three germ clauses actually implemented.
   Checked that `proof_deps` is exactly the union of the steps' `uses`. The abelian stalk
   description is used through its Mathlib match, and finite-colimit preservation is
   supplied by the proved source-library instance, as explained in the report.

Second reading changed only the redundant proof-only import and this report; the proof
terms and all existing statements remain unchanged. Closed one original hole, added zero.
