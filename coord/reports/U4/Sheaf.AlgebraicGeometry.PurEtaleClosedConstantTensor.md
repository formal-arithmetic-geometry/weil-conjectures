## What changed

Filled `AlgebraicGeometry.Etale.closedConstantTensor` with a complete proof from the named canonical flat degree-zero compatibility result. The ordinary pullback adjoints are identified with finite base change. Unit-section epimorphisms give ordinary associativity, symmetry, identity/composition, and the pullback square. Unit/zero geometric stalks give tensor invertibility and flatness, including zero coefficients and empty supports. The final two derived coherence structures follow from the separate generic pairing result.

The new module `Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility` states that source result for arbitrary flat degree-zero sheaves and arbitrary ordinary pairing diagrams. Its real map constructors retain the source library's canonical tensor comparison and inverse-image comparison. Exposing these generic constructors avoids costly comparisons after specializing coefficients: the complete item compiled in 20.3 seconds, versus 57.7 seconds before this refactor. No source-library declaration or target signature changes.

Five change records document definitionally identical presentations of the constant unit and the three canonical map constructors. The new module is a public import because those constructor bodies are used by definitions; the other new imports are private proof imports. The original three consumer modules compile without proof or statement edits: SupportedCup (17.6 s), PurityFramePrincipalBoundary (23.7 s), and PurityFrameClass (13.9 s). The finalized, pruned item compiles in 22.3 s and the new source module in 21.6 s.

## Proved and sorry left

Original hole closed: `AlgebraicGeometry.Etale.closedConstantTensor` (node `lem-pur-etale-closed-constant-tensor`). The existing proved `closedConstantModule_flat` remains proved, now reusing the unit/zero stalk lemmas of the proof. There is no `sorry` in the item module.

One hole added and left: `AlgebraicGeometry.Etale.etaleSingleFunctor_monoidalCompatibility` (node `lem-pur-etale-single-functor-monoidal-compatibility`). It is a separate canonical derived tensor result with arbitrary sheaves and pairings, not the closed-support statement under another name. The item proves its ordinary isomorphisms and coherence independently; only the passage to derived coherence uses this source result. This delivery is a decomposition: one original hole removed and one strictly lower source hole added, net zero holes. No data is selected from its unproved proposition.

Proof work toward the source result established the degree-zero cochain tensor comparison, all its lax braided axioms, compatibility with an additive monoidal exact functor, and generic associativity/symmetry after localization in scratch compilations. The remaining issue is joining these APIs to the specified canonical inverse-image comparison; experimental flat-pairing interface proofs still trigger expensive definitional comparisons. Those scratch files are not delivered as unproved private helpers or extra library modules.

## No longer needed

Removed direct proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`.
- `Sheaf.Paper.RingedTopoiTensorComparisonData`.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`.
- `WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant`.
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`.

The following old direct proof dependencies are replaced by the unit-section argument, finite base change, and the canonical flat degree-zero pairing lemma:

- `lem-weil-pbc-constant-module-locally-constant`.
- `def-weil-closed-immersion`.
- `lemma-openclosed-stalk-lowerstar`.
- `lem-weil-pbc-constant-sheaf-geometric-stalk`.
- `lem-weil-pbc-constant-module-sheaf-underlying`.
- `lem-weil-pbc-inverse-image-stalk-germ`.
- `lem-pod-etale-stalk-tensor-scalar`.
- `lem-weil-pbc-geometric-point-open-or-closed`.
- `lem-weil-pbc-canonical-ringed-tensor-comparison-construction`.
- `def-weil-pbc-canonical-ringed-tensor-comparison`.
- `prop-weil-pbc-geometric-stalks-exact`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `def-pc-tensor-complex-sheaves`.

Definitions still in `stmt_deps` retain their mathematical role even when their attached module is no longer a direct proof import. These removals describe this item's proof; they do not assert that a dependency is globally unreachable through other source-library declarations. No module is withdrawn and no adopted declaration is removed. Obsolete top-level `tool_uses` entries are removed in their original order; the inverse-image composition approval remains. The unit `sk-prop-a1-kummer` has no realized node here, and its route is preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan reconstructs pointwise tensor products and general ringed-topos derived tensor descent. Those constructions are unnecessary for these already specified maps. The constant source is the tensor unit, restriction is epimorphic by the open-closed exact sequence, and closed immersions already satisfy finite base change. These give a shorter proof of the ordinary assertions. The plan's last step also needs a precise compatibility statement for the *canonical* single-functor comparisons; existence of a derived tensor alone does not supply the displayed coherence equalities. The new source lemma states exactly that missing categorical compatibility. No mathematical statement is marked disputed and no target hypothesis or conclusion changes.

## New nodes

`lem-pur-etale-single-functor-monoidal-compatibility`: Stacks Tags 06YQ and 06YU, the canonical flat degree-zero tensor model, and exact inverse image. Its three fields transport arbitrary ordinary associativity, symmetry and pullback pairing diagrams to the specified derived diagrams. The docstring and node contain the complete argument through the sole degree-zero tensor summand, the homotopy quotient, localization, and the tensor/counit equations. The zero-object and empty-scheme cases require no extra hypothesis. Its statement is strictly separate from the support geometry proved in the item.

Change records:

- `coord/changes/u4-constantModuleSheaf.md`.
- `coord/changes/u4-closedConstantFlatModelMap.md`.
- `coord/changes/u4-closedConstantDerivedPullbackMap.md`.
- `coord/changes/u4-closedConstantDerivedPairMap.md`.
- `coord/changes/u4-closedConstantRestriction.md`.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
