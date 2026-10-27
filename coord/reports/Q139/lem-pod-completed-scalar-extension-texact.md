## Worker report

Stage 2, Q139, lem-pod-completed-scalar-extension-texact. The live node is already
split and reviewed (Q58); this delivery does not re-split it or alter its statement,
proof, dependencies, status, source or review. The previous attempt confused this
stage-2 task with a stage-1 re-splitting. There is no repair note for this item.

The new module `Sheaf.Paper.CompletedScalarExtensionTExact` states exactness of
ordinary completed-coefficient sheaf extension in two named finite-limit/finite-colimit
clauses, and the main theorem `WeilConjectures.podCompletedScalarExtension_tExact`.
All three proofs are `sorry`. Each helper is a clause of this same DAG statement,
not a new independent notion; all three declarations are recorded in lean.declarations.
The docstrings contain the corresponding complete natural-language proof plans.
No new definition, dependency repair, statement correction or disputed statement is needed.

Hypotheses and objects, clause by clause:

- The prime is `(l : ℕ) [Fact l.Prime]`.
- The finite extensions of Q_l are `E L : Type u` with `Field`, `Algebra ℚ_[l]`,
  and `FiniteDimensional ℚ_[l]` instances. The inclusion is `ι : E →ₐ[ℚ_[l]] L`;
  it is injective since its source is a field. The existing coefficient datum
  supplies the spectral absolute values, integer rings and chosen uniformizers.
- The base is `Y : AlgebraicGeometry.Scheme.{u}`. `[AlgebraicGeometry.IsNoetherian Y]`
  is noetherian affine-local structure plus compactness, equivalently a finite
  noetherian affine cover; `_hdim : ∃ n : ℕ, topologicalKrullDim Y ≤ n` is the finite
  chain bound. `_hinv : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)` says exactly
  invertibility in each local ring. There is no finite-field base datum.
- The small site is `Y.ProEt` with `Scheme.ProEt.topology Y`, used by the imported
  completed coefficients and module categories. The object and morphism universes
  of this site remain u+1 and u. No site universe equality is imposed. Coefficient
  fields and schemes use the same common ambient universe as the recorded detailed
  constructibility definition. The completed coefficients and module sections live
  in u+1, not the smaller site morphism universe.
- R and S are the recorded `completedIntegralCoefficientSheafUnrestricted l E Y`
  and its L analogue, inverse limits of positive quotient-ring sheaves (index n
  represents exponent n+1). The canonical map is `completedCoefficientMap l E L ι Y`.
- C_E and C_L are exactly `sfIntegralConstructibleCategory l E Y` and its L analogue,
  full subcategories given by `sfIntegralConstructible`, including derived
  completeness, every positive constructible reduction, and a common finite interval.
- The strict-tower functor restricted to these categories is the existing
  `sfConstructibleIntegralScalarExtension (l + 1) l (Nat.ne_of_lt (Nat.lt_succ_self l))
  E L ι Y`. Its object and morphism maps are those of `integralScalarExtension`.
  This is definitionally the equal-input-universe instance of the recorded
  `integralScalarExtensionOfUniverses`, not a replacement or chosen unrelated functor.
  The pre-existing restricted interface has a redundant p argument with l ≠ p.
  Filling it by p=l+1 and the library proof of l<l+1 adds no hypothesis whatsoever,
  makes no characteristic assumption on Y, and its proof is not a new theorem.
- Ordinary sheaf extension is `completedOrdinaryScalarExtension l E L ι Y`, the
  sheafified tensor functor in the recorded change-of-rings universal datum. Its
  additivity is already recorded. The two new instance theorems state preservation
  of finite limits and finite colimits, precisely exactness between abelian categories.
- Ordinary derived extension is `completedDerivedScalarExtension l E L ι Y`.
  The existential natural isomorphism `e` identifies it with the exact ordinary
  functor's `mapDerivedCategory`. For every complex P, the equality
  `e.hom.app (Q.obj P) ≫ mapDerivedCategoryFactors.hom.app P = completedScalarCounit ... P`
  fixes the identification by its universal counit; hence it is the actual termwise
  derivation, not an arbitrary isomorphic functor.
- `ε` is an isomorphism of functors into ambient D(S), from restricted strict-tower
  extension followed by the full inclusion to the inclusion followed by the exact
  derived sheaf functor. The equality
  `ε.inv.app K = e.inv.app K.obj ≫ (completedScalarComparison ...).app K.obj`
  fixes it to the published canonical strict-cone comparison χ. Thus χ itself is
  invertible on every constructible K. Naturality is part of the natural isomorphism.
- The existential `_σ : T.CommShift ℤ` binds the shift comparison used by
  `T.IsTriangulated`. `NatTrans.CommShift ε.hom ℤ` requires compatibility with the
  inherited full-subcategory inclusions and the ordinary exact functor's shift.
  Solving this equality gives exactly χ_{K[n]} inverse, the ordinary shift, then
  χ_K shifted. This records the node's induced shift comparison and preservation
  of distinguished triangles. It does not merely assert unstructured exactness.
- For every `a b : ℤ` with `a ≤ b`, and every K in C_E, the two implications
  `DerivedCategory.IsLE K.obj b → DerivedCategory.IsLE (T.obj K).obj b` and
  `DerivedCategory.IsGE K.obj a → DerivedCategory.IsGE (T.obj K).obj a`
  are the separate standard cohomological bound assertions. These are the ambient
  bounds, which the imported integral characterization and t-structure results
  identify with the restricted integral standard bounds. There is no assumption
  that K has both bounds: each implication is independent.
- K is arbitrary in the recorded full category. No flatness of K, of its
  cohomology, or of finite coefficient quotient maps is assumed.

Dependency declarations used/read:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports the coefficient
  datum: `Padic.coefficientExtensionAbsoluteValue`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, and `coefficientExtensionRing`; the primary
  `finite_coefficientExtensionRing` supplies positive-level finiteness.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology` give the actual small site.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, via its public imports:
  `WeilConjectures.completedIntegralCoefficientSheafUnrestricted`,
  `integralConstantToCompletionOfUniverses`; completions are the existing limits.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`
  and `sfIntegralConstructibleCategory`, the current recorded detailed definition.
- `Sheaf.Paper.IntegralTStructure`: `AlgebraicGeometry.Scheme.pbcIntegralTStructure`
  and `pbc_integral_tstructure`; `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization` and `integralStratifiedPerfectDetailed`
  identify the categories and their ambient bounds in the proof plan.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`
  and `integralScalarExtensionComparisonOfUniverses`; imported publicly by
  `FiniteFreeCompletedScalarComparison`. The restricted functor imports the
  definitionally identical equal-universe `IntegralScalarExtension` interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, its Q and
  cohomology; `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `IsLE`, `IsGE`,
  `isLE_iff`, `isGE_iff` and the standard t-structure by bounded representatives.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence theorem,
  with the actual termwise tensor, universal counit and K-flat computation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  is the general-site `SheafOfModules` presentation; its abelian structure is Mathlib's.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedOrdinaryScalarExtension`,
  `completedDerivedScalarExtension`, `completedScalarCounit`, `completedScalarComparison`,
  and `finiteFreeCompletedScalarComparison`. The canonical map is normalized on K-flat
  representatives to quotient tensor projections and zero shifted-product component.
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`:
  `sfIntegralScalarExtension_constructible`, `sfConstructibleIntegralScalarExtension`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`:
  `sfIntegralConstructible_isClosedUnderIsomorphisms` and
  `sfIntegralConstructible_isTriangulated`; these give the inherited category structures.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `Functor.mapDerivedCategory`,
  `mapDerivedCategoryFactors` and its triangulated/shift instances are the recorded
  exact-functor-derived-factorization Mathlib leaf.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; and the proof import
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` retains the recorded
  sheaf tensor construction. All available statement/proof dependency modules are imported.

Source read: the live node's full statement and six proof steps; every stmt_deps
statement and Lean/mathlib record; the modules above (signatures and docstrings);
main-20261015 `prop-constructible-truncations.proof.md`, its integral paragraph and
finite-scalar-extension sentence. The extracted node is already the corrected
finite-free argument, so the blueprint's unrelated problematic assertions about
truncation functors being triangulated are not reproduced.

Edge cases checked mathematically: K=0 (all bounds hold, empty cohomological support);
Y empty (invertibility vacuous and the constructions are the recorded sheaf categories);
L=E with identity inclusion (χ is the derived-completeness map, not ambient identity
on arbitrary incomplete objects); ramified extensions and torsion cohomology such as
O_E/t (S is finite free, so exactness does not require cohomology flatness); a=b;
negative bounds; an object satisfying only one of the asserted bounds. The ambient
isomorphism e uses exactness on all sheaves, but the completed comparison ε is
restricted to C_E: the false comparison on all incomplete derived inputs is not asserted.

Searches (msearch.py results retained in searches.jsonl):

- LeanFinder, “Completed integral scalar extension of constructible pro-etale complexes
  preserves standard cohomological bounds”: eight generic bounded-complex hits,
  including `DerivedCategory.isGE_Q_obj_iff` and `isLE_Q_obj_iff`; no exact item match.
- Loogle, `CategoryTheory.Functor.mapDerivedCategory`: twelve hits, including exact
  derived functor/shift/triangulated declarations, reused here. No strict-tower comparison.
- LeanSearch, “Exact functor on sheaves induces t exact functor on derived categories”:
  eight hits, including `mapDerivedCategory` and `mapHomologicalComplexUpToQuasiIso`.
  These are the generic exact-functor leaf, not the completed constructible statement.
- msearch grep, `completed.*scalar.*(exact|trunc)|scalar.*extension.*t.exact`: zero hits.
- Direct rg in lean/WeilConjectures and lean/Sheaf for the item id and completed-scalar
  t-exactness names: no existing declaration. The already published finite-free
  comparison and constructible restriction are reused, with no second definition.

Validation: prescribed scompile.py passed the final module as both a sandbox module
and its actual library path, with no errors or warnings. No global build, direct git
mutation, live-source edit or local compiler command was used.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
