## Worker report

This repairs returned head `4ebd803b5ab5`. The saved packet initially passed the prescribed dry run (`24d97326e7`), but inspection confirmed the maintainer's H7b/H3 findings: its first conjunct was only a projection-composition identity, and its second used the exceptional right adjoint of `u` instead of exact inverse image and the sum/evaluation adjunction. The repaired module restores the original DAG statement, unchanged in natural language. The rejected `statement_change` is removed. No correction of the mathematical node is needed.

The module states `AlgebraicGeometry.Etale.tensorMateEtalePrecomp` with one postponed proof. Its helper `tensorMateEtalePrecompLocalityIso` has real data: conjugate the recorded `etaleAmbientLeftComparison`, then invert the resulting right-adjoint isomorphism. That comparison is built from the graph-normalized compact-support-to-sum comparison, the proper/open tower compositor, and refinement comparison. The adjunction on the étale factor is literally `(etaleLowerShriekUpperStarAdjunction (ModuleCat A) u inferInstance).mapDerivedCategoryAdjunction`.

Hypothesis and object correspondence:

| Node | Lean |
| --- | --- |
| Finite commutative coefficient ring | `(A : Type (v + 1)) [CommRing A] [Finite A]` |
| Schemes and `h = f ∘ u` | `{U X S : Scheme.{v}}`, `u : U ⟶ X`, `f : X ⟶ S`, with `u ≫ f` used throughout |
| Noetherian schemes | `[IsNoetherian U] [IsNoetherian X] [IsNoetherian S]`; the class means locally Noetherian and quasi-compact |
| Separated étale finite-type `u` | `[Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]` |
| Separated finite-type `f,h` | The corresponding three instances for `f` and `u ≫ f` |
| Compactifiable `f,h` | `[HasCompactification f] [HasCompactification (u ≫ f)]`; no compactification hypothesis on `u` is added |
| Entire ordinary derived categories | `DerivedCategoryModule A T`, the unbounded derived category of `Sheaf T.smallEtaleTopology (ModuleCat A)` |
| Exact inverse image | `(a)^*[ModuleCat A].mapDerivedCategory`; `leftDerivedUpperStarIsoMapDerivedCategory` inserts the canonical identification when using the upstream projection |
| Derived tensor and coefficient unit | `derivedTensor (ModuleCat A) T` and `𝟙_ (DerivedCategoryModule A S)` |
| Right adjoints and dualizing objects | `R(a)^![ModuleCat A]` and its value on the coefficient unit; adjunctions are `rightDerivedUpperShriekAdjunction` |
| Normalized comparisons | `N : EtaleCompactSupportNormalization A`, used in `etaleAmbientLeftComparison A N u f` |

`N` is universally quantified normalization data, not a new existence assumption. The imported theorem `nonempty_etaleCompactSupportNormalization` supplies it for every finite commutative `A`. Its graph-section and homotopy-representative fields specify the maps; it cannot be an arbitrary isomorphism, negation, or a choice from a bare `Nonempty` of unspecified maps. The theorem holds for every such normalized family, just as the recorded locality theorem does. The finite-coefficient instance supplies existence of the exceptional adjoints, so the returned packet's three extra `IsLeftAdjoint` hypotheses have also been removed.

Clause correspondence:

1. **Definition of each canonical alpha.** Each of the two `homEquiv _ K` expressions transposes exactly the source's displayed composite. First use exact-to-left-derived inverse image in the first tensor factor and signed symmetry to place the factors in the upstream order. Then use the inverse of `projectionMap`, whose actual invertibility proof is `isIso_projectionMap_of_finite A a`. The second signed symmetry puts `K` first; tensor the exceptional counit at `𝟙_` with `K`, then apply `derivedTensorRightUnitor`. These are alpha_f and alpha_h, written out without introducing a second definition of the downstream `smoothTensorDualityMap` notion.
2. **Canonical lambda.** `tensorMateEtalePrecompLocalityIso A N u f` has source `R(f)^! ⋙ u^*` and target `R(u ≫ f)^!`. It uses the exact sum-extension/evaluation adjunction, rather than the exceptional adjunction for `u`. Its construction uses the same normalized left comparison as the dependency's locality statement.
3. **Tensor-mate equality.** The first conjunct quantifies every `K : DerivedCategoryModule A S`. Its left side is `theta.hom ≫ u^*.map alpha_f ≫ lambda.hom.app K`. Its right side applies the inverse pullback-composition comparison in the first factor, then `1 ⊗ lambda.hom.app (𝟙_)`, then alpha_h. The common source is `u^*f^*K ⊗ u^*omega_f`, and the common target is `h^×K`. This restores the equality omitted in the returned delivery; it does not assert that alpha is invertible.
4. **Sum-counit normalization.** The second conjunct quantifies every unbounded `B`. It states `c_(u^*f^×B) ≫ Rh_!.map lambda_B ≫ epsilon_h,B = Rf_!.map e_(f^×B) ≫ epsilon_f,B`. Here `c` is `etaleAmbientLeftComparison` and `e` is explicitly the counit of the descended sheaf sum/evaluation adjunction. Thus it is the fold/evaluation counit and has exactly the compact-support identification required in the node.

Dependency declarations read and used (module names abbreviated only by the common prefix `WeilConjectures.SixFunctors.Etale`):

- `.Derived.Coefficients`: `DerivedCategoryModule` and its coefficient unit; `.Derived.Tensor`: `derivedTensor`.
- `.UpperLowerStar.Defs`: `upperStar`; `.Derived.LowerShriek`: `rightDerivedLowerShriek`, definitionally the chosen-compactification candidate.
- `.Derived.UpperShriek`: `rightDerivedUpperShriek`, `rightDerivedUpperShriekAdjunction`, and `isLeftAdjoint_rightDerivedLowerShriek` for finite coefficients.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`: the fixed-compactification adjoint-existence theorem. The ordinary finite-coefficient interface is used without adding a hypothesis.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`: `etaleAmbientLeftComparison` and the counit characterization in `existsUnique_etaleAmbientAdjointLocalityIso`. Its underlying degreewise adjunction is used through the exact sheaf adjunction named below.
- `.LowerShriek.EtaleMap`: `etaleLowerShriek`, `etaleLowerShriekUpperStarAdjunction`; its degreewise descent is the sum/fold adjunction.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`: `EtaleCompactSupportNormalization.comparison` and `nonempty_etaleCompactSupportNormalization`.
- `Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor`: `etaleSumExtensionTensorPullbackIso`; its full signature and representative construction were read. It transports the canonical derived tensor-pullback comparison to exact inverse image. This also imports the recorded generic ringed-topos comparison, `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`: `unboundedEtaleUpperStarCompIso`, together with the normalized compositor description used by the left comparison.
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`: `derivedTensorSymmetry`; `.Derived.TensorStructure`: `derivedTensorRightUnitor`.
- `.Derived.ProjectionFormula`: `projectionMap` and `isIso_projectionMap_of_finite`. The inverse has this explicit existing proof, not a new assumption or a postponed helper theorem.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`, with its composite-counit formula; `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`.
- Mathlib's `Scheme`, `Etale`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsNoetherian`, and the upstream `HasCompactification` are reused. Proof-only modules for proper projection, tensor composition, support-map compatibility, the generic ringed tensor comparison, open tensor, and Nagata are imported.

The statement dependencies gain the already recorded nodes `lem-asd-etale-compact-support-normalization`, `lem-asd-etale-sum-extension-tensor`, `lem-kun-tensor-sym`, `lem-kun-tensor-unit`, and `lem-kun-inverse-image-monoidal` because their declarations now occur explicitly in the signature or canonical locality helper. No new node or dependency repair is introduced.

Edge cases checked by reading the actual domains and constructions: identity `u` (the graph-normalized identity, with its canonical unit comparisons, is included); empty `U` (sum extension is the empty sum and the fold is the zero map); a disjoint union étale cover (the counit folds the sheet summands); zero `K` and arbitrary unbounded `K`; and the zero coefficient ring. No nonempty, nonzero, boundedness, constructibility, finite-Tor, smoothness, orientation, or invertible-exponent assumption occurs. The coefficient universe is the existing `ModuleCat.{v+1}` size convention for `Scheme.{v}`, not an extra equality between independent mathematical universes.

Searches performed:

- `msearch.py ... leanfinder "canonical exceptional pullback tensor mate compatible with etale precomposition"`: eight generic pullback/over-category hits, no statement of this ordinary étale tensor-mate equality.
- `msearch.py ... loogle "CategoryTheory.conjugateIsoEquiv, CategoryTheory.Adjunction.homEquiv"`: zero hits for that combined query.
- `msearch.py ... grep "tensorMateEtalePrecomp|conjugateIsoEquiv" CategoryTheory/Adjunction`: twelve generic adjunction-mate declarations, supplying construction tools but no geometric theorem.
- `rg` in upstream `WeilConjectures`, the shared `lean/Sheaf`, and `dag/lean_names_upstream.json`: the downstream `smoothTensorDualityMap` defines the canonical alpha; no existing declaration states the present compatibility. Its definition was read to check the two expanded transposes. Importing its module would reverse the intended dependency from `thm-asd-smooth-tensor` to this lemma, so its defining expression is used directly in the theorem instead of making a duplicate definition or an import cycle.
- `rg` and full source reads of the recorded comparison, normalization, sum tensor, symmetry, tensor structure, projection formula, and adjunction declarations; `scompile.py --source Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality` checked the published source. A compiler diagnostic exposed that the live descended-adjunction helper has the generic coefficient-category interface; using the underlying sheaf adjunction's exact descent resolves it with the same sum/fold counit.

No `STATEMENT-DISPUTED` remains. The natural-language statement, source, proof, and proof dependencies are retained from current main. The rejected comparison-only correction is not retained. The node's `lean.statement` is extracted verbatim from the theorem keyword up to `:=`, including newlines, repairing H2.

## Second reading by NS

This is the author's second pass; the maintainer supplies the independent review. I reopened the original DAG node, the returned packet, the blueprint proof paragraph, and the repaired Lean file together.

The returned first conjunct was `compactSupportProjectionMap` composition rather than the node's alpha equality; the first conjunct now contains both explicit alpha transposes, `u^*.map`, and lambda at `K` and at the coefficient unit. I checked both maps have the common source `u^*f^*K ⊗ u^*omega_f` and target `h^×K`: `etaleSumExtensionTensorPullbackIso.hom` is on the left and `unboundedEtaleUpperStarCompIso.inv` is on the right, in the correct directions. Each alpha includes the exceptional counit at the unit and the right unitor, which were absent from the returned statement.

The returned right-adjoint comparison used `R(u)^!`; the repaired helper's source is literally `R(f)^! ⋙ u^*.mapDerivedCategory`. Its conjugated left adjunction is built from the sum/evaluation sheaf adjunction and the exceptional adjunction for `f`. In the second conjunct I checked the left comparison is evaluated at `u^*f^×B`, its next map is `Rh_!(lambda_B)`, and its final map is epsilon_h. The right side is exactly `Rf_!(fold_(f^×B))` followed by epsilon_f. Thus the old generic exceptional-adjoint counit tautology has been replaced by the required étale sum normalization.

I matched every geometric hypothesis in the table above: finite commutative `A`, the three Noetherian schemes, separated étale finite-type `u`, separated finite-type compactifiable `f,h`, and no restrictions on `K,B`. I removed the returned packet's additional compactification of `u` and explicit left-adjoint existence binders. I also checked that `N` carries the graph and representative normalizations and has an already recorded existence theorem; it does not stand for a freely chosen natural isomorphism.

For H8 I checked the module and both declarations have source/blueprint docstrings. The theorem docstring now contains all seven steps of the existing DAG proof, including the two transpose calculations and the use of the sum-tensor counit identity. For H2 the JSON signature is now the literal multiline signature from the file. This concrete second pass replaces the returned H11 placeholder.

Citer audit for removal of the rejected correction: `rg -l '"lem-asd-tensor-mate-etale-precomp"' dag/nodes` finds the item and exactly two consumers. `thm-asd-smooth-tensor` still uses the original tensor-mate equality for its local isomorphism test; that equality is restored, so its use holds. `lem-trf-ambient-diagonal-purity-base-change` still uses the same canonical tensor-mate normalization in its ambient smooth argument; the original assertion is retained, so its use holds. Neither consumer is edited.
