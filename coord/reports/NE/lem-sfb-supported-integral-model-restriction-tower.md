## Worker report

This delivery states `supported_integral_model_restriction_tower` and defines its canonical strict-tower data. The theorem proof is `sorry`; the accompanying eight-step proof docstring follows the node's proof dependencies. Definitions have genuine data, including actual scalar endomorphisms, cokernels, transition maps, sections restrictions and derived functors. No target statement changes.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; the finite coefficient extension is `(E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]`. The preliminary ambient algebraic closure and unused finite ring in the node's general coefficient convention do not enter this integral sublemma: its actual ring is precisely the two cases in `hR`, with their specified topology. A continuous ring equivalence with continuous inverse is used to express these two rings without duplicating the construction. It permits every uniformizer, not merely a distinguished choice. The maximal-ideal equation in the second case is exactly the uniformizer condition.
- `Modules R X` is the existing ordinary internal module category over `condensedRingObj (Profinite.continuousCoefficientRingObj R) X`. The continuous coefficient construction uses all continuous maps, and no completion of the module category is introduced. `condensedModuleSections` is the existing actual internal module sections functor; derived sections are its `rightDerivedFunctor`.
- `T`, `T₀`, `S : Scheme.{u}`, compactness and quasi-separatedness binders, and `[IsClosedImmersion t]` render the qcqs closed pair. The torsion hypothesis is `ht`, using the existing `Scheme.IsTorsionAbelianSheaf` and the actual `Etale.cohomologyMap t F q`, for every natural degree. There is no uniform annihilator or invertibility/Noetherian hypothesis.
- `tree : QcqsOpenClosedTree T` and `p : tree.Path S` encode the finite chain by the existing interface. `p.extension` uses actual lower-shriek on an open edge and lower-star on a closed edge. Complementary branches carry no extra mathematical condition. The root path is the identity; open edges and closed complements are quasi-compact by the recorded tree definition.
- `Models R S` is the full subcategory on the existing `HasFiniteConstantLocalModel`. Its scalar model is finitely presented and may have torsion. Its morphisms are all actual module maps, with no image-presentation requirement.
- `quotient` is the ordinary cokernel of the actual scalar power; `quotientStep` is induced by the identity on the source, `quotientTower` is the strict inverse sequence, and `quotientUnit` is the actual quotient augmentation. Index `n : ℕ` denotes the positive level `n+1`. `supportedQuotients` and `supportedUnit` apply the actual path extension, with its actual action on maps.
- `Coordinates` gives exact additive ordinary scalar coordinates with an underlying abelian sheaf isomorphism and explicitly normalized sectionwise scalar action. These are existential conclusion data, not hypotheses on the input module.
- `Descent.functor` supplies the entire strict étale tower, naturally in the full category of finite models. `identification` is the marked comparison inverse image. `quotientAction` says precisely that the indicated power of the scalar acts by zero, equivalently that the module action factors uniquely through the quotient ring. `ellPower` is an annihilator for each finite-level sheaf. `unique` states uniqueness up to the unique marking-preserving natural isomorphism.
- `PullbackCoordinates` uses the canonical normalized direct image on underlying sheaves and its adjunction mate. `RestrictionComparison.identification₀` supplies the second marked inverse-image identification; `pullback_normalization` fixes it by the canonical comparison square and that mate.
- `integralArrows` uses actual derived restriction; `etaleTowerRestriction` derives actual sections restriction on strict module towers. `etaleArrows` then applies total right derived inverse limit from the derived category of strict abelian towers to both endpoints and the restriction arrow. It never forms a diagram merely in the derived category.
- `RestrictionComparison.iso` is a natural isomorphism in the functor category with values in `Arrow (DerivedCategory Ab)`. Thus its components commute with the actual horizontal restrictions, and naturality includes every actual module map.
- The endpoint normalization equations compare this isomorphism with `augmentedSections`, constructed from the actual strict quotient augmentation using the derived constant/limit adjunction. The finite comparison uses the actual étale/pro-étale adjunction unit and the marked identifications. Both source and target equations are retained.
- Resolution existence is recorded in the conclusion on the same ordinary categories and strict towers. These are proof data needed to elaborate universal derived functors, not extra scheme/coefficient assumptions.

Edge cases: positive indexing includes the first quotient; zero scalar models and empty schemes are allowed by the full category and all constructions; finitely presented torsion models are allowed without flatness; the root path gives the empty/identity chain; finite mixed paths use the same actual extensions. No assertion is made about completeness or finite presentation of images. An arbitrary locally torsion test sheaf is retained in `ht`.

Dependency declarations read and reused:

- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`, `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `def-sfb-condensed-module-sections`: `Sheaf.Paper.CondensedQcqsPushforwardContinuity`, `AlgebraicGeometry.ProEtale.condensedModuleSections`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, `AlgebraicGeometry.Scheme.smallEtaleTopology`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: `None`, `None`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-pbc-scheme-conventions`: `None`, `None`.
- `def-weil-pbc-torsion-etale-sheaf`: `WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf`, `AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf`.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.cohomology`.
- `def-weil-pbc-cohomology-pullback`: `Sheaf.AlgebraicGeometry.ModuleDerivedCohomologyPullback`, `AlgebraicGeometry.Etale.abelianDerivedCohomologyPullback`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-sfb-module-open-lower-shriek`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`.
- `def-sfb-module-lower-star`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`, `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`, `AlgebraicGeometry.ProEtale.IsConstantModelConstructible`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-site-comparison-morphism`: `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, `AlgebraicGeometry.Scheme.proEtaleSiteComparison`.
- `def-weil-inverse-system`: `Mathlib.CategoryTheory.Functor.OfSequence`, `CategoryTheory.Functor.ofOpSequence`.
- `def-weil-derived-limit`: `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`, `CategoryTheory.IsDerivedLimit`.
- `def-sfb-qcqs-open-closed-tree`: `Sheaf.Paper.QcqsOpenClosedTree`, `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree`.

The node's available proof dependency modules are plain imports, while statement constructions are public imports. The proof docstring also identifies `lem-sfb-ringed-restriction-strict-limit-coherence`, whose node currently has no usable Lean module; it is only a proof dependency and introduces no missing notion into this statement.

Searches: `msearch.py` LeanFinder queried the integral supported restriction reconstruction and canonical scalar quotient tower; results were unrelated scheme fractions/presentations. LeanSearch queried strict ordinary quotient towers and actual derived global sections augmentation; results were general sections or scalar-restriction constructions. Loogle queried `Functor.rightDerivedPullback, Functor.ofOpSequence, cokernelFunctor` (no match; unknown-identifier response recorded verbatim). Mathlib grep queried `supported_integral_model_restriction|integral.*restriction.*tower|restriction.*quotient.*tower`, and the auxiliary names (no matches). `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and the DAG found no existing statement or exact tower-data definition; incidental Cartier/smooth-purity names were different notions. `blueprint_refs.py search 'supported integral model tower'` returned no match. The JSON's `mathlib_searches` preserve the tool outputs, including unsuccessful searches. Existing path extensions, local-model predicates, coefficient constructions, site comparison, derived functors and torsion/cohomology interfaces are reused.

## New nodes

`def-sfb-supported-integral-model-tower-data` introduces the previously unrecorded canonical ordinary scalar quotient sequence, supported augmentation, scalar-coordinate normalization, marked finite descent and the associated strict-tower sections comparisons. Its source is the first paragraph of refinement (2), the same integral closed-fibre comparison used by the item. The searches above and in its JSON found no duplicate of this composite notion. Its module constructs data rather than choosing an unspecified object from a postponed existence assertion. The item's `stmt_deps` gains this node and the already-landed `def-sfb-qcqs-open-closed-tree` interface.

`def-sfb-supported-integral-restriction-arrows` records the actual integral and strict finite arrow functors and source quotient normalization, built from the tower-data node. It is separated for the per-file elaboration limit; it introduces no independent cohomology or scalar-module definition. The same searches apply, and all component functors reuse the recorded constructions. The normalization is equality of maps to the entire total derived limit, rather than only degreewise equality.

`def-sfb-supported-integral-restriction-comparison` records the normalized pullback identification and both endpoint equations. The canonical mate and the canonical site-comparison square fix the closed-fibre marking. Its module imports the arrows interface and contains definitions only. Separating these interfaces keeps the construction independent of instances loaded only by the theorem's proof-dependency imports. No instances of imported modules are changed in the final delivery.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
