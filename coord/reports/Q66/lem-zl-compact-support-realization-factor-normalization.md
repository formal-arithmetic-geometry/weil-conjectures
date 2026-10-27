## Worker report

This module states the integral, rational and scalar factor normalization. All theorem proofs are `sorry`; definitions have explicit data. All maps are formed before finite evaluation, using the actual adjunctions and coefficient equivalences. The main declaration is `WeilConjectures.CompactSupportFactorNormalization.realization_factor_normalization`; the other named statements in lean.declarations supply the integral, structural, scalar, identity and naturality clauses.

### Hypotheses and clause-by-clause rendering

- `D₀ : FiniteFieldDatum` supplies the finite field and its fixed algebraic closure `D₀.k`. `[Fact l.Prime]` and `[Fact (l ≠ D₀.p)]` retain the prime conditions. `geometricCharacteristic*` transports the inherited characteristic to the parent API without assuming a new characteristic equality.
- `E : Type u`, `NormedField`, `NormedAlgebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E` are the recorded finite continuous coefficient convention. The valuation ring, uniformizer and positive quotients are the dependency constructions. The scalar theorem has the embedding `a : E →ₐ[ℚ_[l]] PadicAlgCl l`, and the finite extension `i : E →ₐ[ℚ_[l]] F`, including identity extensions.
- `X Y : CondensedERealization.Base D₀.k` retain the separated finite-type schemes with their structure maps. The morphism has explicit `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` hypotheses. `c : Compactification f` includes the open immersion and proper map; `[QuasiCompact c.i]` retains the quasi-compact-open condition.
- `IntegralSystemRealization.Integral` is the recorded completed-ring presentation. `calculus` gives strict reduction, total limit, unit and counit. The existing `purCoefficientModel` transports the parent's Pbc completed-ring presentation. No private coefficient category is introduced.
- `K : CondensedERealization.Integral l E X.scheme` retains bounded constructible completeness. `Domain ... lo hi a z` retains the input, open intermediate, proper/open intermediate and strict system word, with the SAME cohomological and Tor windows and compatible FixedEtaleOriginWitness data from GeneratorReduction.Admissible and IntegralCompactificationBridge.systemWordDomain.
- `o`, `m`, `b` are the recorded simultaneous operations, their canonically normalized realization model and identity-on-sections bridge. They do not assume the desired factorization. `AZ : At ... c.Z` is the same coefficient realization at the middle scheme.
- `word` is separately derived integral open extension followed by proper image. `support` is reduction, system open, system proper, total limit. `systemPresentation` pastes the existing canonical bridge. `parentCoordinates` includes the actual coefficient-equivalence counit, identifying the parent's strict-tower limit with these coordinates.
- `properReduction` is the counit transpose of the specified proper limit comparison, including reconstruction of its complete input. `systemComparison` follows it by inverse open reduction. `integralComparison` is literally `unit ≫ limit.map systemComparison`, hence L(b)u. `integralComparison_normalization` states invertibility, BOTH inverse equations, and `r(q) ≫ counit = b` as an equality in the whole derived-system category.
- `integralInverse` is the proper limit comparison followed by the limit of the open reduction mate and inverse reconstruction unit. `single_realization` identifies this actual arrow with the normalized compactSupport comparison of the recorded Realizations. `structural_conjugacy` quantifies over the actual CanonicalPair, which includes proper/open units, counits, interchange, composition, inverses and finite contexts. `completed_bridge` retains the independently constructed completed comparison, inserted system counit and its full bridge domain. Its right-hand side now explicitly expands all three direct identifications as inverse `integralComparison` (q) followed by the fixed strict-quotient realization; it therefore records the bridge in q coordinates.
- `realize` is actual integral-to-rational scalar extension followed by inverse section encoding. `latticeComparison` identifies this with rationalization followed by J using EXACTLY `At.scalarExtension` and the existing equivalence unit. Thus mapping an integral arrow by realize is J of its rationalization under these specified coordinates.
- `ordinaryRestrictionSquare` is uniquely identity on sections; `restrictionSquare` derives it using canonical derived units. `realizationPull` is its unique adjoint conjugate. `properRealization` is its geometric counit mate. `openRealizationInverse` is the open-unit mate; `openRealization` is its inverse. Their invertibility on the domain is part of the main conclusion, not an input hypothesis.
- `factorization` has order `realize.map integralInverse ≫ properRealization ≫ properPush.map openRealization`. `parentFactorization` includes parentCoordinates and latticeComparison. The main equality is `(normalizedFamilyAt ... C h ...).realization.hom.app (ScalarLocalization.mk K) = parentFactorization ... K`, using exactly the transported integral model of that same family component.
- `realization_factor_normalization` now asserts `∃ C : ComparisonFamily l D₀.k, IsFactorNormalized l D₀ C`. The predicate quantifies over every finite coefficient field F and retains an equality `(C.coefficient F).reduction = calculus l F`; `normalizedFamilyAt` transports the existing `atCompactification` component along that equality, with no new choice. Its `realization` is precisely the arrow equated to the formula. Thus finite-coefficient squares, refinement coherence, shift compatibility and all other parent family laws apply to these same normalized components. All compactifications and admissible lattice inputs use the single C. The node statement is unchanged; the earlier isolated RealizationAt existential was insufficient and is replaced.
- `coefficient_factorization` states the second equality for the actual parent `condensedProjection`: `derivedPushHom` followed by proper push of `derivedOpenImmersionShriekIso`. `coefficient_proper_transpose` writes its target-coefficient counit transpose as inverse `derivedPullIso` then scalar extension of the source counit. `coefficient_open_unit` writes the inverse open map as the adjunct of the scalar-extended open unit.
- These generic scalar statements apply to the parent's actual `fieldMap` and `omegaMap`, with their existing flatness instances. `coefficient_proper_isIso` states invertibility of BOTH finite and closure-linear proper maps on bounded constructible inputs in the actual internal module categories. Its proof docstring retains bounded-below representatives, filtered finite subextensions and qcqs direct-image continuity.
- `ordinaryPushIdentity_existsUnique` uses the actual pullback-identity section coordinates. `integralPullIdentity` is its adjoint conjugate; `integralOpenIdentity` is fixed by the actual open adjunction. `realization_identity_open` and `coefficient_identity_open` identify the open factors with identity under canonical unitors. Substitution in the displayed factorizations leaves precisely the proper factors.
- `integral_naturality` gives both q and inverse-q naturality squares; `factorization_naturality` gives the realization square. Scalar naturality is supplied by the actual natural transformations in coefficient_factorization. No endomorphism, operator, point-realization or proper-unit compact-support equality is asserted.

### Dependency declarations

All recorded statement dependency interfaces and their docstrings were read. The following recorded modules/declarations are publicly imported and reused (the morphism-properties node is a convention-only record rendered with Mathlib classes).
- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-scheme-morphism-properties`: `convention-only`, `Mathlib scheme morphism classes`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
- `def-weil-pbc-bounded-constructible-complete`: `Sheaf.Paper.IntegralUniformCoefficient`, `AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-pbc-etale-origin-witness`: `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`, `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
- `lem-weil-compact-support-reduction-tower-functor`: `Sheaf.Paper.CompactSupportReductionTower`, `WeilConjectures.exists_compactSupportReductionTower`.
- `lem-cbc-integral-compact-support-uniform-restriction`: `Sheaf.Paper.IntegralCompactSupportUniformRestriction`, `AlgebraicGeometry.Scheme.cbcIntegralCompactSupport_uniformRestriction`.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `lem-pur-ringed-coefficient-projection-cocycle`: `Sheaf.Paper.RingedCoefficientProjectionCocycle`, `SheafOfModules.RingedCoefficientProjection.ringedCoefficientProjectionCocycle`.
- `lem-sf-open-tensor-normalization`: `Sheaf.SixFunctors.OpenTensorNormalization`, `SheafOfModules.openTensorNormalization`.
- `lem-weil-pbc-condensed-e-realization`: `Sheaf.Paper.CondensedERealization`, `WeilConjectures.condensedE_realization`.
- `def-weil-pbc-condensed-e-module-category`: `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`, `Profinite.isCommMonObj_continuousCoefficientRingObj`.
- `prop-weil-pbc-qbar-condensed-two-colimit`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`, `AlgebraicGeometry.ProEtale.constructibleCocone_isFilteredTwoColimit`.
- `lem-weil-pbc-condensed-flat-coefficient-calculus`: `Sheaf.Paper.CondensedFlatCoefficientCalculus`, `AlgebraicGeometry.ProEtale.condensedFiniteCoefficientCalculus`.
- `lem-sf-integral-compactification-system-realization`: `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`, `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`.
- `lem-sf-integral-compactification-comparison-bridge`: `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge`, `WeilConjectures.IntegralCompactificationBridge.integralCompactificationComparisonBridge`.
- `lem-pur-compact-support-condensed-realization`: `Sheaf.Paper.CompactSupportCondensedRealization`, `WeilConjectures.compactSupport_condensedRealization`.


- `def-sf-integral-system-operations`: `Sheaf.SixFunctors.IntegralSystemOperations`, `IntegralSystemRealization.Operations`, `calculus`, `Integral`, `System`, `Operations.push`, `Operations.shriek`.
- `def-sf-integral-system-canonical-bridge`: `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`, `IntegralSystemRealization.RealizationModel`, `CanonicalBridge`, `ringedPull`, `ringedPush`, `ringedOpen`, `ringedAdj`, `ringedOpenAdj` and the canonical compositors.
- `def-sf-integral-system-realization-data`: `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`, `IntegralSystemRealization.Realizations`, `CanonicalPair`, their comparison and canonical-generator data. This cites the definition owner separately from its existence theorem.
- `def-pur-condensed-compact-support-projection`: `Sheaf.Paper.CondensedCompactSupportProjection`, `CompactSupportCondensedRealization.condensedProjection`, `condensedScalar`, `FlatCoefficientMap`, `fieldOpenAdjunction` and coefficient-composition/refinement maps.
- `def-sfb-derived-open-lower-shriek-id`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionLowerShriekId`.
- `def-zl-integral-generator-admissibility-inverse`: existing definitions in `Sheaf.SixFunctors.GeneratorReductionStatement`, `WeilConjectures.GeneratorReduction.Admissible`, `SystemAdmissible`, `inverseOrZero`. The coherence theorem stays in proof_deps only; its plain definitions are owned by this new definition node.
- `def-zl-compact-support-small-site-morphism`: existing `AlgebraicGeometry.Scheme.sfCbcSite`, `sfCbcModelInverse`, `sfCbcModelDirect`, `sfCbcModelAdjunction`, `sfCbcMorphism` in `Sheaf.Paper.SfCbcCompactSupportCompositionLimit`.
- `def-zl-compact-support-model-open-extension`: existing `AlgebraicGeometry.Scheme.sfCbcModelRing`, `sfCbcModelModules`, `sfCbcOpenExtension`, `sfCbcModelExtension` in `Sheaf.Paper.SfCbcExtensionZeroCompletion`.
- `def-pur-completed-coefficient-presentation-transport`: `Sheaf.Paper.CompletedCoefficientPresentationTransport` and its published supporting module `Sheaf.Paper.IntegralCoefficientCompletenessTransport`, `WeilConjectures.purCoefficientModel` and `purOrdinaryCoefficientModel`.
- `Padic.coefficientExtensionIntegers l E` is used directly for the coefficient ring; its owner `def-weil-l-adic-coefficient-extension` was already cited. There is no use of `GeneratorReduction.constantRing` in the repaired module.

The existing owning helpers are also reused: RealizationModel.push/openReduction, CanonicalBridge.shriek/push, Realizations.comparison, CanonicalPair, purCoefficientModel, encodingDerived, completedComparison/semilinearComparison and the parent fieldMap/omegaMap/condensedProjection. Three definition nodes now register the already published helpers, without duplicating any Lean definitions; no dependency module is needed.

### Edge cases

Checked zero inputs, empty schemes and empty opens: all formulas use the actual derived adjunction maps. The identity open uses canonical unitors, not definitional equality after sheafification. For the identity compactification q is the reconstruction unit in identity-operation coordinates. Identity coefficient extensions are allowed. The closure uses its actual finite-subextension-valued coefficient ring. Quotients are indexed by n+1; no positive-quotient assumption at n=0 is introduced. Bounds are integer intervals subject exactly to the inherited Admissible and bridgeDomain conditions, including their lo≤hi and Tor-window inequalities; no additional bound hypothesis is imposed. All variables and universes are explicitly bound and autoImplicit is false.

### Searches and validation

- msearch.py leanfinder, query “Compact support realization comparison factors as proper pushforward coefficient projection and extension by zero normalized by reduction limit adjunction unit”: eight unrelated compact continuous-map results; no exact match.
- msearch.py loogle, query “Adjunction.homEquiv, Functor.mapIso, Iso.trans”: zero results, with unknown Adjunction.homEquiv in the index. The actual Mathlib mate/conjugate APIs were then read in source.
- msearch.py grep, query “compactSupport.*[Nn]ormali|realization.*[Ff]actor|[Pp]rojection.*[Cc]ocycle”: two unrelated HomComplex/MappingCone comments.
- msearch.py leansearch, query “canonical compact support coefficient realization proper open factorization reduction limit unit”: eight unrelated compact-support function declarations.
- rg/grep in WeilConjectures and Sheaf for the node id and proper/open normalization: the parent supplies the scalar paste, and the integral realization dependencies supply their normalized maps, but no existing declaration states this full normalization. Those maps and interfaces are reused.
- Read the current blueprint under literature/blueprint/latest and the node's explicit source qualification: the normalization is agent-formulated; the Bhatt–Scholze places provide the coefficient and compactification context.
- Every compilation uses scompile.py against the live published server build. Final compilation and delivery dry-run results are appended after validation.

No statement correction, no STATEMENT-DISPUTED flag and no dependency rebindings. The three new definition-owner nodes are detailed below.

## Second reading by Q66

No second worker reading: this dispatcher brief directs delivery without subagents; the maintainer supplies the independent review.

## Earlier returned-delivery repair (1042dcac4cf4)

The sandbox was compared with the returned delivery and the current read-only node (which has no Lean binding); the mathematical statement is unchanged. This repair changes the Lean declarations and adds only their existing owner nodes to stmt_deps.

- H3: replaced the unrelated RealizationAt existential by existence of a single ComparisonFamily with IsFactorNormalized. The reduction equality and dependent transport explicitly tie the displayed formula to its atCompactification.realization. A negated family fails this normalization unless its components equal the specified formula; coherence laws no longer belong to a different witness. Consumers can extract C and apply its finite/refinement/shift laws to exactly these components.
- Earlier H2 attempt: added the five definition owners and the generator-coherence theorem to stmt_deps. The second return correctly requires definition ownership for the generator helpers instead of a theorem edge; the current repair below supersedes that part.
- Advisory H4: expanded completed_bridge into inverse-q coordinates for cf, cg and cfg, including the fixed strict-quotient identifications and the original middle reconstruction counit. It no longer merely repeats the bridge theorem's semilinearComparison clause.

Repair validation is recorded below after compilation and the delivery dry run.

Repair compile: scompile.py compiled the final file without errors or unexpected warnings in sandbox and library forms (44.2 s and 41.9 s). All 52 declarations are recorded, the main signature matches verbatim, and no Lean line exceeds 100 characters. The only node fields changed are lean and the six explicitly requested additions to stmt_deps.

Repair dry run: deliver2.py --no-push printed OK for commit 5f1b34c63d2: server preflight and per-file compilation passed; nothing was pushed by the dry run.


## New nodes

All three nodes have existing:true Lean records and register exact existing declarations. They introduce no Lean module, duplicate definition, new theorem or proof. Their source fields identify the current blueprint argument and explicitly distinguish the agent-formulated coordinate/domain definitions from literal source theorems.

- `def-zl-integral-generator-admissibility-inverse`: `SystemAdmissible` retains normalization, the compatible Origins package, both window inequalities, and every positive-level constructibility, cohomological-support and Tor-amplitude condition. `Admissible` is exactly `finiteTorConstructibleIntegral ∧ SystemAdmissible` on the supplied calculus's reduction. `inverseOrZero` applies to any category with zero morphisms and is literally `if h : IsIso f then inv f else 0`. The node lists these three definitions from GeneratorReductionStatement; it asserts no generator-coherence theorem. Every interval and positive quotient index is retained, including the boundary n=0 corresponding to quotient exponent n+1.
- `def-zl-compact-support-small-site-morphism`: registers `sfCbcSite`, `sfCbcModelInverse`, `sfCbcModelDirect`, `sfCbcModelAdjunction`, and `sfCbcMorphism`. For schemes in universe t the chosen equivalent model is in t+1. Direct image is precomposition with transported base change; inverse image is sheafified left Kan extension. The morphism retains their canonical adjunction, left exactness and induced algebraic lift. This is the exact ambient `AdicSites.Morphism` used by completed_bridge, without a geometric finiteness restriction or any completion-comparison assertion.
- `def-zl-compact-support-model-open-extension`: registers `sfCbcModelRing`, `sfCbcModelModules`, `sfCbcOpenExtension`, and `sfCbcModelExtension`. For arbitrary commutative A and an open j, these retain the constant ULift coefficient sheaf, exact transport fixed on constant sections, actual localized extension by zero, and its composite with the inverse source transport and target transport. Only the ordinary functor is defined; an adjunction presentation af/ag/ah is still explicit in completed_bridge. Empty opens and the zero ring remain included.

The new nodes lie in sec-zeta-weil, retain the item's chapter and unit, have blueprint ancestor sk-thm-rationality with the item prefixed to its via chain, and are directly cited from the item. Their proof fields are empty and their Lean signatures are copied verbatim from the existing definition headers.

Searches for all new nodes: LeanSearch returned eight generic derived-zero comparison results for the domain query, and eight generic site/sheaf results for the model query; LeanFinder returned eight generic results for each query. Mathlib grep for SystemAdmissible|inverseOrZero|sfCbcModelExtension|sfCbcMorphism returned zero hits. The new nodes' mathlib_searches retain each tool's raw output. Direct rg in WeilConjectures found none of these names; rg in Sheaf found exactly the reused declarations. Extended grep over dag/nodes and inspection of definition-node lean.declarations found no existing definition owner for these helpers (the site-transport/word-comparison nodes only mention them as inputs). blueprint_refs.py searches for sfCbcModelExtension and GeneratorReduction.Admissible returned zero blueprint nodes. These exact searches and outputs are also retained in mathlib_searches.

## Current repair of returned head 1042dcac4cf4

H2 is repaired with a full stage-2 delivery, rather than an S2 FIX: the plain generator-domain and inverse definitions now have an existing:true definition owner, and the generator-coherence theorem is removed only from stmt_deps and retained in proof_deps. The two sfCbc helper packages have their own existing:true definition owners. The item explicitly cites def-pur-completed-coefficient-presentation-transport for purCoefficientModel. All owner modules are public imports. Every occurrence of GeneratorReduction.constantRing is replaced by its actual expansion Padic.coefficientExtensionIntegers l E.

The mathematical statement and its accepted family normalization are unchanged. The only Lean source changes from the returned head are public owner imports and the definitionally identical spelling of the valuation ring. In particular IsFactorNormalized still normalizes the same ComparisonFamily components, and completed_bridge still displays the three inverse-q factors and middle system counit. The main theorem signature and all 52 declaration names are retained. No unresolved mathematical fault or STATEMENT-DISPUTED flag remains.

Current compile and delivery results follow after validation.

Current repair compilation: scompile.py compiled the repaired file in both sandbox and library forms without errors or unexpected warnings (reported elapsed times 62.3 s and 57.6 s). No timeout override was used. All three new nodes are existing:true records, so no new Lean source is required. The open-extension definition node cites the ordinary localized-ringed-site, extension-presheaf and module-sheafification definition owners directly.

Current repair dry run: deliver2.py --no-push printed OK for commit 8fa18b1e768. Server preflight, checks of the existing-declaration records, and compilation passed. The packet contains the main module and node, the three definition-owner node records, and this report.
