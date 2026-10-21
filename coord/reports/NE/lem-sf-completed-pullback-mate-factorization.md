## Worker report

The module `Sheaf.Paper.SfCompletedPullbackMateFactorization` states
`AlgebraicGeometry.Scheme.ExactPullbackNormalization.completed_pullback_mate_factorization`.
Its only postponed proof is this theorem. Four concrete helpers spell out the mate,
the evaluated quotient augmentation, the transported specified limit projection, and
all composite strict quotient transitions. Their data contain no `sorry` or existential
choice. The node is unchanged except for `lean`; no new node or dependency repair is needed.

Sources read: the current blueprint localization unit
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.md`;
the node's complete five-step native refinement; the native
`SfImmersionCompletedPullbackComparison.lean` declarations `rlimComparison`,
`ordinaryToCompleted_eq` and `completedProjection_compatibility`; and Stacks
`proetale.tex`, `lemma-pushforward-Noetherian-case` (Tag 099N), statement and proof.
The Stacks assertion supplies the completion context, while the mate identity is the
agent-written refinement explicitly named by the node. The source's immersion theorem
is only a specialization and is not an exact existing match for this item.

Hypotheses and clauses are rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| A morphism g:Y -> X of schemes | `{X Y : Scheme.{u}} (g : Y ⟶ X)`; there is no immersion, Noetherian-scheme, separatedness or dimension condition. |
| Small pro-etale sites | Every `pbcModules T R` uses `ProEt.topology T` on `T.ProEt`; the existing sites have object universe u+1 and morphism universe u. |
| Noetherian adic datum (A,I), its finite perfect positive quotients and completed rings | `{A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)`; `pbcAdicCompletion T d` is the actual limit of its recorded coefficient sheaves. The datum includes all the node dependency's Noetherian, finite-generation, torsion, finiteness and perfectness conditions. Lean n represents exponent n+1, so all positive levels are included. |
| The projection-defined coefficient map is invertible | `[IsIso (completedCoefficientMap g d)]`; this is the existing map constructed from its finite projections. |
| F is ordinary inverse image with extension along c_g, identified as in the normalization dependency | `moduleFunctor d g` is the recorded inverse image followed by restriction along `inv (completedCoefficientMap g d)`. The normalization dependency's `ModuleComparisonSpec` fixes the tensor-generator isomorphism between this and `completedModulePullback g d`. This is the same identified functor allowed by the node, not a variable unrelated functor. |
| F is additive and exact | `[(moduleFunctor d g).Additive]`, `[PreservesFiniteLimits (moduleFunctor d g)]`, `[PreservesFiniteColimits (moduleFunctor d g)]`. Finite-limit and finite-colimit preservation express exactness in these abelian categories. |
| Unbounded derived modules and strict inverse sequences | `DerivedCategory (pbcModules T R)` and `DerivedCategory (pbcTowers T R)`, where the latter abelian category is `ℕᵒᵖ ⥤ pbcModules T R`. No boundedness restriction is introduced. |
| Exact ordinary and tower pullback, normalized against the original left-derived counits | `(moduleFunctor d g).mapDerivedCategory` and `(towerFunctor d g).mapDerivedCategory` are exactly the functors in the recorded `counit_normalization` theorem. Its ordinary and tower normalization predicates, constant and evaluation equations, and actual-comparison equation were read in full. |
| Canonical constant/derived-limit adjunctions and their units and counits | `d.constantRlimAdjunction T`, its `.unit` and `.counit`; `completedTowerRlim d T` is the same total right-derived limit of the actual strict limit. These are not arbitrary adjunction parameters. |
| j induced from equality on constants and normalized exact comparisons | Existing `constantIso d g` has the reverse orientation to j, so its `.hom` is precisely j inverse. It derives `Functor.compConstIso` using the canonical exact-localization comparison isomorphisms. |
| beta_M = L_Y(F_tower epsilon_X,M) L_Y(j inverse) v_Y | `limitMate d g M` is defined by the target adjunction unit followed by the limit image of `constantIso.hom` and the image of the source counit, in Lean's left-to-right composition convention. |
| i_K and comp_K = L_X(i_K) v_X | The published `(completedReductionTowerUnit d X).app K` and `d.completionUnit X K` are reused. The latter is defined by the canonical adjunction unit followed by the derived-limit image of this exact augmentation. |
| The actual alpha after counit-normalized identifications | Existing `exactAugmentation d g K` is reused, rather than a supplied arbitrary map. The dependency theorem states `completedPullbackComparison ≫ completedIso.hom = e.hom ≫ exactAugmentation`, so this is exactly alpha^F in the node. It retains the published strict quotient augmentation and the projection-defined K-injective constant-limit unit. |
| alpha^F_K = beta_(K_bullet) F_D(comp_K) | First conjunct, `exactAugmentation d g K = F_D.map (d.completionUnit X K) ≫ limitMate d g (K_bullet)`. |
| Specified evaluation p_n | `pulledProjection d g n K`: the existing `completedRlimProjection` followed by the dependency's exact `evaluationIso.hom`. Its target is exactly F_D of the evaluated source quotient tower. |
| Actual quotient augmentation q_n,K | `quotientAugmentation d n K`: evaluate the published strict augmentation and precompose by the canonical inverse of evaluation of a constant tower. Its localization factors are explicitly constructed from Mathlib/upstream identity, constant-evaluation and composition isomorphisms. |
| p_n alpha^F_K = F_D(q_n,K) | Second conjunct, `exactAugmentation ≫ pulledProjection = F_D.map quotientAugmentation`. |
| F_D(rho_m,n) p_m = p_n for every m >= n | Third conjunct, for all `a b : ℕ` and `h : a ≤ b`, with `quotientTransition` the existing canonical `DerivedTowerPullback.derivedTransition` evaluated on the quotient tower. There is no restriction to successive levels. |
| Respect for composite quotient transitions | Fourth conjunct: for all `a ≤ b ≤ c`, the two successive pulled transitions after p_c equal the direct pulled transition after p_c. Together with the third conjunct both are p_a. Equality cases are included. |
| Naturally in every unbounded K | Fifth conjunct gives naturality of the actual augmented map for every derived morphism `f : K ⟶ K'`. Each helper is a composite of canonical natural transformations. |
| No completeness or preservation of countable products | No such instance or hypothesis occurs. In particular `K` ranges over the whole ambient derived category, not its complete full subcategory, and no inverse of `completionUnit` is taken. |

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionTower` and the actual reduction coefficient sheaves; its recorded helper interface is retained through public imports.
- `Sheaf.Paper.PbcQbarCompletedPullback`: the recorded dependency module retains the ambient completed-pullback construction by public import. The relevant actual definitions are `completedCoefficientMap`, `completedPullbackComparison`, and `completedReductionTowerUnit` in `CompletedTowerPullback`, and `AdicCoefficientDatum.constantRlimAdjunction` / `completionUnit` in `CompletedPullback`. The primary Qbar functor is an additional specialization, not used in the ambient assertion.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`, transparently used by `pbcModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, with the existing standard localization instances.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence`; the existing `pbcTowers` uses its equivalent inverse-diagram encoding.
- `Sheaf.Paper.SfExactPullbackCounitNormalization`: `moduleFunctor`, `towerFunctor`, `constantIso`, `evaluationIso`, `exactAugmentation`, and `counit_normalization`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`: `ringedStrictTowerHomotopyLimitIndependentCoefficients`, imported for the unbounded K-injective limit proof step.
- `Sheaf.CategoryTheory.DerivedTowerCounitProjections`: `derived_tower_counit_projections`, imported for the normalization of the actual counit evaluations and strict augmentation.
- `Sheaf.Paper.DerivedTowerEvaluationNormalization`: `CategoryTheory.DerivedTowerPullback.derivedTransition`, already publicly imported by the normalization dependency.

Edge cases checked before writing: equal transition indices (the existing strict transition
is the identity), all composites a <= b <= c, first positive quotient (Lean index 0), the
zero complex, the empty scheme, and arbitrary unbounded and noncomplete inputs. None is
excluded by the binders. There is no nonemptiness, uniform cohomological bound, product
preservation, or coefficient-characteristic assumption beyond the recorded datum. The
adjunction proof uses triangle identities, not joint detection of derived tower maps by
their evaluations.

Searches actually run:

- `msearch.py`, leanfinder: "ordinary completed pullback comparison factors through right mate and source completion unit". Eight hits, all generic categorical pullback comparisons, including `Limits.pullbackComparison` and `ChosenPullbacksAlong.unit_pullbackComp_hom`; none states this completed sheaf-pullback assertion.
- `msearch.py`, loogle: "CategoryTheory.mateEquiv, CategoryTheory.Adjunction". Twelve hits, including `mateEquiv`, `mateEquiv_apply`, `mateEquiv_counit` and unit/mate composition identities; these are ingredients, not the assertion about the specified strict quotient construction.
- `msearch.py`, Mathlib grep: "ordinaryToCompleted|constantRlimAdjunction|completed.*[Mm]ate". Zero hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf`: the same key words plus the exact item id. No upstream match or exact-id declaration. The native `SfImmersionCompletedPullbackComparison.ordinaryToCompleted_eq` specializes to immersions and a finite p-adic datum. `stratumRlimComparison` likewise uses its own canonical pullback and stratum context. Neither states the present arbitrary-morphism, arbitrary-adic-datum exact-normalized assertion with all projection and composite-transition clauses. Their constructions were read rather than copied as private alternative functors.
- `rg` also located the existing general `derivedTransition` and the canonical exact-derived identity/composition isomorphisms; those are reused.

No `STATEMENT-DISPUTED` issue or source correction was found. The example
`Sheaf.CategoryTheory.CompactObject` is now withdrawn; its node records the upstream
`WeilConjectures.CategoryTheory.CompactObject`, whose header and definition were read
for the current formatting conventions.

Validation: all compilation uses the prescribed `scompile.py` on the server. The initial
compile diagnosed a namespace collision with `Scheme.evaluation`, repaired by the full
`CategoryTheory.evaluation` name. The next compile had only one long-line warning, whose
line was wrapped. Final clean compilation and the prescribed dry run precede delivery.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
