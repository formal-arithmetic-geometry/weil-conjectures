## Worker report

Item: lem-weil-proper-coefficient-descent. Group: Q59. Stage: 2 (statements only).
Module: `Sheaf.Paper.ProperCoefficientDescent`.
Main declaration: `WeilConjectures.ProperCoefficientDescent.properCoefficientDescent`.

The module states scalar compatibility of the supplied identity-compactification
integral comparison, its raw rational natural isomorphism, and its descent to the
literal pair category. The main theorem has `sorry`; no proof is supplied.
The six auxiliary declarations have actual definitions, with no postponed data.
They name the finite identity comparison, the ordinary chosen projection adjunct,
the completed identity comparison, the recorded compact integral action, and the
two parts of the hypothesis specifying the supplied comparison.

Source read: `literature/blueprint/latest/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md`, first paragraph. The proper
identity compactification identifies the finite functors; its canonical comparison
passes to integral, rational and algebraically closed coefficients. The node's
expanded seven-step proof specifies the scalar and same-stage normalization.

### Hypotheses, clause by clause

* The finite-field datum is `B : FiniteFieldDatum.{u}`. The prime and distinct
  characteristic are `(l : ℕ) [Fact l.Prime]` and `hl : l ≠ B.p`.
  `PurCompactSupport.coefficientPrimeUnit l B hl` is the published conversion
  to invertibility over the geometric base field; it adds no hypothesis.
* The algebraic closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. Universes `u v` are independent. Its finite
  subfields range over `Index l Ω`; `Coefficient.{u} l Ω E` is the existing
  small model of each finite field. Its ring, uniformizer and positive quotient
  are precisely the published `Padic.coefficientExtension*` constructions.
* `X Y : Scheme.{u}` have `Over (Spec (.of B.k))`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` structure morphisms. Thus finite type means
  locally finite type and quasi-compact, including empty schemes. The morphism
  `f : X ⟶ Y` has `f.IsOver (Spec (.of B.k))` and `IsProper f`.
* The compactification is literally `Compactification.ofIsProper f`, whose open
  is the identity on X and whose proper map is f. The sites and derived module
  categories are those of the recorded dependencies, not replacement categories.
* `D : SfStrictDirectImageScalar.IntegralComparisons l Ω f` with `HasIntegralLaws`
  fixes the normalized strict integral image and the ambient scalar comparison.
  `R : ...Comparisons l Ω f D` with `HasComparisonLaws` fixes the raw rational
  action, its literal tensor map and localized scalar comparison.
  These packages express the specified actions; no choice of scalar isomorphism
  is introduced. In particular, b_* is `(D.integralComparison E L h).inv`.
* `S : SfCompactSupportCoefficientAction ... (Compactification.ofIsProper f)`
  is the specified compact action. Its `integralBeta` is b_!, its `system` the
  normalized rational stage-system action, and its laws retain unit and
  successive-extension identifications.
* `θ : ∀ E, compactIntegral ... E ≅ (D.integral E).image` is the supplied integral
  natural isomorphism at every finite coefficient field. `compactIntegral` is
  only an abbreviation for `sfCompactSupportFiniteIntegralFunctor`.
* `PreservesProjections ... θ` expresses the actual finite projection adjunct
  equation. `ordinaryReduction` transposes the completed reconstruction inverse,
  Rf_* of the actual source reduction unit, then the canonical restriction
  comparison. The compact arrow is `sfCompactSupportFiniteReductionIso`, the
  adjunct of the chosen Roos projection. `finiteIdentity` is ordinary Rf_* of
  `sfIntrinsicDerivedOpenId`, followed by the left unitor. Index n means n+1,
  so every quotient here has strictly positive exponent.
* `InducedOnFullTower ... θ` retains the stronger phrase in the node that θ is
  induced on the full defining system before evaluation. Its ordinary coordinate
  changes a and b are existentially presented but uniquely constrained on EVERY
  module section: a is restriction along the inverse canonical identity
  base-change isomorphism, and b is identity on the underlying sections. They
  cannot be replaced by arbitrary derived natural isomorphisms or twists.
  `completedIdentity` constructs the identity-open comparison using the two
  ordinary adjunction identities, exact derivation, and functorial derivation of
  b. The final equation conjugates this whole derived map through the published
  `sfQcqsCompactSupportRealization` inverse and D's normalized reconstruction.
  This is the completed proper/open presentation of the node's full-tower map:
  on a common resolution its finite terms are exactly Rf_* of the identity-open
  map, and its completed reconstruction is the specified total-limit map.
  The separate projection equations additionally retain the node's chosen Roos
  projections. No inference of equality of coherent maps from their separate
  finite evaluations is used in the statement.

### Conclusions, clause by clause

* The first conjunct is the integral square, for all E ≤ L and K:
  `integralTransition Y .map θ_E ≫ (D.integralComparison E L h).inv =
  (S.integralBeta h).hom ≫ θ_L.app (integralTransition X .obj K)`.
  The orientation agrees with the displayed b_* and b_! in the node.
* `r : ∀ E, S.system.Φ E ≅ R.rational E` gives a natural isomorphism on each
  actual raw rational category. Its hom AND inverse at every object are HEq to
  the localization of θ.hom and θ.inv respectively. Since r is a NatIso, its
  naturality quantifies over ALL raw tensor Hom elements, including every finite
  sum of tensors and torsion classes; it is not limited to pure tensors.
* `G : (stageSystem l Ω X).Morphism (stageSystem l Ω Y)` is the ordinary rational
  coefficient action. Its finite functors equal `R.rational`; its beta components
  are the inverse of the published `R.theta`, as required by the stage-system
  orientation. Its structure includes the specified successive-extension laws.
* `e : S.system.functor ≅ G.functor` is on the ACTUAL quotient pair category.
  Both component maps are represented by inclusion of r.hom and r.inv at the
  object's own finite stage. HEq handles equality-based endpoint transports;
  it does not assert equality between unrelated Hom types.
* `τ : S.system.Hom G` has finite natural transformations equal (HEq) to r.hom.
  Its `comm` is the scalar square and `e.hom = descNatTrans τ` fixes the descent.
* The first displayed `mapAt` equation holds for an arbitrary representative a
  over the SAME common field L, with all source and target beta factors built
  into `mapAt`. Its next conjunct explicitly repeats the equality for the actual
  transported representative `(stageSystem l Ω X).tr hLM a` over every M ≥ L,
  with the prescribed scalar associators and composed field inclusions.
* Because e is a natural isomorphism on quotient Hom groups, it is independent of
  the representative of a morphism. The last conjunct spells out its naturality
  for `isoToStage A h`, the canonical scalar-extension presentation of an object.
  Thus both independence clauses use the recorded categories and maps.

### Dependency declarations used

Names below have their published full namespaces in the module.

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (reexported):
  `Padic.finite_coefficientExtensionRing`, and the original coefficient ring,
  integers, uniformizer and quotient constructors.
* The scheme-property convention node: Mathlib's `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`; `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsProper`.
* `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` and the alias
  `sfAmbientCompactSupportCandidate`.
* `Sheaf.Paper.SfDerivedDirectImage`:
  `sfCompletedModuleDirectImage`, `sfCompletedDerivedDirectImage`,
  `sfDerivedRestrictionComparison`, `sfFiniteDerivedDirectImage`.
* `WeilConjectures.Compactification.RefinementCategory` (and its Defs import):
  `AlgebraicGeometry.Compactification.ofIsProper`.
* `Sheaf.Paper.CompactSupportFiniteAction`:
  `sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteReductionIso`.
* `Sheaf.Paper.CompactSupportCoefficientAction`:
  `SfCompactSupportCoefficientAction`, its `system`, `integralBeta` and laws.
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleLocalization`, the raw tensor Hom category.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `Index`, `Coefficient`, `Stage`, `Pair`, `StageHom`, `stageSystem`,
  `integralTransition`, `stageTransition`, `inclusion`.
* `Sheaf.Paper.IntegralScalarExtensionUniverses` is used through the recorded
  integral transitions; its construction is not duplicated.
* `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`; its coefficient-data import supplies the
  existing `PurCompactSupport.completed`, `openAdjunction` and `image`.
* `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` and
  `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`:
  the existing `sfIntrinsicExtensionByZero` and `sfIntrinsicDerivedOpenId`.
* `Sheaf.Paper.SfStrictDirectImageScalarComparison`:
  `IntegralComparisons`, `HasIntegralLaws`, `Comparisons`, `HasComparisonLaws`,
  their integral/rational comparisons and normalized reconstruction.
* `WeilConjectures.CategoryTheory.StageSystem.Functor`:
  `StageSystem.Morphism`, `mapAt`, `functor`, `Hom`, `descNatTrans`;
  its Basic import supplies `tr` and `isoToStage`.
* The ordinary adjunction, exact mapDerivedCategory and rightDerivedFunctorNatIso
  operations construct `completedIdentity`; they are existing general APIs.

Proof-only dependencies already having modules are imported with plain import.
The postponed proof's docstring retains all seven node proof steps, including
coherent-system transposition, faithful coherent reduction, tensor bilinearity,
and same-stage descent. The two proof lemmas lacking Lean records are mentioned
in that plan only; their theorem statements are not required to type this item.

### Edge cases checked

E=L uses the existing unit constraints, rather than replacing them by definitional
identities. E⊂L⊂M uses `tr` and the stage-system associators, and permits ramification.
The lowest quotient is exponent 1 (n=0 in Lean), never the zero quotient t^0.
Zero objects and zero morphisms, empty schemes and identity f impose no nonzero
or nonempty hypothesis. All Hom sums, including an empty sum, are covered by
NatIso naturality. The full-system condition excludes a sign twist of θ or a
phantom modification invisible to separate evaluation. Coefficient and closure
universes remain independent, using the existing small finite-field model.

### Searches

The prescribed msearch calls were made with group Q59 and this item; their exact
responses are in the sandbox `searches.jsonl`.

* LeanFinder: "A natural isomorphism between integral proper direct image functors
  descends compatibly through raw rationalization and the common finite coefficient
  field category". Eight hits (Condensed and DoldKan comparisons); no exact match.
* Loogle: `"NatTrans", "naturality"`. Twelve general naturality hits; none is this
  identity-compactification/scalar/common-stage comparison.
* Mathlib grep, CategoryTheory: `properCoefficientDescent|identity.*[Cc]ompact|
  [Cc]ompact.*[Pp]roper`. No hits.
* LeanSearch: "Natural isomorphism of linear functors descends to raw scalar
  localization and a common stage coefficient category". Eight hits including
  `CategoryTheory.Localization.liftNatIso`, free categories and scalar extension;
  no exact statement, and no replacement for the specified geometric comparison.
* Project rg searches in BOTH `lean/WeilConjectures` and `lean/Sheaf`, including
  the item id, proper/compact-support identity comparisons, coefficient descent,
  and identity-open declarations. No declaration states the item. The search did
  find the existing `sfIntrinsicDerivedOpenId` and stage-system descent APIs,
  which are reused. Generic constant-coefficient/closed-immersion identity lemmas
  have different endpoints or hypotheses and are not exact matches.

No new DAG nodes, dependency replacements, statement corrections or disputed
statements are needed. The node copy changes only `lean`.

## Second reading by Q59

Independent clause-by-clause reading of `properCoefficientDescent` against the node,
its stmt_dep records and the blueprint source place
(prop-weil-proper-compact-coincidence.proof.md, first paragraph). The maintainer's
second reader wrote this section. The delivery's own section was a self-review by the
worker, which it said itself.

Hypotheses:

1. Finite-field datum (p,a,q,k_0,k), prime l ≠ p: `B : FiniteFieldDatum.{u}`,
   `(l : ℕ) [Fact l.Prime]`, `hl : l ≠ B.p`. `B.k` is the algebraic closure k, which is
   correct (the field `k₀` is F_q). `PurCompactSupport.coefficientPrimeUnit l B hl` is
   only a Prop proof, so it adds nothing.
2. Ω = Q̄_l, finite subfields E with O_E, ϖ_E, A_n: `Ω : Type v` with
   `IsAlgClosure (Padic l) Ω`. E ranges over `Index l Ω`, and `Coefficient.{u} l Ω E`
   is the small model. Index n means exponent n+1, so t^0 never occurs. Correct.
3. X, Y separated finite-type k-schemes and f a proper k-morphism: `Over (Spec k)`,
   `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` on the structure maps, with
   `f.IsOver` and `IsProper f`. Nothing stronger is assumed, and the empty scheme is
   allowed. Correct.
4. c_0 = (id_X, f): `Compactification.ofIsProper f`. Correct.
5. θ_E : Rf_!^{c_0} ≅ Rf_* on D^b_c(X, O_E) for every E: `θ E : compactIntegral E ≅
   (D.integral E).image`. The source is the recorded finite integral compact-support
   functor. The target is the normalized strict integral direct image of
   lem-sf-strict, which the node requires through its pinning of b_*. Correct.
6. "Induced term by term by Res_n Rf_{*,n} of the sectionwise identity (id_X)_! ≅ id":
   `InducedOnFullTower`. Here a and b are existential but pinned on every section:
   - a is restriction along `Over.pullbackId.inv`;
   - b is the identity on underlying sections.

   The ring maps agree: `completed.pull g` is the adjoint of `sfCompletedCoefficientMap`,
   so `proEtaleRingDirectImageMap` of it is that map again. So a and b exist and are
   unique, and the hypothesis is not vacuous. θ is then fixed as
   realization⁻¹ ≫ R(direct image)(identity-open, via `leftAdjointIdIso`) ≫
   reconstruction. Both conjugating isos are the pinned published ones
   (`sfQcqsCompactSupportRealization` is an ∃!.choose; `reconstruction` is normalized on
   representatives). Correct, and no twist is possible.
7. "Preserves the chosen derived-limit projections": `PreservesProjections`.
   - The compact side is `sfCompactSupportFiniteReductionIso`, the adjunct of the chosen
     Roos projection, followed by Rf_{*,n}(identity open) (`finiteIdentity`, the same
     construction as Q75's `finiteComparison`).
   - The ordinary side is the adjunct of reconstruction⁻¹ ≫ Rf_*(reduction unit) ≫
     restriction comparison.

   The orientations check. The node assumes this together with 6, so including both is
   not a stronger assumption.
8. b_!, b_* "specified, with identity and successive-extension identifications":
   - `S : SfCompactSupportCoefficientAction` fixes `integralBeta` by its mate spec,
     `system.Φ` by `finite_eq`, and the rational β by `rationalBeta`.
   - `D`, `_hD`, `R`, `_hR` fix the lem-sf-strict integral and rational comparisons with
     their unit and cocycle laws.

   b_* = `(D.integralComparison E L h).inv`, which is the inverse, as the node pins.
   Correct.

Conclusions:

9. b_* ∘ T(θ_E) = (θ_L T) ∘ b_!: first conjunct, for all E ≤ L and K, in diagrammatic
   order `T_Y(θ_E) ≫ b_* = b_! ≫ θ_L(T_X K)`. Types and orientations check against
   `integralBeta : F_E ⋙ T_Y ≅ T_X ⋙ F_L` and
   `integralComparison : T_X ⋙ image_L ≅ image_E ⋙ T_Y`. Correct.
10. θ^rat on the raw rational categories, natural for all finite sums of tensors:
   `r E : S.system.Φ E ≅ R.rational E`, with hom and inv components HEq to the
   localizations of θ.hom and θ.inv. NatIso naturality covers every raw tensor-Hom
   element. Correct.
11. θ_Ω on the pair categories, with component represented by θ^rat(K_E):
   - G is the ordinary stage-system action. It is pinned by `G.Φ = R.rational` and by
     `G.β` HEq `R.theta.inv`, which matches `Morphism.β : Φ_E ⋙ T ≅ T ⋙ Φ_L`; its
     remaining field is a Prop.
   - `e : S.system.functor ≅ G.functor` has components HEq to `inclusion.map (r ...)`.
   - `e.hom = descNatTrans τ`.

   Correct.
12. The naturality equation over the same L, preserved under every further M: the two
   `mapAt` conjuncts, the second for the actual `tr hLM a`. Correct.
13. Independence of the representative (automatic on quotient Hom groups) and of the
   canonical presentation (the `isoToStage` conjunct). Correct.

Edge cases: E = L, ramified E ⊂ L ⊂ M, n = 0 (exponent 1), the empty scheme, K = 0,
the empty sum, and independent universes u, v. None is excluded.

Dependency records: the item node changes only `lean`, and the statement is verbatim. The
statement uses some declarations whose owners are not in stmt_deps. This is a maintainer
advisory only: S2 may not add existing nodes. The owners are:
- def-pur-integral-compact-support-coefficient-data (`PurCompactSupport.completed`,
  `openAdjunction`, `image`)
- def-sp-finite-intrinsic-open-square (`sfIntrinsicDerivedOpenId`)
- def-weil-ambient-exceptional-adjoint (`sfAmbientCompactSupportCandidate`)
- def-weil-integral-derived-reduction (`scalarReductionDerivedExtension`)
- def-weil-pbc-proetale-operations (`proEtaleRingModuleDirectImage`, adjunction)
- def-weil-integral-reduction-tower (`sfDerivedReductionUnit`)

The remaining items are fine. Local helpers are real definitions. The identity-open
comparisons duplicate only declarations in theorem modules (Q75 lem-weil-proper-integral-
tower-comparison), which cannot be cited. The proof docstring carries all seven node
steps.

Change made by this reading: this section only. The Lean and the node are unchanged.
