## Worker report

The delivery states `lem-sfb-closed-test-chain-mate-restriction` in
`Sheaf.Paper.ClosedTestChainMateRestriction`, namespace
`AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction`. The node's statement,
proof, source and proof dependencies are unchanged. Its statement dependencies gain
`def-sfb-closed-test-kinjective-section-maps` for the canonical representative and
localization definitions, and the already landed
`def-sfb-closed-test-derived-exchange-maps` for the exchange/restriction definitions.
The section-model theorem is not a statement dependency. There is one new
definition ownership node, no dependency module repair, and no statement correction.

There are three postponed theorems, all owned by this node and all proved by
`sorry`: `closed_test_mate_sections` (ordinary section calculation),
`closed_test_chain_mate_restriction` (derived representative, chain evaluation and
normalized restriction), and `closed_test_localized_adjunctions` (unit/counit
compatibility). Their docstrings carry, respectively, proof steps 1–2, 3–6, and 7.
All helper definitions contain their actual constructions. None chooses a map from
an existence assertion or assumes an arbitrary comparison.

Hypotheses and objects, clause by clause:

- The arbitrary commutative condensed ring is
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `MonObj Λ` and
  `IsCommMonObj Λ`. This is the underlying-object presentation of the recorded
  `Profinite.CondensedRing`; no topological presentation or discrete coefficient
  hypothesis is added.
- The coefficient on a scheme Y is exactly `condensedRingObj Λ Y`, the recorded
  point pullback. Internal modules are
  `Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)`.
  Ordinary inverse and direct images are `CondensedRing.upperStar` and
  `CondensedRing.lowerStar`, with the specified
  `CondensedRing.upperStarLowerStarAdjunction`. Exact inverse image on derived
  categories is its `mapDerivedCategory`; ordinary unbounded derived direct image
  is its `rightDerivedFunctor`, the body of the recorded
  `CondensedRing.moduleObjectDerivedPushforward`. The exact construction avoids
  adding any K-flat or preservation hypothesis to the node.
- Every scheme uses universe u and every section value `Ab.{u + 1}`. The small
  sites retain their native object and morphism universes; no universe equality
  is imposed on a generic-site API. All variables and universes are explicit,
  with `autoImplicit false`.
- `A : Type u`, `[CommRing A]`, and `a : Ideal A` introduce precisely A and its
  ideal. `closedMap A a` is `Spec.map` of `Ideal.Quotient.mk a`, so s is the
  specified quotient closed immersion, not an additional arbitrary immersion.
- `liftedTest A a V` uses the recorded `Scheme.AffineProEt.closedSiteLift` v;
  `closedTest A a V` is V in the full small site. The binder
  `V : (Spec (.of (A ⧸ a))).AffineProEt` gives the affine ind-etale test.
  The two `IsWContractibleRing Γ(..., ⊤)` instances are exactly the hypotheses
  that V and B=v(V) are w-contractible. Neither is inferred from the other or
  dropped.
- `[IsAffine X]`, `f : X ⟶ Spec (.of A)`, and
  `w : IsPullback h fZ f (closedMap A a)` give the affine morphism and the
  cartesian square with its named projections. An arbitrary specified pullback
  cone represents X_Z, rather than requiring a particular chosen pullback object.
  Its affineness follows from that square and is not an extra assumption.
- `testFibre f (liftedTest A a V)` is T and
  `testFibre fZ (closedTest A a V)` is T0. These are Mathlib's scheme fibre
  products with factors ordered B×_U X and V×_Z X_Z, respectively; this is the
  same canonical geometric test with the projections retained.
  `testArrow A a w V` is the actual closed map a:T0→T, constructed in the
  existing section-model module from the closed-site inclusion and the square.
- `K : DerivedCategory.Plus (...)` is cohomologically bounded below, while L and
  J are genuinely unbounded `CochainComplex ... ℤ`. `[L.IsKInjective]` and
  `e : DerivedCategory.Q.obj L ≅ K.obj` specify the representative I.
  `[J.IsKInjective]`, `j : (complexes (upperStar Λ h)).obj L ⟶ J`, and
  `[QuasiIso j]` give the supplied K-injective resolution. There is no degreewise
  lower-bound assumption on L and no monomorphism assumption on j.

Conclusions and normalization, clause by clause:

1. `ordinarySquare` is the canonical theta, using `upperStarComp` and the actual
   commutativity equality. `ordinaryExchange` is literally
   `Adjunction.squareExchange` for the two specified adjunctions and theta. Thus
   its formula is the unit followed by the image of theta and the counit, as in
   the node; it is not a map merely asserted to have an adjunct.
2. `closed_test_mate_sections` says that precomposing the evaluated ordinary
   exchange by the actual `closedUnit` gives `testSectionUnit`, under both
   `pushEvaluation` section identities. The closed-unit map is the map whose
   inverse is used in the prose; its invertibility is supplied by
   `closed_test_unit_evaluation` and the section-model theorem, so this equation
   is equivalent to the node's description using its inverse. Explicit functor
   associators only arrange the specified composites.
3. `testSectionUnit` inserts the actual h-adjunction unit and then restricts along
   `testSectionArrow`. This arrow is the canonical T0→h^{-1}T map over X_Z.
   Under `testPullbackComposition` it is the actual a-adjunction unit on the
   localized module. It is therefore F(T)→(h*F)(T0), with the stated coefficient
   identification, not a freely chosen restriction map.
4. `chainMate` is exactly the termwise `ordinaryExchange` followed by
   `(complexes (lowerStar Λ fZ)).map j`; explicit
   `mapHomologicalComplexCompIso` factors identify termwise composition. The
   first conjunct of `closed_test_chain_mate_restriction` identifies its Q-class,
   followed by `pushModel` at J and `pullRepresentative`, with the existing
   `ClosedTestDerivedExchangeModel.exchange` at K. The source comparison is the
   exact inverse-image localization factor followed by the f-pushforward model.
   The existing exchange is defined as the specified derived adjunction mate;
   its adjunct is therefore exactly h*epsilon_f composed with theta.
5. `evaluatedExchange` is the ordinary exchange evaluated under the actual closed
   unit and the literal section formulas. `evaluatedChainMate` applies it in
   every degree and then evaluates j. It assembles the ordinary composition
   before applying `mapHomologicalComplex`; this is evaluation of `chainMate`
   with the canonical composition factors. The second conjunct asserts equality
   with `sectionChain`, whose body is exactly the actual unit-section map
   I(T)→(h*I)(T0) followed by j(T0). The equality is of chain maps and hence of
   their Q-classes, with no passage to cohomology.
6. `globalLocalizationModel` reuses the existing `localizationModel`, changing
   only its final-object evaluation encoding via `terminalSections` (an
   `Iso.refl`). The third conjunct identifies the Q-class of `sectionChain`
   under these canonical localization maps with the existing
   `ClosedTestDerivedExchangeModel.restriction` along `testArrow`. The final
   factor is the inverse of `derivedTestPullbackComposition`, so its target is
   the specified localized h*K, with no coefficient comparison discarded.
7. The existing `restriction` is defined as the specified derived unit followed
   by `pushDerivedSectionsIso`. The latter is
   `rightDerivedFunctorCompIso'` on the literal `pushSectionsIso`, using
   K-injective preservation by the exact-left-adjoint criterion. It therefore
   has exactly the degreewise normalization Γ(T,a_*J0)=Γ(T0,J0) required in the
   node, including use of the identity resolution when the complex is already
   K-injective. No new adjunction is placed on an isomorphic functor.
8. `closed_test_localized_adjunctions` asserts that the ordinary and derived
   direct-image pasting comparisons are the conjugates of the corresponding
   specified pullback comparisons. Conjugacy is the unit/counit preservation
   condition for the two adjunctions. Its first two conjuncts use the actual
   testPullbackComposition and derivedTestPullbackComposition for h and a.
   Its other conjuncts apply `pastingAdjunctionCompatible` to localization of f
   at B, fZ at V, and s at V, with their literal scheme pullback squares. Thus
   the localizations used in the argument, as well as derived composition, are
   covered. The derived compositor in `derivedDirectSquare` is the existing
   right-derived compositor with its specified universal units.
9. No conclusion states that exchange or restriction is invertible. Only the
   previously specified comparison isomorphisms and the given quasi-isomorphism
   are inverted.

The main theorem uses `HEq` for its two derived-arrow equalities, and the
compatibility theorem uses `HEq` for its isomorphism equalities. The two sides
have the same mathematical source and target; their presentations contain
functor-composition and localization encodings. `HEq` records equality of the
actual arrows, including equality of their types. It does not mean existence of
an unspecified isomorphism, equality up to arbitrary transport, or equality
only on homology. It avoids expensive kernel conversion of those presentations.
The chain-map equality and ordinary natural-transformation equality use `Eq`.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` and its
  unbundled monoid-object presentation.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology and
  `AffineProEt`; `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` and exact pullback interfaces.
- `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift`:
  `Scheme.AffineProEt.closedSiteLift`; the affine properties module supplies its
  canonical inclusion and cartesian square.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing`.
- Mathlib pullback and closed-immersion modules: `pullback`, its projections and
  universal arrow, `IsPullback`, and `IsClosedImmersion`.
- `Sheaf.CategoryTheory.AdjunctionSquareExchange`:
  `CategoryTheory.Adjunction.squareExchange`, with its specified adjunct formula.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`:
  `ProEtaleTensorComparison.inverseSection` (the unit-section convention).
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit and object
  comparison; Mathlib `DerivedCategory`, `DerivedCategory.Plus`, `Q`, and
  `CochainComplex.IsKInjective` supply the recorded category conventions.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, and the associated section restriction.
- `Sheaf.Paper.ClosedTestKInjectiveSectionModels`: `evaluation`, `complexes`,
  `pushEvaluation`, `closedMap`, `liftedTest`, `closedTest`, `testFibre`,
  `closedUnit`, `evaluationMap`, `testArrow`, `pullRepresentative`, `pushModel`,
  `localizationModel`, `testPullbackComposition`,
  `derivedTestPullbackComposition`. These 15 plain definitions are owned for this
  statement by `def-sfb-closed-test-kinjective-section-maps`; the theorem is not
  used in the statement or in these definitions.
- `Sheaf.Paper.ClosedTestDerivedExchangeModel`: only the already existing
  canonical definitions `exchange`, `square`, `adj`, `restriction`,
  `pushSectionsIso`, `pushDerivedSectionsIso`, and `sectionsOver`, with their
  exported coefficient/category instances. Its downstream theorem is not used.
- Proof imports: `Sheaf.Paper.ClosedTestUnitEvaluation.closed_test_unit_evaluation`,
  the normalized resolving-derived-adjunction theorem in
  `Sheaf.SixFunctors.ResolvingDerivedAdjunction`, K-injective restriction in
  `Sheaf.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses`, derived
  composition in `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
  the adjunction normalization theorem in
  `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`, and
  the inverse-image construction in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
  The exact-left-adjoint K-injective preservation and composition APIs are the
  existing upstream RightDerivedFunctor.Comp declarations.

Import-cycle note for the maintainer: `ClosedTestDerivedExchangeModel` owns the
canonical exchange/restriction definitions already used above. Their definition
owner `def-sfb-closed-test-derived-exchange-maps` is now cited in stmt_deps. The
separate theorem node `lem-sfb-closed-test-derived-exchange-model` lists this item
as a proof dependency; its downstream theorems are not used here and that theorem
node is not added to stmt_deps. Under stages/2-statements.md §3.7, omit the
reverse proof import of this new module into that existing module: it would
close an import cycle. The definitions have not been duplicated. The proof-only
sibling `lem-sfb-closed-test-localized-model-coherence` has no recorded module in
the read checkout; no import of an unstated proof node is invented.

Edge cases checked against the formulas: a=0 gives the canonical identity closed
square, with the actual unit and compositors retained. a=top permits the zero
quotient and empty closed tests; there is no nonzero-ring or inhabited-test
assumption. Empty V is allowed by the same scheme-site constructions. f=id and
K=0 give the specified identity/unit or zero maps, without asserting an
unavailable inverse. A bounded-below derived K may have an unbounded K-injective
representative; the statement retains this case. The supplied j may be any
quasi-isomorphism into a K-injective, including a nonmonomorphic one. None of the
arguments assumes h*I K-injective. No disputed statement or mathematical node
fault was found.

Searches actually run for an existing statement/notion:

- `msearch.py ... leanfinder`: “Closed pro etale base change mate on K injective
  complexes evaluated on closed tests equals the normalized derived adjunction
  unit restriction”. Eight general adjunction/sheaf hits, including
  `Adjunction.derivedε_fac_app` and sheaf-module adjunction unit/counit
  applications; no closed-test chain statement.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.squareExchange,
  CategoryTheory.Adjunction.derived_unit`. Zero results, with unknown identifier
  `squareExchange` (it is project-local); this is recorded as a query limitation,
  not evidence that the local declaration is absent.
- `msearch.py ... grep`: `(closed_test|closedTest).*(mate|restriction)|squareExchange`
  in Mathlib. Zero results.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for closed-test mate,
  restriction, chain-mate and this node id. It found the downstream
  `ClosedTestDerivedExchangeModel` canonical maps and its different derived
  exchange theorem, and the prerequisite section-model module. Those maps are
  reused; neither theorem states this node's chain representative and unit
  normalization. Upstream `boundedConstructibleBaseChange_eq_squareExchange`
  is a general mate formula, not the closed-test calculation.
- The prescribed `grep -rn` of this item id in `lean/WeilConjectures` returned
  no occurrences. The full statement is not an existing declaration.

Compilation uses only the prescribed `scompile.py`. Explicit associators and
homological-complex composition isomorphisms remove costly implicit conversions;
evaluation is composed before passage to complexes. The final file contains no
diagnostic commands, local notations, auto-bound variables, new axioms, or
proof-bearing definitions with `sorry`. Validation and delivery results follow
from the prescribed server compile and delivery wrapper outputs.

## New nodes

`def-sfb-closed-test-kinjective-section-maps` records existing definitions in
`Sheaf.Paper.ClosedTestKInjectiveSectionModels`, without adding a Lean file.
Its `lean.declarations` lists exactly evaluation, complexes, pushEvaluation,
evaluationMap, closedMap, liftedTest, closedTest, testFibre, closedUnit, testArrow,
pullRepresentative, pushModel, localizationModel, testPullbackComposition, and
derivedTestPullbackComposition, with their full namespace. The primary signature
is copied verbatim from `pushModel`. The definition statement describes each
construction and asserts no K-injective preservation or invertibility theorem.
The sources are Stacks 09BL (closed unit), 0D6F (section localization), and
08BJ/015F (derived and exact-pullback conventions).

The new LeanSearch and LeanFinder queries, respectively “Canonical closed test
K injective section evaluation localization and pullback composition maps” and
“Closed test K injective section evaluation localization representative maps”,
each returned eight general section/localization hits and no exact construction.
Mathlib grep for `closedUnit|localizationModel|derivedTestPullbackComposition|pushEvaluation`
returned five unrelated monoidal closed-unit hits. Project grep located the exact
existing section-model definitions; DAG grep located only their theorem node.
`blueprint_refs.py search 'closed test section'` returned zero hits, and ancestor
reported null, as in the item's recorded ancestry. The new node stores the actual
search result records. This node supplies missing definition ownership, not new
mathematical data or a duplicate definition.

## Returned-delivery repair

For L's return on immutable head `4560c431fba1`, the theorem-only addition
`lem-sfb-closed-test-kinjective-section-models` is replaced by the new definition
owner, and the landed `def-sfb-closed-test-derived-exchange-maps` is cited directly.
The latter owns the used `exchange`, `restriction`, `adj`, `square`, `sectionsOver`,
`pushSectionsIso` and `pushDerivedSectionsIso`. The ownership note above is
corrected accordingly. Relative to current main, the item's only changed fields
are `lean` and addition of these two definition nodes to `stmt_deps`. The main
statement, proof, proof_deps and Lean module are unchanged from the returned
packet; the three postponed theorems remain exactly as independently accepted.

Self-check: opened the existing definition bodies and checked that these 15
declarations do not use the section-model theorem or a choice from it; checked
that the new node cites only definition nodes and claims no isomorphism of the
closed unit or representative/localization maps. The previous edge-case checks
remain applicable. The saved packet's initial dry run passed preflight and
compilation before these ownership corrections. The repaired packet is validated
again by the prescribed delivery wrapper.

The first repaired-packet preflight requested the current new-node schema field
`import_flags`; it is supplied as an empty list. Its two combined coefficient/site
citations are also written separately to satisfy the literal citation advisory.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
