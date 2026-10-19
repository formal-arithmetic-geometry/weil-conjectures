## Worker report

This packet repairs the mathematical defects in the returned compatibility predicates. The item module is `Sheaf.Paper.VectorBundlePurity`, using five explicit definition modules. All definitions have actual data. The only postponed theorem in this packet is `vectorBundlePurity`. Published scalar adjunction, representative, tensor and pullback comparisons are reused unchanged.

Hypotheses and clauses:

- The finite-field datum, prime different from the characteristic, finite extension and positive quotient level are exactly the fields of `PurityFiniteSetting`. `P.Coefficient` is the lifted finite quotient. `B`, its structural map `hB`, `[LocallyOfFiniteType hB]` and `[QuasiCompact hB]` express finite type over that field. No absolute separatedness assumption on B is added. Noetherian and affine finite-type bundle geometry are derived inside the conclusion.
- Rank is the arbitrary natural number `d`, and `F.IsFiniteLocallyFreeOfRank d` is the recorded vector-bundle input. The total scheme, projection and zero section are the dependency's relative Spec of Sym(F), not replacement geometric data.
- `constructibleFiniteTor` is the existing bounded constructible finite-Tor class. `IntegrationPurity` supplies the unique natural isomorphism on this class, its actual projection-formula normalization and its coefficient-unit value. `VectorPurityGammaNormalized` fixes its inverse family by the Brown-counit equation: inverse projection followed by the actual `vectorBundleIntegration`. This universal characterization determines each component independently of all three compatibility equations. The conclusion explicitly asserts that these gamma components are invertible. The adjunction Hom bijection identifies them with the unique normalized family's inverse components.
- `PurityBaseChangeEquation` quantifies a Cartesian pullback presentation of the bundle over B'. Its second bundle has its own independently `VectorPurityGammaNormalized` family. `purityBundleBaseChangeAssociator` is built from inverse-image tensor and composition comparisons and the normalized Tate-line pullback. The equation is `g'^*.map gamma ≫ exceptionalExchange = a.hom ≫ gamma'`. Exchange invertibility is asserted only at the bounded constructible input K. Neither gamma' nor a is defined from this equation.
- `PurityDirectSumEquation` uses F⊞G and the contravariant relative-Spec maps induced by the actual two generator inclusions. It retains the Cartesian factorization and a compactification triangle. `purityCompactComposition` is the compositor through that triangle and the published compactification-independence isomorphisms. `compositeCompactSupportMate` takes its actual right-adjoint mate. `purityOrderedAssociator` adds the ordered ranks using the Tate tensor associator. `puritySecondFactorGamma` is the base change of the first bundle's unit orientation followed by the canonical dualizing tensor morphism. The equation states the Step-5 composite, with both factor gamma maps and the inverse exceptional compositor. There is no quantifier over arbitrary categories.
- `PurityFiniteReductionEquation` covers every positive m≤P.level and the actual `purityReductionRingMap`. `purityScalarExtension` is the universal derived tensor along that map, on sheaf derived categories. The published `scalarExtensionRepresentative`, `ExceptionalCoefficients.tensorIso` and `scalarPullbackIso` have ordinary tensor-adjunction/K-flat normalizations. The ordinary line comparison is fixed on every pure root tensor by `PurityScalarLineNormalization`; it cannot be selected to fit a purity equation. `purityScalarSourceMap` assembles the scalar tensor, pullback, shift and Tate comparisons.
- The compact-support coefficient arrow q is the published `ExceptionalCoefficients.compactSupportMap` on the chosen compactification (scalar mate of the proper part at the open extension, then proper direct image of the open comparison). b is the published `ExceptionalCoefficients.mateMap`, the geometric adjunct of q⁻¹ followed by the scalar image of the actual geometric counit. The reduction equation is `Q_E.map gamma ≫ b = a_scalar ≫ gamma_m`. It first asserts q invertible, so b is the actual adjunct. The same clause explicitly includes `K = 𝟙_ (DerivedCategory ...)`, the coefficient-unit OBJECT, rather than a ring element. The rank-zero Tate power uses the published normalized `ExceptionalCoefficients.unitIso` with both single/unit identifications (`purityScalarUnitMap`).

Coefficient range (returned F5): the current blueprint `sec-six-functors-basics/sk-def-purity-conv/def-pur-conventions.md` explicitly says “For Λ=A all statements and constructions below are made”; the integral, rational and algebraically closed versions are separate transports in the transport section. The live dependency node ends with this same scope rule. The correction makes Λ=A_{E,n}, n≥1 explicit and states the finite theorem in its ordinary-etale realization. It does not claim an unformalized integral or rational theorem. The finite pro-etale interpretation is the existing comparison/transport defining the constructible exceptional adjoint, as spelled out in `lem-pur-vector-integration-site-comparison`.

Dependency declarations used: `Sheaf.Paper.PurityFiniteSetting` / `WeilConjectures.PurityFiniteSetting`; `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` / `VectorBundleZeroSection.scheme`, `π`, `antiEquivalence`; `Sheaf.AlgebraicGeometry.VectorBundleIntegration` / `Etale.vectorIntegration_geometry`, `vectorIntegrationCoefficient`, `vectorBundleIntegration`, `vectorIntegrationBaseCoefficientPullback`; ordinary `Etale.rightDerivedLowerShriek`, `rightDerivedUpperShriekAdjunction`, `projectionMap`, `rightDerivedUpperShriekBaseChangeMap`, `dualizingComplexBaseChangeMap`, `dualizingComplexTensorMap`; lower-shriek `rightDerivedLowerShriekOfCompactificationCompIso` and `rightDerivedLowerShriekIso`; `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` / `SheafOfModules.DerivedChangeOfRingsCochainModel` and `nonempty_derivedChangeOfRingsCochainModel`.

Edge cases checked: d=0 and either direct-sum rank zero use the zero-fold Tate tensor and monoidal unitors; the empty scheme remains allowed; m=n is the actual identity quotient case; m=0 is outside the source's positive-level range; ramified extensions and levels not divisible by ramification are retained; no flatness of the quotient A_m over A_n is imposed. The finite-reduction scalar tensor uses K-flat resolutions, not underived tensor. The exceptional exchange is restricted to bounded K. The earlier all-small-categories endomorphism counterexample no longer instantiates any clause.

Searches: the retained stage-2 node records the original `msearch.py` LeanFinder/Loogle searches for vector-bundle purity, affine integration/duality and projection/adjunction (no exact theorem), and grep in Mathlib and upstream (only abstract categorical and coefficient machinery). In this repair `rg` searched the project and upstream for `scalarExtension`, `scalarRestrictionPullbackIso`, `rightDerivedLowerShriekOfCompactificationCompIso`, `mapDerivedCategorySingleFunctor`, `finiteEtaleTateOneGenerator`, and `sfFixedOpenRestriction`. Their full signatures and normalization docstrings were read. The existing constructions are reused. The final scalar aliases are transparent names for published interfaces; no new independent scalar notion or postponed comparison is introduced.

## Dependency modules

None. The returned §1(B) rebind of `lem-pur-derived-change-of-rings` is removed. Its
NZ record remains `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel` in
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`, with its independent
localization universes and full universal property. No dependency JSON is delivered.

The reduction module imports `Sheaf.Paper.ExceptionalCoefficientComparison` and
`Sheaf.Paper.PurEtaleScalarMateProjection`. It uses the published
`AlgebraicGeometry.Etale.scalarExtension`, `scalarExtensionRepresentative`,
`scalarPullbackIso` and `ExceptionalCoefficients.tensorIso`. `purityScalarExtension`
is an abbreviation for `scalarExtension`; `purityScalarPullback` is an abbreviation
for `(scalarPullbackIso φ f).symm`; `purityScalarTensor` takes the `(K,L)` component of the
published natural isomorphism. The scalar adjunction uses the existing
`ProEtale.pbcRestriction_isRightAdjoint` / `pbcFixedScalarExtension` from
`Sheaf.Paper.WitnessCompatibility`; its ordinary version uses
`ProEtale.etaleSheafExtendScalarsAdjunction`. There is no new IsRightAdjoint theorem,
representative-isomorphism theorem, tensor-existence theorem or pullback-isomorphism
theorem. The item cites the scalar-owning nodes in `stmt_deps`, including
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pur-etale-scalar-mate-projection`, `lem-pur-exceptional-coefficient-comparison`,
`def-weil-pbc-witness-compatibility`, and `lem-fix-operation-reduction`.

## Second reading by NG

This is a dispatcher self-check; no subagent was started. I read the retained Lean
and node records against both numbered defects of immutable return 49ec8d2ffe2c.
H13/H4 is repaired by removing `PurityScalarChangeOfRings` and its dependency
rebind, and by using the published scalar adjunction, representative and normalized
comparisons. A further source search found the already landed
`ExceptionalCoefficients.tensorIso`; the saved duplicate scalar tensor theorem and
its new definition node were removed too. The only `sorry` left in the five-file
packet is the item's theorem, matching the item's DAG statement.

H3 is repaired in `PurityDirectSumEquation`: following the real sum-bundle
projections, `HasCompactification p`, `HasCompactification h`,
`HasCompactification q`, `QuasiCompact q`, and `QuasiCompact p` are universal ambient
instance binders. The geometric equation `w` and Cartesian witness `sq` are also
universal; then `∀ (c : Compactification p) (e : Compactification (q ≫ c.i))`
requires the Step-5 equation for every actual triangle. The independently normalized
factor and sum gamma families remain existential because the theorem supplies
them. Ranks zero, identity reduction, empty schemes and non-flat quotient maps
remain included. The integration, base-change and finite-reduction clauses were
retained with their explicit unit-object clause.

The initial retained-packet dry run failed concretely at the opaque scalar alias:
Lean could not identify it with `scalarExtension` in the published pullback
comparison, scalar adjunction and representative. Transparent reuse of the
published scalar functor fixes all three without a new axiom or construction.

Further searches: `msearch.py ... loogle "scalarExtension, tensor"` returned
`[loogle] OK 0 hit(s) | loogle: unknown identifier 'scalarExtension'`.
`rg` across Mathlib, upstream WeilConjectures and the project found
`scalarExtensionRepresentative` / `scalarTensorIso` in `EtaleDerivedScalarTensor`
and `ExceptionalCoefficients.tensorIso` in `ExceptionalCoefficientComparison`.
The latter has exactly the strong tensorator and representative normalization
needed here and is now reused. The scalar/pullback and tensor source declarations,
full signatures and normalization docstrings were read. A source-only traversal of
all statement and proof dependencies from `lem-pur-exceptional-coefficient-comparison`
visited 10,729 nodes and found no path back to this item, so the reuse closes no cycle.

## Return-entry resolution

- H13/H4: restore NZ's landed change-of-rings record; remove the duplicate scalar
  adjunction and comparison theorems; reuse the published owning-node declarations
  and cite their nodes. No missing scalar prerequisite remains.
- H3: universal ambient instances and universal compactification triangles in the
  direct-sum equation, with the actual ordered two-factor composite retained.

## Statement corrected

The old statement is retained verbatim in `statement_change.old_statement`. Its ambiguous coefficient variable is resolved using the current source's finite-part scope paragraph. The compatibility prose is expanded into the three equations of sk-prop-an Steps 4–6 for the actual normalized maps. The earlier false generic-category conjunct and tautological witnesses are removed. The derived scalar-extension dependency is now cited explicitly. No blueprint unit's mathematical assertion is changed.

- `lem-pur-orientation-ground-field-retagging`: holds. Its normal-bundle argument is at finite Z/l^m and A_{E,n}; the later tower claim transports those normalized finite maps.
- `det-sp-orientation-charts`: holds. Uses arbitrary pullback of the normal bundle at finite Z/l^n and the same integration-normalized unit orientation.
- `thm-pur-composition-coherence`: holds. Uses the ordered direct-sum law and base change for finite A; rank-zero cases use the coefficient-unit associator.
- `lem-pur-finite-universal-smooth-trace`: holds. Uses the integration-adjoint normalization at R and at the finite free extension B; both coefficient stages are finite quotients.
- `det-sp-orientation-vector-bundle`: holds. Compares the diagonal orientation with the inverse integration mate for finite Z/l^n; this is the retained normalization.
- `det-sp-purity-bc-factors`: holds. Its proof applies this result first at R=Z/l^n; general finite rings and varying towers are obtained using its separate scalar and tower steps.
- `prop-pur-dnc-family-constancy`: holds. Uses the unit orientation for trivial rank-d bundles and its arbitrary base change, explicitly with Lambda=A_{E,n}.
- `det-sp-finite-general-ring`: holds. Uses this corollary at R=Z/l^n; its separate trace-and-chart argument then extends to arbitrary finite A.
- `sk-lem-geometry`: holds. The standard-pair family is computed by finite-coefficient rank-d unit purity and then pulled back along the affine-line projection.
- `lem-pur-dnc-section-geometry`: holds. Its standard-pair clause uses only the finite-coefficient unit orientation of a trivial vector bundle.
- `lem-pur-diagonal-dnc-chart-normalization`: holds. Uses finite A_{E,n}, normal-bundle zero-section pullback, base change and direct-sum normalization, all retained explicitly.
- `sk-thm-dnc`: holds. The stated prime-power finite coefficient setting uses trivial-bundle unit purity on the coordinate charts.
- `thm-pur-finite-reduction-of-purity`: holds. Its last diagonal factor is reduced by the actual b_{n,m} square, including K=the coefficient-unit object.
- `thm-pur-finite-coefficient-smooth-purity`: holds. Uses the integration-normalized vector-bundle unit map for arbitrary finite A_{E,n}, not an integral purity theorem.
- `lem-pur-vector-integration-site-comparison`: holds. Identifies precisely the ordinary-etale integration transpose and its inverse with the finite pro-etale vector-bundle map.
- `thm-pur-diagonal-dualizing-object`: holds. Its proof explicitly takes A=A_{E,n} and pulls the bundle unit orientation back to the zero section before gluing.

## New nodes

- `def-pur-vector-purity-normalization` (`Sheaf.Paper.VectorPurityNormalization`) defines the actual integration/counit normalization, its unique purity isomorphism and normalized inverse family. Its source is the vector-bundle integration proposition and Steps 1–2. The generic category helpers merely factor this same condition.
- `def-pur-vector-purity-base-change` (`Sheaf.Paper.VectorPurityBaseChange`) defines the actual pullback/twist associator and the independently normalized base-change equation of Step 4.
- `def-pur-vector-purity-direct-sum` (`Sheaf.Paper.VectorPurityDirectSum`) constructs the symmetric-algebra projection maps, ordered Tate associator, compactification compositor and its right-adjoint mate, then defines precisely the Step-5 equation.
- `def-pur-vector-purity-finite-reduction` (`Sheaf.Paper.VectorPurityFiniteReduction`) constructs quotient scalar maps and the exceptional counit mate, then defines the Step-6 equation, including the actual coefficient-unit object.

- `def-pur-vector-purity-scalar-single` (`Sheaf.Paper.VectorPurityScalarSingle`)
  defines the canonical degree-zero scalar comparison as the derived-adjunction
  transpose of the ordinary scalar unit followed by the exact restriction/single
  comparison. Its coefficient-unit specialization postcomposes with the ordinary
  oplax unit, and its derived-unit specialization includes both single/unit isomorphisms.
  The source is the coefficient-reduction paragraph of the current vector-purity proof,
  with the scalar adjunctions and Stacks 06YY.
  Scalar functors, pullback and tensor comparisons remain aliases for published ones.
  LeanSearch returned eight scalar-tower/graded-algebra hits; LeanFinder returned eight
  sheafification/module-pullback hits; neither provided this scalar/single transpose.
  Loogle did not resolve the searched name. Mathlib/upstream grep found no such map.
  Project grep found only the completed pro-etale reduction map and an exact-restriction
  direct-image theorem; their signatures and docstrings were read and have different
  categories and purposes. Mathlib's exact restriction/single comparison is reused.
  DAG and blueprint search found no existing node for this ordinary-etale comparison.

These define the four compatibility predicates and their canonical maps; no new theorem is postponed in them. For each, Mathlib LeanSearch returned direct sums of algebraic base-change data and topological vector bundles, LeanFinder returned tactic/module normal forms, Loogle returned zero matches, and Mathlib/project/upstream grep found no declaration of these normalized equations. The definition-node records include the actual queries and results. DAG/blueprint search located the existing integration and purity theorem nodes but no definition of these predicates. All existing trace, adjunction, scalar and geometric operations are reused.


LeanFinder query `canonical derived scalar extension tensorator normalized on K-flat complexes`
returned eight hits (`CategoryTheory.Tor`, `Tor'`, flat-module exactness and flat
scalar-extension preservation), none giving the needed etale tensorator. The project
source search above supplies the exact existing comparison.

The scalar shift is the data `(purityScalarAdjunction φ T).leftAdjointCommShift ℤ`
inside the recursive power construction. It reuses the actual restriction/scalar
adjunction and introduces no new theorem or assumption. The signature records
were checked verbatim, and the current citer audit is exactly the 16 retained entries.

Final orientation check: the published `scalarPullbackIso` points from scalar-then-
pullback to pullback-then-scalar. The reduction source map needs the reverse, so its
transparent alias is `(scalarPullbackIso φ f).symm`; the displayed reduction equation
and its endpoints are unchanged.

## Final validation

`deliver2.py NG cor-pur-vector-bundle-purity --no-push` returned
`OK (dry run)` at `b4097e9064`: all five modules compile at their recorded paths
with no errors or non-sorry warnings, and the maintainer preflight passes. The
packet restores the original NZ dependency record by omitting any dependency edit.
The four definition nodes have real constructions and no postponed theorem; only
`vectorBundlePurity` is postponed. The delivery command repeats the required checks.


## Retained-packet repair validation (2026-10-18)

Following the dispatcher instruction, the first action after reading this report was
`deliver2.py NG cor-pur-vector-bundle-purity --no-push` on the saved five-file packet.
It returned `OK (dry run)` at `f7b8a146f5` after current-server confirmation. The
private-overlay finite-reduction file compiled in 57.8 seconds; a later temporary-name
direct-sum compilation timed out locally, so the prescribed wrapper confirmed the
packet against current server sources and accepted it. No limit was raised, no
compiler or launcher tool was changed, and no file was split for this repair.
The saved Lean work is retained exactly as instructed after a passing initial dry run.

The self-check reopened all five module files and their five node records. Every
primary recorded signature matches its file verbatim. All four definition modules
have real constructions and no `sorry`; the single postponed theorem remains
`vectorBundlePurity`. `autoImplicit false` is explicit in every module, and the
universes and variables are explicitly bound. The current shared DAG has exactly
the same 16 citers as `statement_change.citers`, with no missing or extra entry.
The item's delta from the current shared node is confined to `lean`, `statement`,
`statement_change`, and `stmt_deps`; the four definition nodes remain new.

The reading checked the finite coefficient scope against the current
`def-pur-conventions.md`, the bundle projection against the recorded relative-Spec
construction, and the scalar comparison against the published `scalarPullbackIso`
and `ExceptionalCoefficients.tensorIso` signatures and their representative
normalizations. It also checked the positive-level quotient, ordered rank-zero
unitors, universal compactification triangles, and explicit derived coefficient-unit
component in the retained equations. No mathematical signature changed in this retry.
The released repair note is stage 1, concerning proof splitting, and does not
withdraw or rebind this stage-2 statement interface.

## Timeout repair of immutable head b1ff296db89a

The required first retained-packet dry run reproduced the returned failure on both
compiler paths: normalization passed in 21.0 s, base change in 7.1 s, direct sum in
25.0 s, and finite reduction timed out after 60 s on current server sources. It
therefore did not qualify for the instruction to retain a packet that passes its
first dry run. The subsequent generic-helper-only attempt also timed out.

The repair separates the canonical degree-zero scalar comparison into the new
`def-pur-vector-purity-scalar-single` node and module, cited by the item and the
finite-reduction definition. This separates the scalar/single construction from
the quotient-reduction predicate; it does not split an individual Lean invocation,
raise the limit, or change any launcher tool. The moved declarations keep their
names and types. Two generic categorical helpers factor the same adjunction
transpose and single/unit transport, with explicit universes and real data.
Their bodies unfold to the previous displayed composites. The finite-reduction
predicate, the three compatibility equations and the theorem signature are unchanged.

The self-check reopened all six modules and their node records. It checked the
actual ordinary and derived adjunctions, the exact restriction/single isomorphism,
the ordinary oplax unit, and both single/unit identifications. In particular,
`purityAdjunctionSingleMap` specializes its abstract functors to the published
scalar and restriction functors; it makes no additional assumption in the item.
`purityTransportUnitMap` is exactly functorial mapping of the inverse source
identification, followed by the supplied unit arrow and target identification.
The new node's source, dependencies, searches, declaration ownership and signature
are recorded explicitly. The original coefficient range, rank-zero and identity
reduction cases, and all 16 citer-audit entries remain intact.

The repaired `scompile.py` check passed for all three requested files and their
recorded module paths. `VectorPurityScalarSingle` took 33.3 s at its recorded path;
`VectorPurityFiniteReduction` took 54.3 s (39.7 s in the temporary-name check).
Normalization took 25.7 s at its recorded path. All invocations kept the prescribed
60-second limit and reported no errors or warnings. The full six-module delivery
dry run is the next validation step.

The complete repaired six-module packet then passed
`deliver2.py NG cor-pur-vector-bundle-purity --no-push` at `4d914c0e43`:
`OK (dry run): commit 4d914c0e43 passes the preflight and compiles; nothing pushed`.
Every delivered module compiled at its recorded path, including the unchanged
`vectorBundlePurity` theorem on the separated definitions. The normal delivery
command performs its required checks and push next.

## Reviewer fix (stage-2 maintainer review of 4f405667cced)

H4 (one definition per notion), the finding of the b1ff296db89a review, which was not carried into this delivery:
`VectorPurityFiniteReduction` again built its own q (`purityScalarOpenRestriction`,
`purityScalarCompactRestriction`, `purityScalarCompactMap`) and b (`finiteReductionMate`).
`VectorPurityScalarSingle` built its own scalar unit (`purityScalarSheafUnit`,
`purityScalarDerivedUnitMap`). The imported, landed `Sheaf.Paper.ExceptionalCoefficientComparison`
(lem-pur-exceptional-coefficient-comparison) already publishes these maps for an arbitrary φ as
`compactSupportMap`, `mateMap` and the normalized `unitIso`.

- `VectorPurityFiniteReduction`: the four duplicate declarations are removed.
  `PurityScalarReductionEquation` now asserts the following at every ctf K and at K = 𝟙:
  - `IsIso (compactSupportMap φ (compactification π) (Rπ^!K))`, `IsIso a_scalar` and `IsIso (mateMap φ π K)`;
  - `Q_E.map (γ.app K) ≫ mateMap φ π K = a_scalar ≫ γm.app (Q_B K)`.
  The invertibility conjuncts for the restriction arrow and the derived unit existed only to invert the
  duplicates, so they are dropped. The generic-ring factoring and `PurityFiniteReductionEquation` are unchanged.
- `VectorPurityScalarSingle`: `purityScalarSheafUnit` and `purityScalarDerivedUnitMap` are removed.
  `purityScalarUnitMap` (same name and type) is now `unitIso` transported along both
  single/unit identifications by the existing `purityTransportUnitMap`.
  `purityScalarSingleMap` and the aliases are unchanged.
- Node records: both definition nodes get a matching statement, `lean.declarations` and `lean.note`.
  The two unused theorem citations are dropped from the finite-reduction node.
  Every `lean.statement` is unchanged and verbatim.
- Compile, `nt_compile.py --json`, all six modules, load ~97: no errors and no warnings.
  Normalization 31.0 s, BaseChange 8.5 s, DirectSum 24.5 s, ScalarSingle 21.2 s,
  FiniteReduction 28.0 s, VectorBundlePurity 7.1 s. The delivered files took 40.2/17.0/25.6/23.8/33.6/10.0 s
  at load ~111.
