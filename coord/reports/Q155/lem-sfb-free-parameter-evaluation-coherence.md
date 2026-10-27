## Worker report

This packet retains the six modules and their canonical closed-derived-Hom
interfaces. The repair of return L at immutable head 07d4261482bb removes the
two duplicate theorems and the duplicate whole-family map from
FreeParameterRelativeMaps. That module now imports
Sheaf.Paper.ProfiniteConstantDerivedFunctions, and restricted_whole_family uses
the existing ProfiniteFunctions.familyParameterMap and familyParameterMap_over
directly. The existing testSchemeFunctor_preservesFiniteLimits supplies the
finite-limit instance. No statement of the item, proof plan, or existing
dependency is changed. All data definitions remain explicit constructions; only
named theorem/instance proofs are `sorry`.

The required first dry run on the saved packet passed as ed0ee4b5d3d. The
subsequent self-check confirmed the return still applied, so the work was retained
and the duplicate declarations repaired before delivery.

Returned points repaired:

- L / H4: removed `FreeParameterEvaluation.parameterSchemeFiniteLimits` and
  `FreeParameterEvaluation.familyParameterMap_over`. Also removed the duplicate
  `FreeParameterEvaluation.familyParameterMap`; the coherence statement now names
  `ProfiniteFunctions.familyParameterMap` and its existing over-equation directly.
  These generic geometric helpers have explicit binders `X : Scheme.{u}`,
  `Q P P' : Profinite.{u}`, `α : Q ⨯ P' ⟶ P`; the finite-limit theorem has only
  `u`. None has an `R`, field, Kummer, coefficient, or beta/c binder. Both
  testScheme/projection abbreviations unfold to the same profiniteToProEtOf
  construction. This import is the reuse expressly requested in return L;
  no downstream evaluation or comparison is used. The parent node lists this
  item as a proof dependency; the reverse proof import must be omitted under
  stages/2-statements.md §3.7 to avoid a module-import cycle. No reverse DAG
  dependency on the parent theorem is added for these generic helper declarations.
- F2 / H3,H4: `schemeFunctions` is literally
  `(CondensedRing.derivedHom R.X V).obj (op (ProfiniteFreeSlice.derivedFree R.X V P))`.
  Every gamma in the statements is `G.gamma.hom.app K` for the recorded
  `ProfiniteFreeSlice.Comparison`; its generator and chain-localization fields
  fix normalization. `functions` is the existing closed derived `ihom(A_P[0])`.
  Unary right derivation appears only in `unaryHomComparison`, an actual linking
  natural isomorphism obtained by uniqueness of right adjoints after the
  tensor comparison normalized on K-flat representatives.
- F3 / H3: `finite_free_matrix` now has `conjugatedAction` on its left. After beta
  and a checking coordinate, its right side is the sum over j of the jth input
  coordinate, substitution along a, and multiplication by the actual local
  regular-module endomorphism `localMatrix ... i j`. These endomorphisms are
  arbitrary sections of B on V. `finite_free_matrix_multiplication` states
  `matrix(v;w) = matrix(w) * matrix(v)` using actual `Matrix` multiplication.
  The action itself contains no checking basis and the formula quantifies over
  every pair of checking bases, expressing basis independence.
- F4 / H2,H8: `scalar_comparisons_isIso`, `restrictHomD`, and `restrictPushD` are
  gone. `scalarHomPoint` is the scalar transpose of a closed transpose of
  `(freeScalarMap⁻¹ tensor id);scalarTensor;E(ev);n-sharp`.
  `scalarPushMap` is the double scalar/geometric transpose of
  `scalarPullComparison⁻¹;E(counit);(p_U(n);action)-sharp`.
  The two structural isomorphism claims refer to these forward, independently
  specified maps, with full K-flat/free-generator proof docstrings. They assert
  neither a nor b invertible and impose no scalar flatness.

Hypotheses and clauses matched against the node:

- The explicit `universe u`, `Scheme.{u}`, `Profinite.{u}`, and internal abelian
  sheaves in `u+1` retain the recorded small sites and derived-category sizes.
  No site-object/morphism universe equality is added.
- `R : Profinite.CondensedRing.{u}` and `[IsCommMonObj R.X]` allow every
  commutative condensed ring. `Modules R X` abbreviates the recorded internal
  category, `pointPull` the recorded point inverse image, and `parameterD` the
  recorded free module in degree zero. All coefficient objects `N,K,K'` range
  over ordinary unbounded derived categories, with all derived arrows allowed.
- `comparisonApp` is c, defined as the projection-adjunction transpose of
  `derivedEvaluation` after the canonical `pointComposition`. `parameterGenerator`
  is an actual regular-module map from the universal section, obtained by the
  section-module equivalence and `unitHomEquiv`. `beta` is the existing canonical
  evaluation transpose `PointDerivedHom.comparison` followed by the normalized
  single-complex pullback identification. Neither definition uses gamma or c⁻¹.
- (1) `factorization_and_naturality` is c=beta;gamma with G's point-composition
  target identification, and naturality for every `v:N⟶N'`.
  `degree_zero` is H⁰(c) under `sourceZero` and `targetZero` equal to the ordinary
  exponential-law evaluation adjunct `evaluationApp`. Its source comparison is
  linked to the actual closed derived Hom by `unaryHomComparison`, not assumed
  definitionally equal to unary derivation. The generator is the pullback of
  `[id_P]` along the tautological graph and its restrictions, giving f([t]).
  `parameter_and_base_change` states the continuous-j square and pro-etale
  base-change square as derived morphisms. Base change is stated for all
  weakly-etale maps (the same pullback-mate construction applies to all maps).
  `pushParameterApp` and `pushSquareApp` are adjunction mates of actual counits
  and pullback-composition comparisons, so agree with the unit formulation by
  the triangle identities. Derived equalities survive every restriction functor
  and its composites.
- (2) `whole_family` allows every scheme V, hence V=X[Q], both arbitrary derived
  K,K', every v, and every relative scheme arrow a with its over-V equation ha.
  The free map uses G'.freeIso, the local free functor on the representable a,
  and G.freeIso⁻¹. Thus precomposition is on all generalized sections [t']↦[at'].
  `ProfiniteFunctions.familyParameterMap` is the existing actual map
  (q,p')↦(q,alpha(q,p')), and
  `restricted_whole_family` specializes the gamma square to this map and applies
  any further functor E, including successive slice restrictions. The formula
  therefore holds over the entire X[Q]. `conjugatedAction` is independently
  defined by beta;H(a,v);beta⁻¹; `conjugated_action` states its c square, with
  only the two stated beta-isomorphism instances. The finite-free clauses are
  the explicit coordinate and matrix multiplication identities described above.
- (3) S is another arbitrary commutative condensed ring, φ any monoid morphism
  of its underlying abelian sheaves, and n any map into exact derived scalar
  restriction. `extendPoint` is the existing K-flat total left derivation of
  `Mod.extendScalars`; its tensorator uses the scalar-unit normalized monoidal
  structure and preservation of flat modules. `freeGeneratorScalar` is literally
  the free-adjunction transpose of S's free unit; `freeScalarMap` is its derived
  scalar transpose, so [t] maps to [t]. `scalarHomMap` is a with the point/action
  identification; `scalarPushMap` is b with the geometric counit mate.
  `coefficient_square` states c;b=a;Res(c') and, only with both c-isomorphism
  instances, c⁻¹;a=b;Res(c'⁻¹). No flatness, exact scalar extension, nonempty
  parameter, completion, or finite-subextension coefficient replacement occurs.

Dependency declarations used:

- `ProfiniteFreeSliceDerivedHom`: `Comparison`, `freeParameter`, `pointGenerator`,
  `pointModulePullback`, `test`, `derivedFree`, `localFree`, `abelianAdjunction`,
  `pointDerivedComposition`. In particular the existing normalized `freeIso`
  and `gamma` are used directly.
- `Sheaf.Paper.ProfiniteConstantDerivedFunctions`:
  `ProfiniteFunctions.testSchemeFunctor_preservesFiniteLimits`,
  `ProfiniteFunctions.familyParameterMap`, `ProfiniteFunctions.familyParameterMap_over`
  supply the geometric helpers reused for return L.
- `PointPullbackDerivedHom`: `comparison`, `tensorComparison`,
  `restrictionComparison`, and point-pullback exact/monoidal instances.
- The public upstream `ModuleObject.Basic`, `.Derived.Hom`, and recorded
  `CondensedModuleDerivedPushpull` provide coefficient rings, internal modules,
  actual closed derived Hom, and the geometric derived adjunction.
- `DerivedCategory.FlatModel`: `singleFunctorObjUnitIso` and
  `QObjTensorSingleFunctorObjIso`; the latter normalizes `parameterTensor`.
- `DerivedExtendScalars`: exact `Mod.comap`, `Mod.extendScalars`,
  `derivedExtendMapDerivedCategoryAdjunction`; `ChangeOfCoefficients` supplies
  `coefficientMap`, `mapModComapIso`, and `derivedComapUpperStarIso`.
- `ScalarExtensionMonoidal`: `exists_extendScalarsMonoidal` with its displayed
  scalar-unit equation; `ScalarTensorCancellation`: `extendScalars_preservesFlat`;
  `LeftDerivedFunctor.MonoidalStructure`: `leftDerivedFunctorMonoidal`.
- `RightDerivedFunctor.PlusCompatibility`: canonical H⁰/R⁰ comparisons;
  the existing closed adjunction and uniqueness of right adjoints give the
  explicit unary-Hom link. `Matrix.Basic` supplies actual matrix multiplication.
- Existing Mathlib APIs provide ultralift Yoneda, module sections, biproducts,
  pullback lifts and comparison functors. No private copy of their objects is made.

Searches: msearch LeanFinder (canonical derived evaluation/free profinite scalar
maps) returned 8 ordinary free/profinite/adic hits; LeanSearch (canonical free
profinite evaluation and relative substitution on unbounded modules) returned 8
ordinary free/evaluation hits; Loogle `CategoryTheory.ihom,
CategoryTheory.Adjunction.homEquiv` returned 7 generic closed-adjunction hits.
Those generic adjunctions are used. msearch grep
`parameterTensor|scalarPullComparison|FreeParameterEvaluation` in CategoryTheory
returned 0 hits. Repository rg in WeilConjectures and Sheaf found the imported
free-slice and point-derived-Hom interfaces and the downstream parent. Repair L
additionally read the existing finite-limit theorem, whole-family map and
over-equation there, together with the two definitions of testScheme/projection;
these are exact geometric matches, with no coefficient binders, and are reused.
`blueprint_refs.py search` returned 0
matching blueprint nodes; grep of DAG new IDs returned none. The exact tool
queries/results are retained in each new node's mathlib_searches.

Edge cases read against the constructions: empty P (zero free module and empty
slice), singleton P (identity evaluation), empty X or Q, zero derived coefficient,
r=0 or s=0 (empty coordinate sum), t=0 and empty middle rank in matrix product,
identity relative a and identity coefficient φ,n, and nonflat Z→Z/2. No condition
excludes these cases. The only conditional inverses are precisely the structural
free-scalar/pullback isomorphisms and the expressly conditional beta/c inverses.

## New nodes

`def-sfb-free-parameter-evaluation-data` owns the actual generator, beta and c
construction on the recorded free/closed/pullback interfaces. Its only postponed
section-compatibility theorem supplies proof data for an explicitly constructed
section. The source is Stacks 08J7 evaluation and the node's generator calculation.

`def-sfb-free-parameter-relative-maps` owns representable relative substitution,
projection-adjunction parameter and base-change mates, and beta-conjugated
action, with the whole-family α specialization using the existing scheme map. The finite-limit fact, whole-family map and over-equation
are reused from ProfiniteFunctions rather than declared again. The new node
still owns only the remaining canonical relative free-module and adjunction
constructions; its lean.declarations lists only declarations this delivery adds.

`def-sfb-free-parameter-degree-zero-data` owns the normalized exact tensor
comparison and resulting right-adjoint identification needed to read H⁰(c).
The choice is from an existence-and-uniqueness statement fixing the map on every
K-flat representative, not from an unspecified isomorphism.

`def-sfb-free-parameter-scalar-maps` owns a and b with the displayed closed/scalar
and scalar/geometric adjunction formulas. Structural isomorphism claims name
exactly the independently constructed generator and pullback maps and give
complete natural-language K-flat proofs, without flat φ.

`def-sfb-free-parameter-matrix-coordinates` owns local matrices and checking
coordinate maps on actual finite-free point coefficients. It introduces no
second ring of sections: entries are End of the local regular module.

Each new node was searched against DAG, Mathlib and both source libraries as
recorded above, cites only existing upstream interfaces or earlier new nodes,
and is imported by the item. The module split keeps each compile under 60 seconds.

## Second reading by Q155

This is a separate self-reading; the dispatcher forbids additional agents and
assigns independent review to the maintainer. I reread the returned F1–F4 entry,
the node's three clauses and all six module signatures. The unrelated gamma,
additivity-only matrix clause and reverse scalar inverses
remain removed. For return L I compared the two sets of scheme/parameter
binders and unfolded their testScheme/projection abbreviations: both geometric
theorem types are identical. I removed their new declarations, and also removed
the redundant family-map definition. restricted_whole_family now passes the
existing map and existing over-equation to both schemeParameterMap and
pushParameterApp. Its K,K', v, G,G', E and category/universe binders and both
sides of the derived equality are retained. In particular the square remains
over all X[Q] and under arbitrary further restrictions. The relative-map node
still states its finite-limit and over-projection clauses using the imported
existing declarations. No mathematical statement correction was needed.
The retained earlier self-check covers c's definition without gamma, gamma's exact
Comparison type, unary-Hom's tensor-normalized link, the direction of every mate,
the beta-conjugated matrix coordinates and actual Matrix product, and all
conditional inverse hypotheses. The free-slice witnesses G,G' are normalized
models whose existence is the recorded dependency's theorem, not extra mathematical
hypotheses. The source and target are the same ordinary derived categories.

Validation before this repair: all six modules passed the saved packet dry run.
Validation of the repaired packet: scompile.py compiled all six delivered modules
individually under their sandbox and library names with no errors or warnings.
Library times: 40.2 s evaluation data, 19.3 s relative maps, 18.0 s degree-zero
data, 49.7 s scalar maps, 7.9 s matrix coordinates, 15.7 s coherence.
deliver2.py --no-push passed the repaired packet at 48cfaf59482 (preflight and
per-file compilation). The final self-check also confirmed all six recorded
signatures occur verbatim in their modules, no duplicate helper declarations
remain, every module disables autoImplicit, and every Lean line is at most
100 characters.
