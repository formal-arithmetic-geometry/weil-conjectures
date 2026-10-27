## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteTypeModuleSupportPullback`
states `AlgebraicGeometry.AlgebraicSpace.finiteType_moduleSupport_pullback`, with its
whole proof `sorry`. It introduces no definitions or auxiliary theorem obligations.
The source read is Stacks `literature/stacks-project/spaces-morphisms.tex`,
Tag 07TZ, `lemma-support-finite-type`, lines 2835–2890, specifically (1) and (3).
The statement is unchanged. Its six proof steps are reproduced in the theorem docstring.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`, using Mathlib's scheme and morphism category.
- The algebraic space over this base is `{X : AlgebraicSpace S}`. This is the recorded
  full subcategory of fppf sheaves with representable diagonal and a surjective etale atlas.
- The small-etale structure-sheaf module is `(M : X.Modules)`, using the recorded
  regular-functions structure sheaf, with section and ring carriers in universe `u`.
- Quasi-coherence is `[M.IsQuasicoherent]`, exactly Mathlib's local arbitrary-free
  presentation predicate used by the recorded `X.QCoh`. Taking an ambient module with
  this instance is equivalent to taking an object of that full subcategory.
- Finite type is `[M.IsFiniteType]`, Mathlib's local finite-generating-sections predicate,
  read in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Generators.lean` lines 109–145.
  Its slice sheafification instances are the recorded algebraic-space ones.
- The support is the existing `moduleSupport M`, the nonzero-geometric-germ locus.
  The chart-support dependency identifies it with the ordinary stalk support after
  restriction to any etale chart, independently of the representative.
- Closedness in the atlas topology is `IsClosed (moduleSupport M)`, with the existing
  `pointTopologicalSpace` on `Point X.obj.obj`; no atlas is selected in the statement.
- Every space morphism is `∀ (Y : AlgebraicSpace S) (g : Y ⟶ X)`.
- The specified tensor pullback is `(moduleTensorPullback g).obj M`, the left adjoint
  of the chart-limit module direct image, with its existing unit normalization.
- Its finite type and quasi-coherence are the first and second conjuncts under this
  universal quantifier, respectively `.IsFiniteType` and `.IsQuasicoherent`.
- Its support equality is `moduleSupport ((moduleTensorPullback g).obj M) =
  mapPoint g.hom.hom ⁻¹' moduleSupport M`. The point map applies the natural
  transformation to field-valued representatives and descends by `Quot.map`.
- There is no flatness, separation, finite-presentation or Noetherian hypothesis.
  The only universe is explicit `u`, the same universe as in the recorded sites and
  structure rings; point classes live in `Type (u+1)`. No auto-bound implicits are used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules` (publicly available through imports).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and the two
  small-etale slice sheafification instances, using `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport`:
  `AlgebraicSpace.etale_chart_moduleSupport`; its public support dependency supplies
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`, `AlgebraicSpace.moduleSupport`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace` (available through the support import).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicSpace.moduleTensorPullback` and its specified chart direct-image adjunction.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `AlgebraicSpace.mapPoint` only.
  Added its already-landed owning node `def-sfb-proper-curve-moduli` to `stmt_deps`,
  as authorized by the standing brief's rule STMT_DEPS MAY GAIN LANDED NODES.
  No curve-family hypothesis or moduli construction appears in this statement.
- `def-weil-size-convention` is a metatheoretic convention and has no module.

The module also imports the stated proof dependencies with plain imports:
`SchemeZariskiEtaleQuasiCoherentEquivalence.scheme_zariski_etale_quasiCoherent_equivalence`
(in namespace `AlgebraicGeometry.Scheme.Modules`),
`WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
(`AlgebraicGeometry.Scheme.Modules.finiteType_module_support_pullback`),
`AlgebraicSpaceFibreProductsEtaleCovers` (`fibreProduct_isAlgebraicSpace`,
`etaleCover_pullback`, `etale_fibreProduct_isScheme`),
`AlgebraicSpaceRepresentableEtaleSchemeTests` (`representable_etale_scheme_tests`),
`SpaceChartTensorRealization` (`space_chart_adjunction_tensor_realization`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`). The Sheaf module names
in this paragraph have prefix `Sheaf.AlgebraicGeometry`; space declarations have
namespace `AlgebraicGeometry.AlgebraicSpace`.
The proof dependency `lem-sfb-scheme-etale-module-exact-finiteness-comparison` has no
Lean record or Mathlib match in the read DAG, so there is no module to import yet.
It supplies no object needed to type this statement and is not re-created here.

Edge cases checked before writing: the zero module gives empty support; empty source
or target spaces impose no nonemptiness binder; identity morphisms retain the existing
adjoint-defined pullback. For the nonflat map `Spec F_2 → Spec Z`, the finite module
`Z/2` pulls back to `F_2` and support is precisely the inverse image of `(2)`.
For `D(t) → Spec k[t]` and the module `k[t]/(t)`, pullback has empty support.
No finiteness on the base ring is used. The non-finitely-generated module
`⊕_p Z/p` has nonclosed support in `Spec Z`, illustrating why finite type matters.

Searches actually run with the prescribed msearch.py wrapper:

- LeanFinder, “The support of a finite type quasi coherent module on an algebraic
  space is closed and arbitrary pullback has inverse image support”: eight hits,
  including `Module.isClosed_support` and scheme ideal-sheaf support theorems;
  none is this algebraic-space theorem.
- LeanSearch, “Support of finite type quasi coherent sheaf on an algebraic space is
  closed and commutes with pullback”: eight hits of the same ring-module or
  scheme-ideal type; no match.
- Loogle, `SheafOfModules.IsFiniteType`: four hits, including exactly the local
  finite-generating-sections predicate reused here. The initial combined query
  `SheafOfModules.IsFiniteType, SheafOfModules.IsQuasicoherent` was also run.
- Mathlib grep, `support.*pullback|pullback.*support|isClosed_support` in
  `AlgebraicGeometry`: three hits in scheme ideal-sheaf files, no match.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` with that support/pullback
  expression, then narrowed to algebraic-space module files: the scheme finite-type
  theorem and the existing space support/chart definitions, no duplicate theorem.
- Direct node-id search in `lean/WeilConjectures`, and the new declaration name in
  both roots: no match. Existing `mapPoint` found in `ProperCurveModuli.lean` and used.

No new nodes, dependency-module repairs, statement corrections or disputed statements.
Validation: the prescribed scompile.py compiled the sandbox and library module cleanly
(1.8 seconds each); the only postponed proof in this delivery is the assigned theorem.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
