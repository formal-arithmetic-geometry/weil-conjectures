## Worker report

The module `Sheaf.Paper.CountableNormProjectionCriterion` states
`AlgebraicGeometry.ProEtale.countableNormProjection_criterion`, with `sorry` as its
only postponed proof. It also constructs the coefficient inclusion, its existing
ring-homomorphism instance, the canonically normalized scalar/pullback comparison,
and the specified geometric-adjunction counit mate. All definition data are real
terms using existing constructions. No additional theorem is postponed.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
and the item's full agent-extracted proof. The newest blueprint paragraph cites the
proper and open direct-image finiteness inputs; the detailed countable endomorphism
argument is the auxiliary DAG's explicitly agent-written proof, not a claimed
published theorem. The module preserves that attribution and its wanted-reference
qualification. The exact node statement is unchanged.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite normed E/Q_ell: `[NormedField E] [Algebra (Padic ℓ) E]`
  `[FiniteDimensional (Padic ℓ) E]`, with `_hE` identifying the supplied norm with
  `Padic.coefficientExtensionAbsoluteValue ℓ E` pointwise. This permits any
  presentation of the specified extended norm, without assuming a second topology.
- Nonarchimedean normed field extension F/E with the same restricted norm:
  `[NormedField F] [NormedAlgebra E F]` and `_hF`, the ultrametric inequality.
  Mathlib `norm_algebraMap'` says exactly that the norm restricts to E's norm.
  Conversely, a norm-preserving inclusion of normed fields supplies the stated
  `NormedAlgebra`; this is no extra restriction. Nonarchimedeanness of E follows
  from `_hE` and its extended p-adic absolute value.
- Algebraic countable spanning: `_hcountable : ∃ s : ℕ → F,
  Submodule.span E (Set.range s) = ⊤`. Finite spanning families can be enumerated
  with repetitions and padded with zero; F is nonzero as a field. This is algebraic
  finite-sum span, without completion or an infinite-series assertion.
- A(P)=C(P,E), B(P)=C(P,F): `normContinuousRing E` and `normContinuousRing F` are
  the existing wrappers of `Profinite.continuousMapRingObjOfUniverse`. They use ALL
  continuous functions. `countableNormCoefficientHom` is exactly postcomposition
  by `algebraMap E F` using `continuous_algebraMap E F`; the instance is precisely
  `Profinite.isMonHom_continuousMapRingObjMapOfUniverse`.
- Pulled-back coefficient rings and internal modules: `Modules` is the existing
  alias for `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})
  (condensedRingObj (normContinuousRing E).X X)`, so the rings are the recorded
  `coefficientRing`, not constant sheaves or section-ring substitutes.
- Ordinary unbounded derived categories: `DerivedCategory (Modules ... X)`;
  `D (countableNormCoefficientHom E F) Z` is the existing total
  `leftDerivedFunctor` of `Mod.extendScalars (coefficientMap ... Z)`.
- Noetherian Y: `[CompactSpace Y] [IsLocallyNoetherian Y]`, exactly the node's two
  conditions. These also imply quasi-separatedness, so the existing constructibility
  predicate takes its finite-stratification branch on Y.
- X and f unrestricted: `{X Y : Scheme.{u}} (f : X ⟶ Y)` has no properness,
  quasi-compactness, finite-type, separatedness, or base-field binder on X or f.
- K arbitrary: `(K : DerivedCategory (Modules (normContinuousRing E).X X))`, with
  no boundedness, constructibility or Tor-amplitude hypothesis on K.
- M=Rf_{*,A}K: `(QuotientChange.F (normContinuousRing E).X f).obj K` uses exactly
  the recorded `CondensedRing.moduleObjectDerivedPushforward`.
- N=Rf_{*,B}T_XK: `(QuotientChange.F (normContinuousRing F).X f).obj
  ((D (countableNormCoefficientHom E F) X).obj K)`.
- Constant-model constructibility: `IsConstantModelConstructible` is the landed
  predicate using finite constructible locally closed strata and
  `HasFiniteConstantLocalModel`. The recorded `finiteConstantLocalModel_iff_exists_cover`
  identifies the latter with the explicit scalar-extension model. For a field,
  finitely presented abstract scalar modules are finite-dimensional vector spaces.
  No arbitrary local presentation matrix predicate is substituted.
- M bounded constant-model constructible: `_hM : constantModelBoundedConstructible
  (normContinuousRing E).X Y ...`.
- T_YM bounded constant-model constructible: `_hTM` applies the same predicate to
  `(D (countableNormCoefficientHom E F) Y).obj M`.
- Every H^q(N) constructible without a common bound: `_hN : ∀ q : ℤ,
  IsConstantModelConstructible ... ((DerivedCategory.homologyFunctor _ q).obj N)`.
- Specified beta: `countableNormProjection E F f K` is defined by the actual
  `(adj (normContinuousRing F).X f).homEquiv`, applied to the component of the
  normalized `countableNormScalarPull` at M, followed by `D_X.map` of the actual
  E-geometric counit at K. Its domain is exactly T_YM and its codomain exactly N.
- Canonical balanced comparison: `countableNormScalarPull` retains the b component
  of `internal_scalar_pullback_normalization`. That theorem's `PullNormalized`
  computation-counit equation fixes b on K-flat resolutions by the ordinary
  `CondensedRing.pullIso` and hence on the whole derived category. Thus its statement
  determines the chosen b up to equality, although the irrelevant tensor and section
  witnesses need not be unique. This is not a choice from a bare Nonempty isomorphism.
  The theorem supplies exactly the inverse of the normalized scalar-adjunction mate
  specified by the original K-flat comparison node. No coefficient flatness is needed.
- Conclusion that N is bounded constant-model constructible: the first conjunct.
- Conclusion that this specified beta is invertible: the second conjunct
  `IsIso (countableNormProjection E F f K)`.
- The degreewise stronger conclusion: the final `∀ q : ℤ, IsZero (H^q M) →
  IsZero (H^q N)`. `IsZero` is applied to actual objects of an abelian category,
  never to a bare type.
- Universes: all carrier sizes are allowed by `universe u`, with the framework's
  site object universe u+1, morphism universe u, and section universe u+1 retained.
  No site object/morphism universe equality has been imposed. The section-derived
  localization instances required only inside the comparison construction are
  supplied via the existing section-module equivalence and
  `HasDerivedCategory.ofIsGrothendieckAbelian`; they add no theorem hypotheses.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` imports
  `Sheaf.NumberTheory.Padics.CoefficientExtension`, supplying
  `Padic.coefficientExtensionAbsoluteValue`; the node's positive-level finiteness
  theorem is not needed for this statement.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse` and its recorded monoid structure.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjMapOfUniverse` and
  `Profinite.isMonHom_continuousMapRingObjMapOfUniverse`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, `upperStarFromPoint` and their canonical
  commutative ring-object instances.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its morphisms.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded derived-category convention interface, with Mathlib `DerivedCategory`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  generic `leftDerivedFunctor`, K-flat preservation and
  `Mod.derivedExtendMapDerivedCategoryAdjunction` without flatness.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`,
  and the imported canonical geometric adjunction.
- `Sheaf.Paper.KFlatScalarComparisonNormalization` (public statement dependency):
  `SheafOfModules.ScalarPullback.kflat_scalar_comparison_normalization`, the recorded
  representative and unit normalization, transported by the internal interface.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  the recorded finite locally closed stratification;
  `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `finiteConstantLocalModel_iff_exists_cover` and its scalar-extension formulation.

Five already landed interface owners are added to `stmt_deps`, as allowed by brief
§5: `def-sfb-norm-continuous-monodromy-data` (`normContinuousRing`),
`def-sfb-internal-derived-scalar-comparisons` (`Modules`, `D`, `L`, `F`, `adj`),
`lem-sfb-internal-scalar-pullback-normalization` (the normalized b component),
`sk-def-sfb-constructible` (constant-model constructibility and boundedness), and
`def-pd-section-module-operations-data` (the section-module equivalence used to supply
canonical auxiliary localization instances). Their declarations and docstrings were
read. A read-only traversal found no dependency path from these owners to this item.
There are no new DAG nodes or dependency repairs and no statement correction.

The stated proof dependencies are imported without `public`:
`Sheaf.Analysis.NormedSpace.CountableUltrametricBasis`,
`Sheaf.LinearAlgebra.CountableEndomorphismModuleReconstruction`, and
`Sheaf.Paper.ConstructibleNormedGeometricFibres`.
`lem-sfb-norm-coefficient-endomorphism-corner` has no Lean record in the read DAG,
so there is no module to import yet; its exact role is retained in proof step 2.
It is a proof prerequisite, not an object needed to state this theorem.

Edge cases checked before stating: E=F and finite-dimensional F/E satisfy countability;
F need not be complete; K=0, X empty, Y empty and empty stratifications are included;
all degrees q including negative degrees are quantified; N can initially be unbounded;
M=0 forces every cohomology object of N to vanish by the stated last conjunct; nonproper
f and X not of finite type are not excluded. Rank-zero finite constant models are allowed.
No counterexample or statement dispute was found in these checks.

Searches performed with the prescribed `msearch.py`, group Q82 and this item:

- LeanFinder: `Derived scalar extension direct image projection isomorphism for countable
  dimensional normed fields and bounded constant model constructible cohomology`.
  Eight hits: algebraic cotangent cohomology, group-cohomology/Ext comparisons,
  ModuleCat scalar adjunctions and Nobeling exactness; none states the criterion.
- Loogle: `Condensed, "tensor"`. Zero hits.
- Mathlib grep: `(scalar|coefficient).*(projection|directImage)`, subdirectory
  `CategoryTheory`. Zero hits.
- LeanSearch: `The canonical derived scalar extension direct image comparison is an
  isomorphism for constructible cohomology and a countable dimensional normed coefficient
  field extension`. Eight hits about scalar restriction, normed scalar structures and
  elementary scalar coercions; none states the criterion.
- `rg` in both read-only `lean/WeilConjectures` and `lean/Sheaf` for
  `countable.*[Pp]rojection|[Pp]rojection.*countable|countableNormProjection`: no matching
  criterion; the few hits concern unrelated countable coproduct projections.
- Exact item-id search in `lean/WeilConjectures`: no hits.
- Broader scalar/projection searches found the existing specialized all-continuous mate
  for PadicAlgCl, the supported-lattice theorem and the generic internal comparison
  interfaces. The first two impose specialized coefficient/input/geometric assumptions
  and do not state this criterion. The generic internal interface is reused instead of
  introducing a new derived scalar-extension construction.

Validation is through `scompile.py` and the prescribed delivery dry run only.

The final `scompile.py` check passed in both sandbox mode and final library module
mode, with no errors or warnings. The node signature matches the file verbatim;
all Lean lines fit within 100 columns, auto-implicits are disabled, and the only
`sorry` is the assigned theorem's proof. The auxiliary localization-instance omission
and a line-break parsing issue in the nested existential projection were repaired
before this clean check.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
