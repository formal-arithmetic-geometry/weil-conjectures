## Worker report

The module `Sheaf.Paper.IntegralCoefficientModelRealization` states
`AlgebraicGeometry.Scheme.IntegralAmbientTower.integral_coefficient_model_realization`.
Its sole postponed proof is `by sorry`. Three helper definitions compose existing
isomorphisms or bundle actual quotient maps; they contain real data. The node is
unchanged except for its `lean` record. No dependency repair, new node, or statement
correction is needed.

The reference example `Sheaf/CategoryTheory/CompactObject.lean` is now withdrawn;
its node points to `WeilConjectures.CategoryTheory.CompactObject`, which was read
for the actual module/docstring/explicit-universe conventions.

Clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`, and the finite intermediate field is
  `(E : PadicAlgCl.FiniteIntermediateField l)`. The chosen uniformizer is `(π :
  PadicAlgCl.integers l E.1)` with `hπ : Ideal.span {π} =
  IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1)`. The valuation topology,
  coefficient rings, and actual reductions are the imported constructions.
- The site's universe is arbitrary `u`, with `T : Scheme.{u}`, site
  `ProEt.topology T`, and ring/module values in universe `u + 1`.
  `integers.{u} l E` is the recorded ULift of the valuation ring. No site-object
  and site-morphism universes have been equated.
- `C_T` and `Q_{T,n+1}` are `integralRing l E T` and
  `quotientRing l E π T n`, the actual section-ring reconstructions of the
  pulled-back continuous-function condensed ring objects. `quotientProjection`
  is the specified reduction, not an arbitrary ring homomorphism.
- The first five conjuncts state Noetherianity, finite generation of the exact
  principal ideal `Ideal.span {ULift.up π}`, additive torsion of its first
  quotient, finiteness of every positive quotient, and `adicQuotientPerfect`
  for every exponent at least one. The latter unfolds to the imported
  `DerivedCategory.IsPerfectRingComplex` of the actual quotient in degree zero.
  These are precisely the fields of the recorded adic datum.
- The sixth conjunct is `∀ n x, l ^ (n + 1) • x = 0`. Thus the paper's exponent
  `n ≥ 1` is expressed without dropping the first quotient; `n = 0` in this
  indexing means exponent one.
- `∀ T, Nonempty (CoefficientModel l E π hπ T)` asserts existence of the
  normalized ring identifications. The existing structure has fields `finite`,
  `completed`, `projection`, and `constants`. Its constants clause sends the
  class of `a` to the class of `ULift.up a` through the actual continuous chart.
  Consequently this is not mere existence of arbitrary ring isomorphisms.
- `CoefficientModel.constantFinite` composes `C.finite n` with the inverse of
  `pbcLevelConstantComparison`: the target is the actual constant sheaf of the
  lifted quotient. `CoefficientModel.constantCompleted` similarly composes
  `C.completed` with the inverse of `pbcCompletedComparison`: the target is
  `adicLisseCompletedRing`, the inverse limit of those constant quotient sheaves.
  The projection equation is stated for every model and every positive level
  using `limit.π (adicLisseRingSystem ...) (op n)` and the actual quotient map.
  This expresses exactly the cited normalized limit identification in constant
  coordinates, rather than declaring a new completion.
- `realizationQuotientSystem` is `Functor.ofOpSequence` on the actual quotient
  rings; its consecutive maps are reconstructed from `completedResidueTransition`
  by `AlgebraicGeometry.ProEtale.completedCoefficientMap`. The `∀ a b g`
  equation intertwines every arrow of this diagram with the constant quotient
  diagram, including identities and nonconsecutive transitions.
- `∀ {X Y} (f : X ⟶ Y) (CX ...) (CY ...)` imposes no geometric hypothesis.
  The next two equations are the integral and finite coefficient squares in
  adjunct form on every site object's sections. Their left sides use the
  actual `condensedPushforwardHom`, the mate of `condensedPullbackHom`.
  Their right sides use `proEtaleSheafAdjunction` on `datum.integralRingIso`
  and `datum.finiteRingIso`. These latter maps are exactly the canonical
  profinite/constant comparison transported to the adic presentation, as their
  definitions in `FourCorners.lean` show. Equality on all sections is equality
  of the ring-sheaf adjuncts and hence of the inverse-image squares.
- `Nonempty (AmbientEncoding l E f CX CY)` and `∀ n, Nonempty
  (FinitePushEncoding ... f n)` use the dependency's exact structures. Each
  contains an ordinary natural isomorphism, identity on underlying section
  groups (`ordinary_property`), and a derived natural isomorphism with
  `NormalizedSquare.normalization` on **every** unbounded complex. Thus the
  ordinary functors, scalar actions, localization factors, and universal units
  are retained. The finite encoding is the fixed-scalar direct image of the
  lifted quotient, with the already normalized scalar lift. No independent
  replacement action, cohomology-only comparison, or complete subcategory occurs.
- The resolution lemma's normalized limit, flatness, and K-flat resolution are
  cited input results, not new assumptions on schemes/modules. They are imported
  publicly and used in the seven-step proof plan. No completeness, boundedness,
  properness, constructibility, qcqs, or nonemptiness binder was added.

Dependency declarations read and used (direct public imports for statement
interfaces, plain imports for proof-only interfaces):

- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`.
- `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
- `def-weil-pbc-constant-sheaf`: `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `CategoryTheory.constantSheaf`.
- `sk-def-sfb-derived-categories`: `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
- `def-weil-pbc-adic-coefficient-datum`: `Sheaf.Paper.AdicCoefficientDatum`, `AlgebraicGeometry.Scheme.completedReductionTower`.
- `def-sfb-integral-ambient-coefficient-presentation`: `Sheaf.Paper.IntegralAmbientCoefficientPresentation`, `AlgebraicGeometry.Scheme.IntegralAmbientTower.CoefficientModel`.
- `def-sfb-integral-ambient-direct-image-encoding`: `Sheaf.Paper.IntegralAmbientDirectImageEncoding`, `AlgebraicGeometry.Scheme.IntegralAmbientTower.FinitePushEncoding`.
- `lem-sfb-integral-quotient-resolution-normalization`: `Sheaf.Paper.IntegralQuotientResolutionNormalization`, `AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_resolution_normalization`.
- `sk-def-sfb-coefficient-morphisms`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.condensedPullbackHom`.
- `lem-weil-pbc-profinite-coefficient-inverse-image`: `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image`.
- `def-pc-perfect-ring-complex`: `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`, `DerivedCategory.IsPerfectRingComplex`.
- `lem-sf-finite-discrete-normalized-encoding`: `Sheaf.Paper.FiniteDiscreteOrdinaryEncoding`, `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_exists`.
- `lem-weil-pbc-integral-coefficient-presentation-comparison`: `Sheaf.Paper.IntegralCoefficientPresentationComparison`, `WeilConjectures.IntegralCoefficientPresentation.comparison`.
- `lem-sfb-internal-module-operations-transport`: `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`, `AlgebraicGeometry.ProEtale.InternalModuleOperations.internal_module_operations_transport`.
- `lem-sfb-constant-scalar-restriction-tensor`: `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`, `CategoryTheory.ConstantScalarRestriction.derived_comparison`.
- `lem-derived-exact-equivalence-squares`: `Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`, `CategoryTheory.exactEquivalenceDerivedSquares`.
- `lem-weil-pbc-exact-functor-derived-functor`: `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`, `CategoryTheory.Functor.exactFunctor_derivedFunctor`.

For the coefficient datum the primary recorded declaration is the reduction-tower
constructor; the same module publicly exposes `AdicCoefficientDatum` and
`adicQuotientPerfect`. These exact definitions were read through its imports.
For direct-image encodings the primary declaration is `FinitePushEncoding`; its
module also supplies `AmbientEncoding` and `NormalizedSquare`, whose full fields
were read. `CoefficientModel` and its module/derived equivalences are reused.
The general right-derived convention is specialized by the prescribed
`CondensedRing.moduleObjectDerivedPushforward`, definitionally the total right
derived functor used by `NormalizedSquare`.

The natural-language proof docstring follows all seven accepted DAG proof steps:
arithmetic and perfectness; normalized finite constants and their lifted quotient
comparison; integral/finite inverse-image squares; exact section/scalar encodings;
the integral identity on sections; its finite analogue; universal total derived
comparison. The unused left half of the cited two-sided comparison theorem is
filled by zero functors in the proof plan, as in the reviewed DAG proof. The
qcqs projection formula in Bhatt--Scholze 6.5.9(3) is not applied to obtain the
ordinary encoding for arbitrary schemes. The source's Section 6.5 and the
specified extracted `IntegralAmbientTowerComparison` declarations were read,
as were Stacks 093J, 093M, and 0D6E in the local TeX sources.

Edge cases checked before finalizing:

- The first positive quotient is included; exponent zero is never used as a
  positive adic level. Perfectness separately quantifies every `n ≥ 1`.
- Ramification is allowed: the annihilator is `l^(n+1)`, using `l ∈ (π)`;
  no claim that the quotient is annihilated by `l` at every level was substituted.
- Empty schemes and empty site objects are admitted. No point or section was
  selected; constant normalization is local, and section comparisons quantify
  all sections (including singleton section rings on the empty object).
- Identity scheme maps, arbitrary scheme maps, identities of the tower index,
  and all composite quotient transitions are included.
- The zero module and unbounded/noncomplete complexes are included by the
  whole ambient categories and the every-complex normalization.
- All variables/universes are explicitly bound (`set_option autoImplicit false`).
  The universe lift is only the dependency's prescribed lift, not a restriction
  on schemes or a new coefficient field assumption.

Searches:

The sandbox's `searches.jsonl` records successful wrapper searches on 2026-10-22:
LeanFinder for normalized realization of integral condensed coefficients by
inverse limits of constant finite quotient sheaves and direct image (8 hits,
including `CondensedMod.ofSheafProfinite` and locally constant presheaf results,
not this statement); Loogle `SheafOfModules.pushforward,
CategoryTheory.Equivalence` (0 hits); Mathlib grep
`coefficientModel|AmbientEncoding|FinitePushEncoding` (0 hits); LeanSearch for
exact equivalences transporting total right derived functors with their universal
units (8 hits including `Functor.totalRightDerived` and
`Functor.isRightDerivedFunctor_iff_of_iso`, not the coefficient realization).
The three first searches were repeated in this resumed turn.

`rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id and
`integral_coefficient_model_realization`, `coefficientModel_exists`,
`AmbientEncoding`, and `FinitePushEncoding` found no single existing declaration
of this entire statement. `IntegralAmbientTowerComparison.coefficientModel_exists`
and `.encodings` are partial existing statements: they omit the arithmetic,
constant-coordinate projection/transition equations and coefficient-map squares.
Their types and docstrings were read; no duplicate of either partial theorem is
created. The helper declaration names were searched in both source roots; no
same fully qualified declaration exists. All existing notions are reused.

No STATEMENT-DISPUTED flag or node fault remains.

Compilation: the initial draft exposed a name-resolution clash for
`completedCoefficientMap`; qualifying it as
`AlgebraicGeometry.ProEtale.completedCoefficientMap` fixed the actual quotient
transition. `scompile.py Q152 lem-sfb-integral-coefficient-model-realization
<module>` then accepted both its sandbox and its library-name compilation.
After adding explicit direct imports of every statement-dependency module,
the final version again compiled cleanly (39.8 s sandbox, 27.4 s library).
No global build or direct compiler invocation was run.

## Second reading by Q152

This is a separate self-check pass with the node, final module, and encoding
structures open, not a claim of an independent second worker: the dispatched
brief forbids starting agents and assigns independent review to the maintainer.
The clause correspondence above was checked again against the final signature.
In particular the finite fields of `CoefficientModel` target continuous-function
adic sheaves, so the explicit compositions with the existing constant comparisons
are essential; those compositions and their projection orientations were checked.
The ordinary normalization is inside each encoding's `ordinary_property`, and
the universal-derived-unit equation is inside `normalization`; neither is omitted
by asserting `Nonempty` of the full structure. The two coefficient equations
use adjuncts of the canonical maps, not arbitrary ring isomorphisms. The full
index-arrow transition equation includes every transition. The compiler clash
was corrected and direct dependency imports were added; no mathematical
statement was changed. The read-only library and launcher scripts were not edited.
