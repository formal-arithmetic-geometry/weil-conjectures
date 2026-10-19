## Worker report

This delivery states `lem-weil-constant-weil-structure-stage-independence` in
`Sheaf.Paper.ConstantWeilStructureStageIndependence`. Clause 1 is
`WeilConjectures.constantWeilRationalScalar_equivariant`; clause 2 is
`WeilConjectures.constantWeilStructure_stageIndependent`. No statement, statement
 dependency, proof, or proof dependency of the item is changed. No theorem is proved.

The source read is the coefficient-object paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md`,
order 1869, together with this auxiliary node's eight-step proof. The paragraph defines
the coefficient objects by integral completion and scalar extension and equips the rational
and algebraically closed ones with the canonical Weil structure. The supplied dependency
module makes the normalization of that scalar extension available, rather than selecting
one of the previous bare `Nonempty` isomorphisms.

Hypotheses and objects, clause by clause:

- The fixed finite-field datum `p,a,q,k₀,k` is `D : FiniteFieldDatum.{u}`; its fields include
  primality, the positive exponent, cardinality and an arbitrary fixed algebraic closure.
- The prime `l` is bound by `(l : ℕ) [Fact l.Prime]`; distinctness is `(hl : l ≠ D.p)`.
  Invertibility on the geometric fibre is derived by `sfWeilPrimeInvertible`, not assumed.
- A finite-type `k₀`-scheme is `Y₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`. No separatedness is imposed.
  Its actual geometric fibre is `(D.geometricFiber Y₀).left`; its geometric Frobenius is
  `(D.geometricFrobenius Y₀).hom`, a scheme isomorphism, without a k-linearity assumption.
- The fixed closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`, with independent closure universe `v`.
- Clause 1 quantifies over `(A B : AlgebraicallyClosedCoefficients.Index l Ω)` and
  `(h : A ≤ B)`, exactly the finite extensions inside the fixed closure and their
  inclusions. The underlying fields are the recorded small models
  `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω A/B`, and their map is the
  recorded `coefficientInclusion l Ω A B h`. The map definitions and heart-carrier
  helpers take the equivalent intrinsic field/algebra interface; the actual equivariance
  theorem is stated on precisely these stages, without an extra universal conclusion.
- `E_Y,theta_E` are exactly `constantWeilRationalObject` and `constantWeilRationalTheta`.
  Their fixed pair and heart restriction are the recorded `constantWeilRationalComplex`
  and `constantWeilRationalSheaf`.
- The specified integral beta is `constantCoefficientIntegralScalarIso`, using the regular
  complex itself and the *recorded* `integralScalarExtensionComparisonOfUniverses`.
  Its inverse is the localized `constantCoefficientScalarUnit`, preceded by the inverse
  representative comparison. The chain unit is determined uniquely by its image of 1
  at every quotient and by its zero shifted component in every degree. Since it is an
  S-linear map from the regular S module, the displayed image of 1 fixes its value on
  every local section s: S acts on the m-th target by `pi^L_m`, so it sends s to
  `pi^L_m(s) tensor 1`, identified by multiplication with `pi^L_m(s)`. There is no
  identification of uniformizers, no arbitrary cone filler, and no K-flat replacement
  of this regular representative.
- `constantCoefficientRationalScalarIso` is alpha: its unique specification says its hom
  is the image of beta in `sfRationalConstructibleLocalization`. `HEq` expresses only the
  endpoints' identification by the recorded rational scalar object's formula; it does
  not leave the arrow or its normalization unspecified.
- `constantWeilScalarPullbackComparison` specializes the recorded
  `rationalPullbackScalarComparison` to geometric Frobenius. Its inverse followed by
  scalar extension of theta_E is the structure of `constantWeilScalarComplex`.
- Clause 1's displayed equality is literally `pullback.map alpha.hom ≫ theta_L.hom =
  scalarPair.str.hom ≫ alpha.hom`, i.e. theta_L after pullback(alpha) equals alpha after
  extended theta_E with the stated pullback/scalar identification. The second conjunct
  gives an isomorphism `constantWeilScalarSheaf ≅ constantWeilRationalSheaf`, and requires
  its forgotten hom to be alpha.hom. `constantWeilScalar_mem_heart` supplies the full
  constructible-heart restriction using the same alpha and heart closure under isomorphism.
- Clause 2 quantifies over `A : AlgebraicallyClosedCoefficients.Index l Ω`, the finite
  intermediate fields inside Ω. `constantWeilStageSheaf` is precisely `(A,(A_Y,theta_A))`
  with its recorded finite-stage fixed-pair construction; its membership proof is
  `constantWeilStage_mem_heart`, using that very stage in the two standard classes.
- The target is the recorded `constantWeilAlgebraicallyClosedSheaf`, defined at
  `Padic.finiteCoefficientBase l Ω`, the small model of Q_l. The isomorphism is in the
  common-stage *Weil-sheaf* category, not a derived category of Weil sheaves.
- Compatibility with `For` is the explicit equation on the inverse isomorphism:
  `(sfCommonStageWeilForget ...).map φ.inv.hom = constantWeilStageComparison ... A`.
  The right side is an actual `GeneralAlgebraicallyClosedCoefficients.ofHom` class at A,
  represented by alpha_{Q_l,A}, with exactly the stage associator and the target
  self-transition. `constantWeilStageScalarIso` uses the stage-system's specified
  transition equality to identify its source; it introduces no new comparison choice.
  Faithfulness of For makes this specified isomorphism canonical.

Dependency declarations used, with their recorded modules read:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber` and coefficient
  conventions (`Padic`, the valuation rings, uniformizers and finite quotients).
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `def-weil-scheme-morphism-properties` is a convention record; finite type is the
  recorded Mathlib `LocallyOfFiniteType` plus `QuasiCompact`.
- `Sheaf.Paper.ConstantWeilStructure`: the regular complex and its good representative,
  its unit section, integral/rational objects and theta maps, rational and algebraically
  closed fixed pairs and their constructible Weil-sheaf restrictions.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible` (retained publicly through
  ConstantWeilStructure): `integralConstantCoefficientObject` and its constructibility;
  the wrapper adds the normalized comparisons, described below.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleLocalization`,
  `sfRationalScalarExtension` and its unique integral-object normalization.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalPullbackScalarComparison`, with its
  integral normalization. `sfWeilFrobeniusPullback` is its exact recorded specialization.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilForget`, `sfWeilSheaf`,
  `sfWeilStageObject`, and common-stage counterparts. `IsoAlgebra.mk` and `.str` are the
  existing fixed-pair constructor and structure isomorphism, not another definition.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `stageSystem`, `stageTransition`,
  `stageSystem_existsUnique`, `ofHom`, and the recorded small coefficient models.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`: `integralScalarExtensionOfUniverses`
  and `integralScalarExtensionComparisonOfUniverses`; its publicly retained
  IntegralScalarExtensionWellDefined gives `integralScalarTowerFunctor`,
  `integralScalarComplexFunctor`, and `integralScalarTensorSection`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: retains the actual completed
  coefficient rings and their quotient projections. The integral scalar tower acts
  through those actual projections, on the small pro-etale site.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`: `completedScalarRoosEndomorphism`
  names exactly the transition endomorphism of the recorded strict scalar tower.
  It is publicly imported by the dependency wrapper because its public normalization
  statement uses that declaration.

All recorded proof-dependency modules are imported (privately when needed only by the
proof plan). Each postponed theorem has a source, blueprint tag, and step-by-step proof
in its docstring. The main proof includes the coefficient-action square, finite regular
unit computation, strict-cone completion, rationalization, and common-stage class
calculation of the node. No new node is needed: the added helpers implement exactly the
canonical maps already required by these two nodes.

Edge cases checked before writing and reread after elaboration:

- Empty Y₀: no nonempty-site, connectedness, nonzero-stalk, or nonempty-space assumption
  occurs. The regular module and its unit/zero formulas still make sense.
- E=L with identity inclusion: every construction accepts `AlgHom.id`; the actual
  self-transition is retained in the common-stage representative instead of assumed to
  be an identity functor.
- A=Q_l: `bot_le` supplies the base inclusion, and the same self-transition normalization
  handles the least-stage object. No strict inequality is required.
- Ramified E⊆L: only the actual quotient-inclusion maps are used in the scalar tower;
  source and target uniformizers are not equated.
- Index zero means exponent one, exactly as in the recorded coefficient modules;
  no exponent-zero quotient is introduced. All integers occur in the shifted-component
  condition, and degree zero uses the actual regular single-complex generator.
- Geometric Frobenius is used as a scheme isomorphism, not as a k-morphism. No extra
  geometric assumptions (proper, separated, smooth) have been introduced.
- Ω has independent universe v; its finite coefficient models are the recorded small
  ones. The pro-etale site's object/morphism sizes are unchanged.

Searches for an existing statement and normalization:

- `msearch.py ... leanfinder "The canonical Weil structure on a constant coefficient
  sheaf is compatible with extension of scalars"`: eight hits, including
  `CompHausLike.LocallyConstantModule.functor`, `ModuleCat.Tilde.res_const`,
  `ModuleCat.tilde`, `CondensedMod.LocallyConstant.functor` and `SheafOfModules.unit`.
  These do not give a Weil fixed-pair or completed coefficient comparison.
- `msearch.py ... loogle "CategoryTheory.Endofunctor.IsoAlgebra,
  CategoryTheory.constantSheaf"`: zero hits, with unknown Mathlib identifier IsoAlgebra;
  that fixed-pair notion is supplied by the recorded upstream project module instead.
- `msearch.py ... grep "WeilSheaf|WeilComplex|constant.*Frobenius|Frobenius.*constant"`:
  zero Mathlib hits.
- `msearch.py ... leansearch "The canonical Weil structure on the constant coefficient
  object commutes with extension of scalars"`: eight algebraic scalar-extension hits,
  including `AlgHom.extendScalars`, `ModuleCat.extendScalarsId` and intermediate-field
  coercion statements; no completed coefficient or Frobenius compatibility statement.
- `rg` in upstream WeilConjectures and project lean/Sheaf for `stageIndependent`,
  `stage_independent`, constantWeil scalar/stage names and the exact item id found the
  existing constant Weil definitions and the earlier non-Weil coefficient pair result,
  with no theorem asserting this node's equivariance. Exact new declaration names were
  also searched in upstream, Mathlib and project sources, with zero existing matches.

No statement correction or disputed statement is needed. Initial compilation diagnosed
one private import in the normalization signature; it was made public. The compile and dry-run outcomes are recorded below.

## Dependency modules

`lem-weil-constant-coefficient-objects-constructible` receives the wrapper module
`Sheaf.Paper.ConstantCoefficientScalarNormalization` under §1(B), with only its `lean`
record changed. Its previous `integralConstantCoefficient_scalarExtension` and
`rationalConstantCoefficient_scalarExtension` provide only `Nonempty` isomorphisms and
therefore cannot name the particular beta/alpha in the present node; the older rational
statement also uses the prior rational category instead of the currently recorded
intrinsic sfRational category. The wrapper retains the original module's Parts 1-3 by
public imports, and supplies a chain-unit map determined uniquely by its finite
coordinates and zero shifted component, its quasi-isomorphism statement, the integral
beta, its lift to the full intrinsic integral category, and its uniquely specified
rational image alpha. The data are chosen only from uniqueness specifications; no mere
existence witness is used to pick an unspecified isomorphism. The regular complex and
its good representative are reused from ConstantWeilStructure, whose constructions
use the original constructibility theorem; the wrapper adds no import cycle.

Validation before the final finite-stage binder alignment: the two-file `scompile.py` invocation passed cleanly. The dependency
module compiled in 13.8 seconds and the item module in 6.1 seconds under the unchanged
60-second per-file limit; sandbox copies also passed (3.9 and 6.3 seconds). There were no
compiler warnings. A structural comparison confirmed that each delivered node copy
changes only `lean`; both modules have no line exceeding 100 characters. All newly
introduced names were checked for collisions before writing. There are no new DAG nodes
or mathematical statement changes.

The first delivery dry run passed (`bb4e02b386`). A final scope rereading aligned
clause 1's quantifiers with the node literally: finite indices A,B inside the fixed Ω
and h:A≤B, replacing the more general field/algebra embedding presentation of that
theorem. All map definitions and both mathematical clauses are unchanged. The final
dry run is rerun on this alignment before pushing.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
