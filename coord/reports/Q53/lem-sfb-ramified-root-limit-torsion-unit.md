## Worker report

Stage 2, Q53, 2026-10-22. This delivery states the complete node in
`Sheaf.Paper.RamifiedRootLimitTorsionUnit`, using the transparent predicate
`AlgebraicGeometry.Etale.RamifiedRoot.RootLimitAssertion`. Its only postponed
proof is `ramifiedRootLimitTorsionUnit`. No mathematical statement is corrected.
The live item has a passed stage-1 split; this assignment is its stage-2 statement,
so the previous worker's stale-stage-1-dispatch observation does not close this task.

The main theorem has explicit `p`, `ℓ`, proofs `hp`, `hℓ`, `hne`, a tower `T`,
and `s`, `hs`. `Coeff ℓ s` is the actual ring `ULift (ZMod (ℓ ^ s))`, with its
inherited ring operations; the lift only places coefficients in the site's
required universe. The coefficient-annihilation proof uses Mathlib's existing `ZMod.natCast_self`
transported by `congrArg ULift.up` directly, without a new theorem.
No model of a different finite ring, arbitrary coefficient datum, completion,
or adic category is substituted.

Clause-by-clause reading:

- Distinct primes: `hp : p.Prime`, `hℓ : ℓ.Prime`, `hne : p ≠ ℓ`.
- Positive integers prime to p, ordered by divisibility: `RamifiedRootIndex p`
  has `val`, `positive`, `coprime`; its preorder is exactly divisibility.
  Its opposite category indexes `T.diagram`, with no discreteness or total-order
  assumption. `one p` is the actual integer 1.
- Regular Noetherian affine stages: fields `regular`, `noetherian`, `affine`
  of `RamifiedRootTower`. `regular` uses the dependency's `IsRegularScheme`.
- Affine transition maps: field `transition_affine` on every arrow.
- Invertibility of ell: field `ell_unit` on every stage's global section ring.
- Actual nonzerodivisor parameters: fields `parameter`, `nonzerodivisor`.
  The latter is membership in Mathlib's `nonZeroDivisors`.
- Actual regular zero-locus schemes: `divisor_regular` on
  `zeroLocusSubscheme {parameter n}`. `divisor` and `closed` abbreviate this
  scheme and its actual closed immersion, preserving its scheme structure.
- Parameter power transitions: field `ramification`, with exponent
  `m.val / n.val` for an arrow `n ⟶ m` in the divisibility category.
- Effective Cartier property: the conclusion supplies `hI n`, precisely
  `(T.closed n).ker.IsInvertible`, using the recorded Cartier notion.
- X as inverse limit, with its projections: `cone`, `isLimit` in the tower,
  and `T.cone.π.app (op n)`. The chosen cone is a limit, not a replacement
  arbitrary scheme equipped only with maps to the stages.
- Stage punctures: `puncture` and `open` are the actual principal basic open
  and its canonical inclusion.
- W = X[1/f_1] = lim W_n: `limitParameter` is the pullback of the stage-one
  parameter, and `limitOpen`/`limitInclusion` are its actual principal open.
  The conclusion supplies `O : OpenSystem T` and `Nonempty (IsLimit O.cone)`.
  `O.diagram` has these actual stage punctures as objects. Every arrow and leg
  is fixed by its inclusion square; monicity proves the functor and cone laws.
  The conclusion also asserts the actual open squares are Cartesian, at stages
  and at the limit.
- s ≥ 1: `hs : 1 ≤ s`, retained even though the zero-coefficient edge s=0
  would admit a vacuous extension of the assertion.
- Constant sheaves: `ordinaryFiniteConstant`, `ordinaryFiniteUnit` reuse the
  recorded constant-sheaf construction and its degree-zero single functor.
- Ordinary etale derived modules: every object is in `DerivedCategoryModule A X`,
  i.e. the existing derived category of small-etale `ModuleCat A` sheaves.
- K = fib(actual unit): `support A j` is the existing total right derived
  functor of `sectionsWithSupport`, the kernel of the actual sheaf adjunction
  unit, evaluated at the constant object. `inclusion` derives its kernel
  inclusion. `unit` is the published exact-derived adjunction unit itself.
  The conclusion `IsFibreTriangle` asserts the distinguished triangle with
  exactly those first two maps and its connecting map. This is the canonical
  supported-kernel model of Cone(unit)[-1], not a free fibre object. The same
  construction is used at every finite stage and at the limit.
- The negative Tate line: `finiteEtaleTateSheaf ... (-1)` is the dependency's
  actual internal sheaf dual of the finite roots-of-unity coefficient line.
- Derived purity: `P n : closedDual ... ≅ (support ...)[2]` is the shifted
  version of `i_* A_D(-1)[-2] ≅ K`. Both are actual derived isomorphisms;
  this has not been replaced by a per-cohomology isomorphism.
- Supported Kummer normalization: `KummerNormalized` supplies an `Ext` class
  satisfying the existing `SupportedKummerBoundary` predicate. Its equality
  identifies that exact supported class with the tensor evaluation of the
  forget-support map of `P n`. Tensoring with the finite Tate line is exact
  by its actual tensor inverse, so the Ext equality is precisely the derived
  normalization. `closedEvaluation` is the ordinary adjunction transpose of
  normalized line pullback, the closed counit, and internal evaluation.
- Canonical transition on K: `θ a` is required to satisfy `SupportExchange`,
  the forget-support square with `constantPullback`. The assertion includes
  uniqueness with that property. It also includes the signed boundary square
  for the entire unit triangle, whose third component is `openExchange`.
  The latter uses `exactDerivedBaseChangeMap`, the actual adjunction mate of
  the descended inverse-image commutative square. The projection legs `β n`
  have the identical normalization and signed boundary compatibility.
- Multiplicity and reduction: `TransitionFormula` explicitly retains
  E = V(f_m^(m/n)) and its immersion k, with maps r:D_m→E and d:E→D_n
  fixed by their actual inclusion equations. The formula for the derived θ
  is the scalar `(m.val / n.val) • closedExchange` followed by P_m. The
  reduced closed square uses r followed by d; it is only commutative, and is
  never asserted Cartesian or identified with the nonreduced divisor.
  Its sheaf mate is exactly closed exchange followed by reduction.
- H^q K_n = 0 for q ≠ 2: the corresponding `IsZero` conclusion is quantified
  over every n and every integer q.
- Transition n→n ell^s is zero on H^2: the conclusion covers every arrow
  with `m.val = n.val * N`. Such m exists in the index because ell≠p.
  Cohomology is transported by `mapDerivedCategoryHomologyFunctorIso`;
  `cohomologyExchange` then applies homology to the same θ.
- Canonical limit comparison: for each integer q, the conclusion supplies F
  and object identifications E_n with b_n^*H^qK_n. Its map equation fixes every
  transition to `limitTransition`, using the cone equation and exact-pullback
  composition. The natural transformation c is a cocone with vertex H^q K,
  and every leg is explicitly E_n followed by the homology of β_n. The actual
  `colimit.desc F (Cocone.mk _ c)` is required to be an isomorphism. Separate
  `IsZero` clauses assert both colimit F and H^q K are zero.
- Actual etale and proetale units: `IsIso (unit A T.limitInclusion)` and
  `IsIso (proetaleUnit A T.limitInclusion)` concern the published derived
  adjunction units. The latter uses the ordinary proetale sheaf category,
  `singleFunctor` of the constant discrete ring, and total `rightDerivedFunctor`.
  The construction uses K-injective resolutions, without completion.
- Same unit under site inverse image: `sitePullback` descends the published
  canonical sheaf inverse-image comparison and its exact/left-derived
  comparison. `siteMate` is its actual adjunction mate. Its finite-constant
  component is required to be invertible, and the final equation identifies
  the inverse image of the etale adjunction unit with the proetale unit
  through that mate and the same pullback comparison. It is stated for every
  L, so includes the constant object and its usual canonical constant
  identifications, without choosing an unrelated isomorphism of direct images.
- Small compatible universes: explicit `universe u`; schemes are `Scheme.{u}`,
  coefficient rings and their module values have universe u+1, and the
  countable divisibility index is small. No equality of site universes is added.

Dependency declarations reused:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- Mathlib Scheme, Noetherian, IdealSheaf: `Spec`, `IsAffine`, `IsNoetherian`,
  `Scheme.zeroLocusSubscheme`, `Scheme.zeroLocusSubschemeι`, `Scheme.basicOpen`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible`.
- Mathlib constant sheaves and colimits: `constantSheaf`, `Cone`, `IsLimit`,
  `Cocone`, `colimit`, `colimit.desc`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` and its public
  interface: `SupportedKummerBoundary`.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`, owned by
  `def-asd-ordinary-finite-p1-kummer-class` already in the dependency closure:
  `ordinaryFiniteConstant`, `ordinaryFiniteUnit`, `ordinaryFiniteLine`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`: `finiteEtaleTateSheaf`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateLinePullback`:
  `finiteEtaleTateLine_pullback_normalized`, with its full generator equation.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTensorFamily`:
  `finiteEtaleTateLineInverse`, `finiteEtaleTateTensorFamily`.
- `WeilConjectures.SixFunctors.OpenClosed.SupportedSections`:
  `sectionsWithSupport`, `sectionsWithSupportι`; ordinary total derivation uses
  `Functor.rightDerivedFunctorNatTrans` and its exact-functor comparison.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`:
  `exactDerivedBaseChangeMap`, `exactDerivedSquareUpperStarIso`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`:
  `upperStarComp`, and `Scheme.upperStarConstantSheafIso`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`:
  `ProEtale.derivedUpperStarLowerStarAdjunction` and the exact/left-derived comparison.
- `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`:
  `comparisonUpperStar`, `comparisonUpperStarCompUpperStarIso`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the ordinary
  K-injective total right-derived convention; the main constructions reuse the
  canonical monomorphic-resolution model already provided by the live library.

The proof docstring contains the six DAG proof steps. Stated proof dependencies
are imported, including relative continuity, exact inverse image, homology
preservation, the fibre long exact sequence, forget-coefficients exchange, and
ordinary etale/proetale direct-image comparison. The unstated ramified supported
purity proof node is a stage-3 proof prerequisite, not a missing object used to
parameterize or weaken this stage-2 statement.

Edge cases checked: the empty scheme satisfies the universal local conditions;
a unit parameter gives an empty divisor and whole-scheme puncture; the identity
transition has exponent one; exponent greater than one uses a genuine nonreduced
E and its reduction rather than an equality of schemes. For the usual tower
Spec k[t^(1/n)], the parameter identity has the stated direction and exponent.
For n→n ell^s the coefficient scalar is zero. No nonempty or irreducible
hypothesis occurs, and the theorem does not require a fixed base field.

Searches: `msearch.py` LeanFinder on finite torsion root-limit unit invariance
returned eight unrelated ring/period-ring/local-cohomology declarations;
Loogle `"Etale", "IsIso", "unit"` returned zero hits. Mathlib grep for
ramification and supported purity returned five unramified-locus hits, none the
statement. The exact tool results are retained in `searches.jsonl`. Project
searches in `WeilConjectures/`, `Sheaf/`, and `dag/lean_names_upstream.json`
found neither the theorem nor a general ramified scheme-tower interface. The
existing tame-root order carriers do not supply this divisibility-indexed
functor with general schemes, global parameters and a limit cone. The extra
Tate and unbounded-exchange definition nodes added to stmt_deps are already landed interfaces,
not replacements or new copies of those notions.

## New nodes

`def-sfb-ramified-root-tower`, module `Sheaf.Paper.RamifiedRootTower`, packages
exactly the indexing order, scheme inverse system, parameters and limit cone
of the first paragraph. All data and canonical geometric abbreviations are
written in full, with no sorry. The remaining support, open-diagram and site-comparison helpers stay in the
assigned statement's module and are listed in lean.declarations.

`def-sfb-cartier-dual-kummer-normalization`, module
`Sheaf.Paper.CartierDualKummerNormalization`, owns `twistPullback`, `closedDual`,
`closedEvaluation`, `KummerNormalized`, and `closedExchange`. Its normalization
predicate accepts the actual K, inclusion and candidate P as explicit arguments;
the assigned theorem supplies exactly `support`, `inclusion`, and its purity P.
This changes no object or clause. It separates the real finite-Tate constructions
from the inverse-limit assembly so per-file elaboration stays within the limit.
Its definitions use the already proved, generator-normalized Tate pullback and
actual Tate tensor inverse; no data are selected from a bare Nonempty statement.
LeanSearch for canonical dual-Tate Cartier normalization returned eight unrelated
linear-duality and Kummer-Dedekind results. Loogle Ext/tensorLeft/Kummer and the
Mathlib grep returned no hits. Source and Sheaf searches found only generic
closed-evaluation duality and unrelated Kummer charts; the published supported
boundary predicate is reused. The blueprint search returned zero nodes. The new
node records the exact tool outputs and digests.

Searches for this missing interface: LeanSearch returned `InverseSystem`, its
recursors, its type-valued limit, and `AffineScheme`, but none the scheme tower
with these hypotheses. LeanFinder returned period-ring and type-system
examples; Loogle `"Scheme", "Coprime"` returned no hits; Mathlib grep for
`RamifiedRootTower|ramifiedRootTower|RamifiedRootIndex` returned no hits.
Equivalent source and Sheaf greps and the blueprint search returned no existing
notion. These exact queries, result names and digests are in mathlib_searches
of the new node. `blueprint_refs.py ancestor` returned None, retained as null.

## Dependency modules

None. Recorded mathematical notions are reused without repairing their interfaces.

## Validation

All three delivered files compiled without errors or warnings through the
prescribed scompile.py wrapper against the live library. The recorded library
compile times were 39.7 seconds for CartierDualKummerNormalization, 6.3 seconds
for RamifiedRootTower, and 30.0 seconds for RamifiedRootLimitTorsionUnit.
The canonical Tate definitions have their own owning definition node and module
to keep the individual compiler checks within the per-file limit. There is one
sorry, the assigned theorem, and no postponed definition data. Every node's
recorded signature is copied verbatim from its module.

An earlier dry run rejected a proved coefficient-annihilation helper. It was
removed; the main signature now applies the existing Mathlib theorem directly.
No theorem other than the assigned statement is delivered. The current layout
is checked again by the final server preflight and delivery compiler.

No second reading: this worker delivers directly for the maintainer's independent review.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
