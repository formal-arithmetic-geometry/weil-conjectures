## Worker report

NS states `lem-sfb-integral-ambient-tower-comparison` in
`Sheaf.Paper.IntegralAmbientTowerComparison`. All mathematical results are named
`sorry` theorems with source and proof docstrings. All definitions have real data.
The original node statement is unchanged. Positive paper index n is encoded by
Lean index n+1, including n=0 for the first quotient.

Hypotheses and clauses, in order:

* Prime ell is `(l : ℕ) [Fact l.Prime]`; E is
  `PadicAlgCl.FiniteIntermediateField l`, so it is literally the finite intermediate
  field in the fixed algebraic closure, with its given p-adic topology. Its valuation
  ring is the existing `PadicAlgCl.integers l E.1`. `π` is in that ring and `hπ`
  says its principal ideal is the maximal ideal, precisely a uniformizer here.
  `integers` is only ULift of that same ring to the site's coefficient universe;
  `quotientScalars` is quotient-mk composed with the ULift ring equivalence.
* `datum` uses the actual ideal `Ideal.span {ULift.up π}`. Its named
  `arithmetic` well-definedness theorem states Noetherianity, finite generation,
  additive torsion of the residue, finiteness of all positive quotients and their
  perfectness. It determines every datum field: there is no existence choice.
* `multiplication` is multiplication by π^(n+1) on A[0]; `resolution` is its
  mapping cone. `finiteResolution` states ell^(n+1) annihilation, an augmentation
  quasi-isomorphism to the actual quotient in degree zero, strict bounds -1 and 0,
  finite free terms through `HasFiniteFreeTerms`. The quotient target is the explicit
  principal-ideal quotient, definitionally the ideal used by datum.
* `integralRing`, `quotientRing`, `quotientProjection` reconstruct the *existing*
  pulled-back condensed coefficients and their actual reduction maps as section
  rings. `CoefficientModel` specifies the finite/completed isomorphisms and the
  equation `completed.hom ≫ d.projection = quotientProjection ≫ finite.hom`.
  Its constants clause fixes the scalar quotient, via `chartComparison` and
  `finiteOriginConstantIso`, on local constant sections. This excludes arbitrary
  finite-ring automorphisms. `coefficientModel_exists` supplies these models with
  no scheme hypotheses. Since `d.completedRing` is the actual limit, this states
  the required inverse-limit identification, with its projections.
* The inverse-image coefficient identifications are the existing
  `coefficientPullbackIso`, `condensedPullbackHom` / `cartesianCoefficients` and
  `d.integralRingIso`, `d.finiteRingIso`; compatibility with reduction is the
  existing `d.projection_comm`. Their normalized comparison is used by
  `encodings`, with the coefficient-model projection equation.
* Internal module coordinates are transported by the existing
  `InternalAbelianSheafModule.sectionModuleEquivalence` followed by
  `CondensedRing.ringModuleEquivalenceOfIso` along `completed.symm`.
  `CoefficientModel.derived` is their termwise exact derived equivalence.
  `AmbientEncoding` compares the literal
  `CondensedRing.moduleObjectDerivedPushforward` (ordinary total K-injective
  right derived direct image, with no completion) with `d.push`.
  Its ordinary map is identity on underlying sections; its derived map is
  normalized against the universal right-derived units on every complex.
  `encodings` asserts existence for every f and every coefficient model, so these
  data are not extra hypotheses on the main comparison.
* `quotientRoosComplete` states exactly the augmented quotient-tower Roos triangle
  condition from `def-weil-derived-complete`, in the d.derived coordinates.
  `complete_iff` compares this predicate with invertibility of the specified
  `d.completionUnit`; these conditions are not identified by definition.
* The main `comparison` binds arbitrary schemes `{X Y : Scheme.{u}}`, their
  morphism `f`, `[QuasiCompact f] [QuasiSeparated f]`, arbitrary unbounded
  `K : d.derived X`, and `hK : d.quotientRoosComplete X K`.
  There are no hypotheses on characteristic, global qcqs of X or Y, properness,
  constructibility, or Tor amplitude.
* Its first conjunct is completeness of `(d.push f).obj K`, the ordinary ambient
  M in these coefficient coordinates. Its second is `IsIso (d.finiteProjection
  f K n)` for every n, in the finite-coefficient derived category. These are the
  existing counit/projection mates, not arbitrary maps or an assumed projection
  formula. The third is invertibility of `d.towerProjection f K` in the derived
  category of *strict towers*. The fourth identifies each evaluation, via
  `d.towerPushReductionEvaluation`, with restriction of the actual finite
  projection after `completedReductionEvaluation`. Thus quotient transitions
  commute before taking Rlim, rather than just at individual levels.
* The fifth conjunct makes `d.completionUnit Y M ≫ completedRlim.map
  (d.towerProjection f K)` invertible. Its last conjunct identifies that exact map
  with `d.push.map (d.completionUnit X K)` followed by the projection-normalized
  `d.directImageRlimIso`. This retains the actual completion/quotient augmentation.
* `finiteFixed` first restricts along `finiteOriginConstantIso`, then applies the
  existing `ConstantScalarRestriction.restriction`, retaining induced scalar
  action. `finiteDerivedFixed` uses localization sizes u+2 and u+1 respectively;
  this does not identify the site's object universe u+1 with morphism universe u.
  `FinitePushEncoding` compares finite ringed direct image with fixed-scalar
  pro-etale direct image by the section-identity and derived-unit normalizations.
* `etaleOriginComparison` states the optional etale clause by specializing the
  fully expanded `FiniteEtaleOriginComparison` to the exact `datum l E π hπ`,
  f and K of the item. This predicate quantifies over every level n and every
  normalized finite encoding H (supplied by encodings), every specified etale
  `DerivedCategory.Plus` object L, and its bound b. `θ` is precisely the supplied
  isomorphism from `finiteDerivedFixed X (A/I^(n+1)) (d.reduction X n K)` to
  ν_X^* L. The conclusion asserts IsIso of the actual derived morphism from the
  encoded `d.finitePush f n (d.reduction X n K)` to ν_Y^* Rf_et,* L. Its arrow is
  pinned to `FiniteCoefficientPushEncoding.comparison.hom.app K_n ≫
  proEtalePush.map θ.hom ≫ etaleComparisonInverse`. Here `proEtalePush` and
  `etalePullback` are typed specializations of the existing total derived direct
  image and exact comparison inverse image; `etaleComparisonInverse` is literally
  inv of the canonical mate, certified by the published bounded-below theorem.
  Thus asIso gives the required canonical isomorphism in the derived category.
  No compatibility between antecedents at different levels is imposed. Every Plus
  object has a lower bound, so b excludes none. Completeness is not needed for
  this optional clause beyond its role in the separate integral comparison.


Dependency declarations used: `Sheaf.Paper.AdicCoefficientDatum`
(`AdicCoefficientDatum`, its `finiteRing`, `completedRing`, `derived`, `reduction`,
`completedReductionTower`); `Sheaf.Paper.FourCorners` (`push`, `finitePush`,
`projection_comm`, `integralRingIso`, `finiteRingIso`);
`Sheaf.Paper.FourArrows` (`finiteProjection`);
`Sheaf.Paper.CompletedDirectImageLimits` (`towerProjection`,
`towerPushReductionEvaluation`, `directImageRlimIso`);
`Sheaf.Paper.CompletedPullback` (`completionUnit`, `TowerComplete`);
`Sheaf.Paper.CompletedRlimFunctor` (`completedRlim`, `completedRlimRoosProjection`);
`Sheaf.Paper.CompletedCondensedCoefficients` (`completedResidue`,
`completedReduction`, `completedCondensedIntegral`);
`Sheaf.Paper.ContinuousCoefficientModuleEncoding` (`sectionRingMap`,
`ringModuleEquivalenceOfIso`, `chartComparison`);
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
(`sectionRingSheaf`, `sectionModuleEquivalence`);
`Sheaf.CategoryTheory.ConstantScalarRestrictionTensor` (`restriction`, its exactness);
`Sheaf.Paper.RingedEtaleOriginWitness` (`finiteOriginConstantIso`);
`Sheaf.Paper.CondensedModuleDerivedPushpull` (`moduleObjectDerivedPushforward`);
`Sheaf.AlgebraicGeometry.UnboundedDirectImageComparisonMap`
(`unboundedDirectImageComparisonMap`);
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`
(`rightDerivedFunctorUnitQ`); Mathlib mapping cones, derived categories and Plus.
The proof-only imports in the item retain its existing eight-step proof plan;
the coefficient definition module no longer copies those imports.

Edge cases read against the signatures: first quotient n=0, E=Q_l, ramified E
(the exponent ell^(n+1) remains valid), empty schemes, zero K and zero complexes,
identity f, arbitrary characteristic including ell, non-quasicompact X and Y with
qcqs f, and unbounded K. Only the optional étale antecedent is bounded below.
No independent test-algebra universe appears. All variables and universes are bound.

Searches: msearch leanfinder for ordinary derived pushforward preserving derived
adic completeness returned only scalar AdicCompletion declarations; loogle
`IsDerivedComplete, rightDerivedFunctor, ModuleCat` returned no match; grep
`derivedPushHom|adic.*pushforward|[Cc]omplete.*[Pp]ushforward` in Mathlib
CategoryTheory returned none. Additional LeanSearch, LeanFinder, Loogle,
Mathlib/project grep and DAG/blueprint searches for normalized coefficient
presentation and encoding are recorded in each new node's `mathlib_searches`.
No exact existing combined declaration was found. The existing generic
`CompletedCoefficientPushforward.Square` is restricted to a single localization
universe and different coefficient models; `NormalizedSquare` permits the actual
mixed localization sizes without forcing the site universes equal.

No statement correction and no STATEMENT-DISPUTED flag.

## Second reading by NS

Solo second reading, as required by the dispatcher instruction prohibiting other
agents: the item and all delivered definitions were reread clause by clause.
The independent maintainer review remains required. During this reading, arbitrary
isomorphism-only encoding interfaces were replaced by section-identity and
universal-derived-unit normalizations; the Roos predicate was kept distinct from
IsIso of a selected unit; the exact finite scalar action was retained; theorem
signature lets were expanded; and fixed-scalar localization uses its actual u+1
universe. No mathematical hypothesis was added to the item.

## New nodes

`def-sfb-integral-ambient-coefficient-presentation` defines the specified coefficient
presentation and its actual module transports. The datum's ideal is constructed,
not chosen; its named arithmetic proof is only a well-definedness obligation for
that fixed datum. The two-term cone is a real complex. The source is BS Section 6.5
and Lemma 6.5.9(3). Existing nodes supply the separate ring models and section/module
encoding, but none supplies their quotient-normalized identification for this
finite intermediate field. The new node records all required searches.

`def-sfb-integral-ambient-direct-image-encoding` defines the mixed-universe derived
square with universal-unit normalization, and its section-normalized integral and
finite specializations. The source is BS Section 6.5 and Stacks 0D6E. The existing
single-universe square cannot express the fixed-scalar specialization at the
published localization sizes; the same normalization is used without introducing
a new direct-image functor. Searches found no existing instance of this notion.

`def-sfb-completed-rlim-roos-projection` owns the canonical product lift of the
published `completedRlimProjection` maps. Its `existing: true` binding is exactly
`AlgebraicGeometry.Scheme.completedRlimRoosProjection` in
`Sheaf.Paper.CompletedRlimFunctor`; no Lean is copied. LeanSearch and LeanFinder
returned generic product/inverse-system results; Mathlib grep returned generic
`Pi.lift` constructions. DAG grep finds only the Rlim theorem record, and the
project source supplies the exact definition. The new node records the raw search
summaries. The existing `def-pur-completed-rlim-functor` owns `completedRlim` and
its projections and is now cited directly.

The coefficient-presentation definition node additionally owns
`quotientRoosComplete` and its two specialized sheafification instances. The
predicate uses the actual quotient tower and its prescribed unit legs, through
the product projection just owned by the new definition node. Its statement and
record list all three declarations. The existing global/slice completeness
record is preserved without any dependency-node delivery.

Final compilation note: the ordinary comparison and strict completion statements
compile without warnings. The mapping-cone terms are tested through the generic
`HasFiniteFreeTerms` predicate to avoid unfolding categorical biproducts during
scalar-structure inference. The existing bounded-below etale theorem supplies the
inverse used in the new item-coordinate `etaleOriginComparison`; it is not claimed
as a declaration of this item. No independent second-agent review is claimed.

The generic finite-free-term predicate was also checked against
`WeilConjectures.CategoryTheory.DerivedCategory.Perfect.FiniteFree`: that module
uses the same termwise Module.Free / Module.Finite assertions inline and supplies
no predicate with this meaning. The helper packages precisely those existing
Mathlib predicates, without a new definition of freeness.

## Return repair and final self-check

H13: removed the delivered copy of `def-weil-derived-complete.json` and the
standalone `AdicQuotientRoosCompleteness` module. The live
`DerivedCompleteOnSlices` / `IntegralOnSlice.IsComplete` binding is untouched.
The quotient predicate and two instances now belong to the new coefficient
presentation definition node, whose statement records their role.

H2: replaced the mistaken statement dependency on
`prop-weil-pbc-rlim-functoriality` with its existing definition-node owner
`def-pur-completed-rlim-functor`; added the existing-definition owner
`def-sfb-completed-rlim-roos-projection`. The genuine theorem dependencies
`prop-weil-pbc-direct-image-limits` and
`lem-sfb-constant-scalar-restriction-tensor` remain: the former determines the
canonical strict tower map by unique characterization, and the latter supplies
the exact equivalence used in finiteFixed. No properties theorem was replaced
by an assumed arbitrary map.

H3: removed the borrowed bounded-below theorem from the item's declarations.
Added `etaleOriginComparison` with the actual finite quotient, reduction, finite
pushforward and normalized encoding. Read against the final sentence of the node
and Bhatt--Scholze 5.4.3: L is bounded below, theta is specified, the target is
ν_Y^* Rf_et L, and the displayed morphism is exactly the normalized finite comparison,
Rf_* theta, and inverse canonical mate. Zero K, empty schemes, identity f and
negative lower bounds remain permitted. No main integral conjunct changed.

Advisory: corrected the coefficient module's copied title and removed the
item's twelve proof-only imports from it. They remain in the item module.
Solo second reading of all changed files checked the three repairs against the
return; no independent agent was started, as instructed. The first mechanical
dry run of the saved packet passed, but did not check these mathematical defects;
this repair changes the saved packet concretely before the final validation.

Final elaboration self-check: `FiniteCoefficientPushEncoding` defines the same
normalized finite square for an abstract adic datum. `FinitePushEncoding` is its
literal specialization to the valuation-ring datum, and its comparison is the
same normalized-square projection. `FiniteEtaleOriginComparison` writes the
complete optional clause first for that abstract datum; the item's theorem
specializes it to the original datum, f and K. This keeps quotient fields abstract
while elaborating and avoids expensive unfolding of the p-adic arithmetic data.
No new notion of direct image, scalar action, localization or comparison is used.
The fixed-scalar category uses the ordinary sheaf abelian structure consistently;
only cached duplicate instance routes from ConstantScalarRestriction are disabled
for elaboration. The sites retain object universe u+1 and morphism universe u.
No local notation, definition or instance and no heartbeat/timeout increase remains.

Validation: scompile compiled every delivered module separately against the live
published build, with no errors or non-sorry warnings. The item compiled in 16.7 s,
the normalized encoding in 5.2 s and the coefficient presentation in 25.9 s.
The final delivery dry run and its per-file check are recorded by deliver2.py.
