## Worker report

The module `Sheaf.Paper.CondensedERealization` states
`WeilConjectures.condensedE_realization`, with its sole postponed proof `sorry`.
The records `At`, `Along`, `Data`, and `Exchange` package the clauses of this
one node. They are interfaces for its conclusion, not assumptions supplied to
the theorem. Their auxiliary definitions have real data. No other DAG theorem
is stated, no new node is created, and no dependency binding is changed.

Source read: Bhatt--Scholze, The pro-etale topology for schemes, Lemmas
4.2.12--4.2.13; Definition 6.8.1, Lemma 6.8.2; Lemmas 6.8.12--6.8.13,
Proposition 6.8.14(2), and Remark 6.8.15. The paper supplies the continuous
coefficient and scalar-localization route. As the node explicitly says, the
archived finite-presentation bridge and equality with the specified ordered
completed exchange are additional obligations. The archived definitions read
were `ConstructibleSheaf/ProEtaleModule/Def.lean`, its `DerivedCategory.lean`,
`ModuleObjects/Free.lean`, the restricted operations in
`ModuleObject/Derived/BoundedConstructible.lean`, and the three ordered steps
in `ModuleObject/BaseChangeTheorems/MorphismDefs.lean`.

Hypotheses and clauses, individually:

* Prime ell is `(l : ℕ) [Fact l.Prime]`.
* A finite normed extension is `(E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The given norm is
  compatible with the p-adic algebra structure, as in the coefficient nodes.
* The base is `(k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ l)]`: positive prime characteristic, distinct from ell.
* `Base k` bundles an arbitrary `Scheme.{u}`, its `Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` structure morphism.
  The middle two conditions are exactly finite type. All `Base k` objects
  are quantified in `Data.atObject`, with no extra geometric hypotheses.
* The valuation ring and uniformizer are the recorded `PbcIntegralRing l E`,
  `pbcIntegralDatum l E`, and `pbcUniformizer l E`. These use the project's
  lifted integer ring and its specified uniformizer; they introduce neither
  a new ring of integers nor a new rationalization.
* `Integral` abbreviates `PbcBoundedConstructibleComplete`; `Rational`
  abbreviates `PbcRationalCategory`. Thus objects and localized Hom modules
  are exactly those of the raw rationalization, with no Karoubi envelope.
* `Coefficient E T` is the actual `condensedRingObj` of
  `Profinite.continuousCoefficientRingObj E`; `Ambient` is its internal-module
  derived category and `Constructible` its archived `BoundedConstructible`.
* `At.coefficientIso` is an isomorphism of internal ring objects to the
  sheaf with sections `ULift C(U.unop.left,E)`. Here `U.unop.left` is the
  entire underlying scheme with its Zariski topology, not its closed points
  or its set of connected components. Pointwise ring operations and
  restriction by precomposition are the existing sheaf's definitions.
* `At.coefficient_normalization` fixes this isomorphism by its adjunct on
  every profinite test function, using `profiniteTestProjection`. It is not
  an arbitrary ring isomorphism. `sectionIso` and `section_normalization`
  identify its reconstructed commutative section ring with the dependency's
  `rationalCoefficientSheaf` using equality of every section value.
* `At.integralIso`, `finiteIso`, `finite_normalization`, and
  `integral_normalization` identify the completed integral coefficient ring
  with continuous integral functions and fix every quotient projection on
  constant generators and every integral function's residues.
  `inclusion` and `inclusion_normalization` fix the actual integral-to-field
  map by values. These retain the coefficient maps used in scalar extension.
* `At.realization : Rational l E T ≌ Constructible E T` is the equivalence.
  `moduleEncoding` uses the existing internal/sectionwise module equivalence
  and restriction through the displayed section-ring isomorphism.
  `At.scalarExtension` identifies the realization, on integral objects and
  maps, with `pbcDerivedExtend (integralIso.hom ≫ inclusion)` after these
  explicit encodings. Thus an unrelated equivalence does not satisfy the
  conclusion. Its additive encoding hypotheses are fields of the existential
  conclusion, not extra hypotheses on the theorem.
* `fieldScalarSections`, `fieldModuleLinear`, and `fieldDerivedLinear`
  construct the pointwise E-action on the sectionwise derived category.
  `At.linearity` states that mapping a morphism multiplied by a localized
  scalar equals its image multiplied by `pbcRationalCoefficientEquiv` of
  that scalar. Since this is a ring equivalence onto E and the encoding is
  faithful, this is precisely E-linearity of the realization in the two
  coefficient encodings.
* `At.integral_model` says every archived object is isomorphic to the image
  of `ScalarLocalization.mk M` for an integral `M`. It explicitly retains
  the integral-model assertion even though every raw localized object
  already has an integral underlying object.
* `At.lisse_criterion` is an iff for every ambient complex. The first
  conjunct is vanishing of cohomology outside some integer interval.
  For every degree, a finite `Scheme.Stratification`, and a pro-etale cover
  on each stratum, `Mod.IsFree` says the restricted cohomology sheaf is
  isomorphic to a finite biproduct of regular modules. The definition read
  in `ModuleObjects/Free.lean` quantifies a natural-number rank, not an
  unrestricted basis. The right-hand stratification is existential and
  may therefore refine the original finite-presentation stratification.
* `Data.along` quantifies every k-morphism between arbitrary `Base k`
  objects, using `[h.IsOver (Spec (.of k))]`. `Along.pull` and `push` are
  integral restrictions, tied to the specified ambient `completedPull`
  and `push` by `pullAmbient` and `pushAmbient`. Their additive and
  integer-linear structure is retained for the recorded tensor transport.
* `Along.rationalPull` and `rationalPush` are exactly
  `ScalarLocalization.transport` of those integral functors. They are not
  arbitrary rational functors. `pullComparison` and `pushComparison` are
  natural isomorphisms to the archived `boundedConstructibleUpperStar`
  and `boundedConstructibleLowerStar`, respectively. Those archived
  functors are the restrictions of the specified ambient derived functors;
  their public compatibility isomorphisms and preservation theorems were
  read in `Derived/BoundedConstructible.lean`.
* `Along.integralAdjunction` is normalized to the actual ambient unit and
  counit through `integral_unit` and `integral_counit`, with the specified
  ordinary-to-completed comparison. `rationalAdjunction`, `rational_unit`,
  and `rational_counit` retain the localized adjunction and its pure-tensor
  formulas. `Along.unit` and `Along.counit` are equalities of composites
  against the actual restricted condensed adjunction. They assert more
  than source and target isomorphisms.
* `Data.integralComp` and `integralComp_normalization` use the recorded
  completed-pullback composition. `rationalComp_normalization` fixes its
  tensor transport, and `composition` is the exact equality with archived
  `boundedConstructibleUpperStarComp`. The analogous `integralId`,
  `rationalId`, their normalization fields, and `identity` retain identity
  compatibility. `condensedId_normalization` fixes the condensed identity
  comparison by its composition-with-identity equation.
* `Data.square` explicitly composes the inverse first composition
  comparison, the equality transport for the two composite k-morphisms,
  and the second composition comparison. It needs only `CommSq`, not a
  cartesian square. `Data.mate` is `mateEquiv` for that square and the two
  retained rational adjunctions: the unit-square-counit transformation.
* `Exchange` alone introduces `ChosenCartesianSquare` and `[IsProper f]`.
  `Exchange.integral` is a natural transformation on the integral category.
  `integral_normalization` is equality, after the ambient inclusion
  comparisons, with `AdicCoefficientDatum.completedExchange`. This is
  definitionally the dependency's ordered `completedBaseChangeMap` on
  complete inputs with any allowed finite-origin witnesses.
* `Exchange.rational_normalization` equates the rational mate at each
  integral object to `1 ⊗` the specified integral exchange. `HEq` retains
  the equality through the definitionally identified scalar-localization
  objects; it does not merely assert existence of an isomorphism.
* `Exchange.condensed_normalization` is the equality of the J-image of that
  rational mate, followed by the target comparisons, with the source
  comparisons followed by the archived `boundedConstructibleBaseChange`.
  This fixes the order of the three steps and the actual transformation.
  No field asserts that either exchange is an isomorphism.

The theorem concludes `∃ D : Data l E k, Nonempty (Exchange l E k D)`.
Thus the category, all-morphism, adjunction, and composition assertions
precede and are independent of every properness/cartesian-square hypothesis.

Dependency declarations used (module, names):

* `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`,
  `pbcRationalization`, `pbcCompletedScalarSections`, and inherited linearity.
* `Sheaf.Paper.IntegralUniformCoefficient` publicly reexports
  `PbcBoundedConstructibleComplete` and its defining predicate from
  `Sheaf.Paper.BoundedConstructibleComplete`. The main statement uses this
  same generic predicate at `pbcIntegralDatum`, rather than its newer
  convenience wrapper for an unlifted carrier in `Type (u+1)`.
* `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`:
  `Profinite.continuousCoefficientRingObj`, its commutative ring structure,
  and the reexported archived `condensedRingObj`, `BoundedConstructible`,
  restricted pull/push functors, their adjunction/composition, and exchange.
* `Sheaf.Paper.PbcRationalTransport`: `ScalarLocalization.transport`,
  its additive/linear instances, and `pbcRationalCoefficientEquiv`.
* `Sheaf.Paper.CompletedBaseChangeMap`: `AdicCoefficientDatum.completedExchange`
  and `completedBaseChangeMap` (the latter's body is the former).
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionRingSheaf`, `sectionModuleEquivalence`.
* `Sheaf.Paper.ContinuousCoefficientModuleEncoding`:
  `ringModuleEquivalenceOfIso`. Its general scheme-universe helper is used;
  its Type-0-only convenience encoding is not specialized to the wrong
  universe. Missing local source was read through `scompile.py --source`.
* `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `coefficientExtensionNormedField`, `integralCoefficientSheaf`,
  `rationalCoefficientSheaf`, finite continuous coefficients, the value
  functions, and `integralRationalCoefficientNormalized`.
* `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralCoefficientULift`, for the residue normalization.
* `Sheaf.Paper.CompletedExchangeCoherence`: `AdicCoefficientDatum.pullId`
  and `completedPullComp`, both normalized by the actual completion unit.
* `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`:
  `profiniteTestProjection` and the unique-adjunct characterization used
  in `coefficient_normalization`; current source read through `--source`.

The six additional statement dependencies are already existing DAG nodes
with published Lean declarations. They expose only coefficient encodings,
normalizations, and composition maps used to express the original node.
The node's natural-language statement and proof are unchanged. The remaining
imports are the recorded, stated proof dependencies, imported without
`public` as the stage contract prescribes.

Edge cases checked: the empty scheme is admitted by `Base`; the zero
complex satisfies any suitable finite cohomological interval, and rank zero
is allowed in `Mod.IsFree`. Empty finite stratifications and covers retain
their existing definitions. Bounds are existential integers, not a
nonnegative truncation. Negative cohomological degrees are included.
Non-quasi-compact pro-etale test objects use the entire function sheaf;
no global bounded-denominator claim is included. Identity morphisms and
two composable arbitrary k-morphisms occur before properness. The exchange
clause quantifies all integral inputs and all chosen cartesian squares,
including identities, and requires no inverse to exchange. The universe is
arbitrary `u`, matching the scheme, coefficient, base-field and archived
framework convention; coefficient sheaves and internal modules use the
required `u+1` lift without equating site object/morphism universes.

Searches repeated using the prescribed `msearch.py Q51` wrapper:

* LeanFinder: "Rationalization of integral constructible proetale complexes
  realizes condensed E module objects compatibly with pullback and
  pushforward adjunctions". Eight results: generic condensed free/solid and
  locally constant module functors/adjunctions; no realization equivalence.
* Loogle: `"Condensed", "Equivalence"`. Three results: equivalences between
  coherent sheaves on Stonean, profinite, and compact Hausdorff sites. None
  compares integral rationalization with the category in this node.
* Mathlib grep: `rationaliz|rationalis|condensedRingObj|boundedConstructible`.
  One irrelevant rational-number computation in `Analysis/Real/Pi/Bounds`.
* Direct `rg` of upstream `WeilConjectures`, side `lean`, and the upstream
  name index for the node id, `condensedE_realization`, and
  `CondensedERealization`: no existing realization declaration; only a
  proof docstring in `CondensedQbarBaseChangeCompatibility` cites this node.
  The earlier sandbox's logged searches also include LeanSearch service
  failures, recorded as unavailable rather than as absence of a match.

There is no statement correction or disputed mathematical assertion.
The initial full-artifact compile reached the fixed 60-second limit. Profiling
identified automatic size-function generation for the large dependent records.
The module now sets `genSizeOf false` and `genInjectivity false`; the
automatically generated size functions and constructor-injectivity lemmas
are unused. All mathematical fields and the theorem signature are unchanged.
With those auxiliary generators disabled, `scompile.py` passed cleanly:
sandbox check 23.8 s, library artifact 29.1 s, with the fixed 60 s limit,
two threads, and no warnings. The required dry delivery check follows.

## Second reading by Q51

I reread the node statement, its source places (Bhatt--Scholze Lemmas
4.2.12--4.2.13, Definition 6.8.1, Lemmas 6.8.2 and 6.8.12--6.8.13,
Proposition 6.8.14(2), and Remark 6.8.15), every recorded statement dependency,
and the complete Lean module. The item-by-item correspondence is:

* The prime, finite normed extension, and positive characteristic base field
  hypotheses are the binders of `condensedE_realization`; `Base` introduces
  exactly a scheme over `Spec k`, locally finite type, quasi-compact, and
  separated structure. Thus it renders “separated finite-type `k`-scheme”
  without an extra geometric assumption.
* `Integral`, `Rational`, `Coefficient`, `Ambient`, `Constructible`, and
  `SectionRing` are the recorded bounded-complete category, raw scalar
  localization, condensed coefficient ring, ambient derived module category,
  archived bounded-constructible subcategory, and reconstructed section ring.
  They reuse the dependency declarations and do not introduce a Karoubi
  envelope or a second coefficient notion.
* `At` contains the canonical coefficient ring isomorphism, its test-function
  normalization, section-ring identification and value normalization, finite
  quotient and completed integral identifications, inclusion, additive module
  encoding, realization equivalence, scalar-extension comparison, `E`-
  linearity, integral models, and the bounded-cohomology/finite-rank
  stratified `Mod.IsFree` criterion. These are exactly the first paragraph's
  coefficient and realization clauses; all ranks are natural numbers and all
  stratifications and covers are existential as in the node.
* `Along` quantifies every morphism over `Spec k`; its pull and push are the
  specified integral completed operations, `rationalPull` and `rationalPush`
  are their `ScalarLocalization.transport`, and the comparison, unit, and
  counit fields give precisely the two functor comparisons and adjunction
  compatibilities in the second paragraph.
* `Data` quantifies all composable morphisms and supplies integral and rational
  composition and identity isomorphisms with their completed/tensor
  normalizations. `Data.square` uses only the commutative-square equality and
  the recorded composition comparisons, while `Data.mate` is the specified
  unit--square--counit mate. Hence no Cartesian or properness hypothesis leaks
  into the all-morphism clauses.
* `Exchange` alone adds chosen Cartesian squares and `[IsProper f]`; its three
  normalization fields identify the specified completed exchange, its
  rational mate on every integral input, and the ordered condensed base-change
  arrow. They assert equality of the specified arrows and no invertibility.
  The theorem conclusion is exactly
  `∃ D : Data l E k, Nonempty (Exchange l E k D)`.

Edge cases checked: `Base` admits the empty scheme; zero complexes and rank
zero satisfy the bounded/free clauses; empty finite stratifications and covers
retain their definitions; integer bounds include negative degrees; identities
and arbitrary composable morphisms occur before the exchange's properness
hypothesis; identity Cartesian squares and all allowed integral inputs are
included. The coefficient and site universes use the required `u+1` lift and
do not impose an equality of object and morphism universes.

The prescribed LeanFinder, Loogle, LeanSearch, Mathlib grep, upstream grep,
and side-project searches found no existing realization declaration or exact
statement. The six dependency declarations were opened and match the notions
used by the module; no dependency repair or statement correction was needed.
The only implementation change from the worker was retaining
`set_option genSizeOf false` and `set_option genInjectivity false` so the large
records compile under the fixed timeout. The theorem signature remains
verbatim equal to the node's `lean.statement`. `scompile.py` succeeds for the
module with no errors or warnings.
