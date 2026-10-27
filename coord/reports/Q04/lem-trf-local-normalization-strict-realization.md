## Worker report

The module `Sheaf.TraceFormula.LocalNormalizationStrictRealization` states
`WeilConjectures.LocalNormalization.localNormalizationStrictRealization` and gives
explicit canonical constructions for all maps appearing in its `Laws` conclusion.
All eight postponed assertions are named theorems, owned by this DAG node, with
source and proof docstrings. Every definition has real data. Selections are from
unique characterizations of a map or isomorphism, including its normalization;
there is no selection of an arbitrary comparison map or triangle filler.

The source is the node's extracted ten-step proof, ultimately the last transport
sentence of main-20261015 `prop-trf-karoubi-independence.proof.md`. The blueprint
file itself has only that short motivating sentence, so the detailed normalization
requirements are read from the accepted node statement and its ten proof steps.
No change to the mathematical statement was needed.

Hypotheses, objects and clauses are rendered as follows:

- The global tuple is the existing `FiniteFieldDatum D`: its prime, positive
  exponent, cardinality, finite field and fixed algebraic closure are fields of D.
  `l`, `Fact l.Prime`, `hl : l ≠ D.p`, `E`, its field/algebra instances and
  `FiniteDimensional ℚ_[l] E` give exactly the coefficient assumptions. Its integer
  ring, chosen uniformizer, and positive quotients are the existing Padic objects.
  An arbitrary finite extension is used; a choice of an embedding into the fixed
  algebraic closure does not occur in any construction or equation here.
- `X₀ : Over (Spec (.of D.k₀))`, `LocallyOfFiniteType X₀.hom`,
  `QuasiCompact X₀.hom`, and `IsSeparated X₀.hom` give separated finite type.
  The geometric fibre is exactly `(D.geometricFiber X₀).left`; the point scheme
  is `Spec (.of D.k)`. Scheme and Galois Frobenius are the recorded constructions.
- `hm : 1 ≤ m` retains every positive period. `Point D X₀ m` bundles an
  arbitrary scheme map `z`, `overBase` asserting that it is a k-point, `fixed`
  asserting `z ≫ Phi^m = z`, and `returnSquare` asserting `g_s^m ≫ z = z ≫ g^m`.
  It does not restrict z to a separately chosen finite-subfield point or minimal
  period, and it assumes no arbitrary comparison arrow.
- `K : sfIntegralConstructibleCategory ...` gives derived completeness,
  constructibility of every positive reduction and a single uniform cohomology
  interval. `Q : (integralOperationsGoodComplex ...).FullSubcategory` gives
  precisely K-flatness with flat terms, without any boundedness of Q.
  `q : DerivedCategory.Q.obj Q.obj ≅ K.obj` identifies this representative with K.
  Quantification over Q and q covers every representative and quasi-isomorphic
  resolution named by the node; no particular resolution is imposed.
- `quotient` uses `unrestrictedIntegralFiniteComplex` on the single Q. `tower`
  is the existing `PointPullbackRepresentative.sectionTower`, retaining all actual
  quotient transitions. `levelModel` changes only the finite pullback and scalar
  presentations; its identity-on-sections characterization fixes this change.
- `finitePull`, `finiteSections`, `finiteComp` use ordinary module pullback and
  exact point sections. `finiteInsertion` is restriction followed by the recorded
  inverse-image/tensor-unit comparison. `finiteSuccessiveInsertion` composes the
  one-step insertions recursively; the zero case is the identity in canonical
  identity-pullback coordinates. This renders I^(0)=1 and the successive I recipe,
  rather than replacing it by an unexplained direct power map.
- `finiteA` is these successive point insertions followed by the canonical return
  comparison. Its endpoint is the direct-composite pullback by `z ≫ g^m`.
  The common final compositor identifies this endpoint with P G^m as in the node.
- `finiteKappa` is the ordinary absolute-Frobenius normal form specified by the
  recorded scheme/Galois comparison theorem. `finiteB` composes the fixed-point
  rho, pullback of that kappa, and that same final direct-composite compositor.
  These are actual chain maps, not representatives arbitrarily selected from
  derived Hom classes. The existing annihilator theorem is reused directly.
- `StrictMaps` is a pair of morphisms between the entire actual section towers.
  `Components` specifies both recipes at every level before localization.
  `strictRecipes_existsUnique` asserts their transition compatibility and unique
  assembly. `strictRecipes` selects only that uniquely determined pair. `Laws`
  asserts its component characterization on every permitted Q; naturality of a
  strict map includes all quotient transitions, not merely adjacent ones.
- `CoefficientCompatibility` quantifies over every `j ≤ n`; the actual exponents
  are j+1 and n+1. `coefficientComparison` is the uniquely prescribed ordinary
  tensor associator, fixed on every generator using the actual quotient map.
  The two displayed commuting squares concern both finiteA and finiteB. The
  `IsIso` clauses on the actual derived tensor counits ensure that these ordinary
  squares compute the canonical derived coefficient squares, including nonflat
  quotient maps. They impose no Tor-amplitude assumption on K or its reductions.
- `B : IntegralComparisonSystem l` is the specified normalized comparison family
  from the recorded dependency. Its constituent realization models retain their
  K-flat/counit normalizations. `pointPowerModel` and `integralReturn` use its
  specified integral compositors, including its identity comparison at zero.
- `successiveIntegral` starts with identity and composes the actual dependency
  `frobeniusPointTransportIntegral` at every successive U^j N.
  `integralA` is defined independently of strict realization as that successive
  recipe followed by the specified return compositor. Thus its realization law
  is substantive, not a definition of integral transport by the tower map.
- `realize` uses `integralOperationsRoosMap` and the dependency's canonical
  `PointPullbackRepresentative.representative` on both endpoints. These are
  whole-system comparisons with both cone coordinates specified. It is the
  functorial Rlim model, not an assertion deduced from separate derived levels.
  `integralAInCoordinates` transports the independently specified integralA to
  exactly these section/localization coordinates. The corresponding clause of
  `Laws` states equality with realization of A. The stipulated B realization is
  exactly `realize ... (strictRecipes ...).2`, with identical endpoint comparisons.
- The implication in `Laws` assumes equality of finiteA and finiteB as actual
  chain maps at every level, and concludes equality of the strict maps, equality
  of the integral realizations, and equality after raw scalar localization.
- `rationalize` is the same raw `ScalarLocalization` construction underlying
  `sfRationalConstructibleCategory`, now on integral point modules; it adjoins no
  idempotents. Its coefficient ring is the existing ULift presentation of O_E.
  `successiveRational` uses each recorded `frobeniusPointTransportRational` component
  in `pointRationalFibre` coordinates.
  `rationalAInFibre` uses that recurrence and the canonical coefficient tensor/size-descent
  images of the specified compositors. `rationalPointHom` is the unique additive
  equivalence fixed on every pure tensor; `rationalA` uses its inverse to return
  this independently specified rational recipe to the raw module coordinates.
  `Laws` asserts that rationalization carries integralA to this successive recipe.
- `integralJ` is P followed by the recorded ambient point fibre. Its additivity
  and semilinearity are stated as named helper theorems. `rationalJ` uses the
  existing semilinear scalar-localization extension, which specifies its Hom maps
  on all pure tensors. The final two clauses assert integral naturality and
  naturality for every arrow of the raw rationalized category, respectively.
  No restriction to arrows lifted integrally is made.

Dependency declarations read and used (module paths below have prefix `Sheaf.`):

- `Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.geometricFiber`.
- `NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`,
  with the coefficient constructions publicly reexported by that module.
- `AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  with the existing finite/integral ambient operations.
- `Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient`, `pointIntegralSections`,
  `pointFiniteSections` and their exactness/size conventions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `SixFunctors.SchemeFrobenius`: `schemeFrobeniusIterate`, `geometricGaloisFrobenius`,
  `schemeFrobeniusCoefficientInvertible`.
- `Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`; the good-complex
  predicate used for Q is the existing `integralOperationsGoodComplex`.
- `Paper.IntegralPullbackComparisonRealization`: `IntegralComparisonSystem`,
  `integralComparisonComposition`, `integralComparisonUnit`.
- `Paper.IntegralFinitePullbackComposition`: `integralFinitePullbackModel` and
  the publicly reexported canonical ordinary/derived pullback compositors.
- `SixFunctors.SelectedSchemeGaloisComparison`: the selected
  `FiniteFieldDatum.canonicalSchemeGaloisComparison`, retained through the precise
  ordinary normal form of `SixFunctors.SchemeGaloisComparisonNormalForm`.
- `SixFunctors.FrobeniusPointTransport`: `frobeniusPointTransportIntegral`,
  `frobeniusPointPrimeInvertible`, and the underlying finite tensor-unit recipe.
- `CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  total derived strict inverse limit; used through the recorded Roos realization.
- `Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, whose
  `ScalarLocalization` and actual integral objects are retained exactly.
- Additional already landed owners now cited in stmt_deps: the point representative
  diagram (`representative`, `sectionTower`); point transport powers
  (`pointPowerFiniteSigma`); integral tower powers (`integralCompositor`); scheme/Galois
  normal form; finite-reduction tensor/counit/generator API; the existing finite-ring
  annihilator specialization; integral section localization transport
  (`sfSectionsCoefficientLift`, `sfSectionsCoefficientLiftIso`); the actual quotient
  ring map (`pointReductionQuotient`); and semilinear raw scalar extension
  (`ScalarLocalization.IsSemilinear`, `.extension`). No dependency is redefined.
  All recorded proof-dependency modules are imported, privately unless their
  declarations also occur in the public constructions.

Edge cases checked: m=1 gives one successive transport, not zero; intermediate
j=0 is retained in both recurrences and the integral power compositor. n=0 denotes
A_(E,1), and j=n is included in the quotient squares. All nonadjacent quotients
are included. Q can be unbounded, and the zero complex and zero object are allowed.
An empty X has no such k-point, precisely as in the source. Nonminimal periods
are allowed by the arbitrary Point bundle. Ramified E is allowed; the existing
annihilator theorem does not assert a false ramification-independent valuation.
No reduction is assumed perfect, of finite Tor amplitude or termwise bounded.
All universes and variables are explicit; no auto-bound implicit variables occur.
The site keeps object universe u+1 and morphism universe u; only the coefficient
ULift and canonical change of localization coordinate the two point targets.

Searches: `msearch.py leanfinder` with the strict quotient/Frobenius transport
statement returned eight unrelated affine-limit or Frobenius-ring declarations;
none states the result. `msearch.py loogle` on qualified NatTrans.ext and
Functor.map_comp gave no exact match (an additional unqualified query reported an
unknown identifier). `msearch.py leansearch` on equality of strict transformations
returned `CategoryTheory.NatTrans.ext` and `ext_iff`, useful for the elementary
strict-equality step but not the local realization theorem. `msearch.py grep`
for `strictRecipe|strictTower|FrobeniusTransport` found no Mathlib match. Direct
rg of Mathlib, WeilConjectures and lean/Sheaf found no declaration for this node.
The project's `LocalFrobeniusTransportNormalization` is the downstream theorem:
its node uses this item in its proof, and its helpers are restricted to separately
supplied finite-subfield points. It is not imported, avoiding that proof cycle.
The existing sandbox draft was checked and revised: finiteA now spells out the
successive finite insertions, the recorded annihilator is reused, and the actual
quotient ring map is reused. The repair adds six existing:true definition nodes owning these APIs; no Lean
notion is duplicated and no dependency module is modified.

Validation: the prescribed scompile.py compiles this single module against the
current published live library in module mode; delivery preflight and its compile
are run with deliver2.py. Only the expected sorry warnings are permitted.

## Second reading by Q04

A second pass by this worker (no other agent was started, as required by the
assignment) read the accepted node alongside the complete module and checked the
clauses above. It found and repaired the draft's direct-power presentation of A:
`finiteSuccessiveInsertion` now explicitly uses successive one-step maps and the
specified compositor at every step. It also removed a redundant annihilator
assertion in favor of the existing dependency declaration and reused the owning
quotient-ring map. The arbitrary-point, positive-period, actual-transition,
nonflat-derived-quotient, independent-integral-transport and all-rational-morphism
clauses are present. Endpoint changes are canonical presentation isomorphisms;
none replaces an actual integral point map by a family of reductionwise maps.
No mathematical statement correction or disputed statement remains.


## New nodes

The H2 repair records unchanged existing declarations, with no new Lean files.
All six nodes use the item's source place (the normalization construction supporting
the final transport sentence). Their records contain actual LeanSearch, LeanFinder
and grep output; direct DAG/source search found the APIs only under theorem-node
records, with no definition owner. Thus these records supply ownership, not duplicate
constructions. Each paragraph specifies the declarations listed in its lean record.

- `def-trf-section-localization-coordinate-transport`: owns
  `sfSectionsCoefficientLift` and `sfSectionsCoefficientLiftIso` in
  `Sheaf.Paper.IntegralSectionsPerfectReduction`; these are the canonical uniqueness
  of localization functor and its exact-section comparison, not an invocation of
  the perfect-reduction theorem.
- `def-trf-semilinear-raw-localization-extension`: owns
  `ScalarLocalization.IsSemilinear`, `.coefficientMap` and `.extension` in
  `Sheaf.CategoryTheory.SemilinearScalarLocalization`. The definition is fixed on
  every pure tensor by the actual induced scalar ring map.
- `def-trf-point-power-restriction-data`: owns `pointFrobeniusAut` and
  `pointPowerFiniteSigma` in `Sheaf.TraceFormula.PointTransportComposition`.
  The latter is uniquely fixed by restriction on every degree and section.
- `def-trf-point-representative-coordinate-data`: owns `sectionTower`,
  `representative`, `completedSections`, `moduleQ`, `sections`, `derivedSections`
  and `moduleHasDerived` in `Sheaf.Paper.PointPullbackRepresentativeDiagram`.
  It retains actual transitions and the two-coordinate normalized whole-Roos map.
- `def-trf-integral-point-power-compositor`: owns
  `IntegralPointTransportTower.integralCompositor` in
  `Sheaf.Paper.IntegralPointTransportTowerPowers`, including its zero case and the
  specified comparison family B; this is the explicit c^E construction.
- `def-trf-point-finite-reduction-tensor-data`: owns
  `pointFiniteReductionComplexTensor`, `pointFiniteReductionModuleCounit` and
  `pointFiniteReductionTensorGenerator` in
  `Sheaf.Paper.PointSectionsFiniteReductionData`. It uses actual quotient rings,
  ordinary mixed total tensor, and the recorded derived computation counit.

The corresponding six theorem nodes were removed from the saved packet's added
statement-dependency list as requested. `lem-trf-scheme-galois-comparison-normal-form`
and `lem-trf-frobenius-coefficient-reduction-coherence` remain: their proofs specify
the comparisons used. `lem-pod-point-sections-derived-reduction-data` remains a
reused definition node. Original proof dependencies are retained as proof imports.

## Repair reading by Q04

H2: checked all six new records against the full signatures and docstrings in their
existing modules. They own precisely the used data and cite the constructions they
are built from. No theorem assertion was used as a substitute for plain data.

H3: `successiveRational` now starts with identity and composes the recorded
`frobeniusPointTransportRational` at each iterated point pullback, rather than
mapping the integral factors under raw localization. `rationalSectionMap` spells
out tensor with E, the specified coefficient lift and size descent, and the recorded
`pointRationalFibreObjIso` on both endpoints. `rationalPointHom_existsUnique`
characterizes the coordinate comparison on EVERY pure tensor as the actual scalar
field image times that tensor/size-descent map. Its additive equivalence is canonical:
integral point sections are bounded with finitely generated cohomology over a DVR,
so their Hom commutes with flat localization. This is a property of integral point
sections; it imposes no perfectness on any finite reduction. `rationalAInFibre`
composes the successive rational components with the actual tensor image of the
power and return compositors. `rationalA` is its inverse image under that normalized
coordinate comparison. Thus the Laws equality now relates independently specified
integral and rational point transports; map_comp alone does not establish it.

Rechecked m=1 and the recurrence's zero stage, the equal-exponent and all nonadjacent
quotients, nonminimal periods, the zero complex, ramified coefficient fields, and
arbitrary rational Hom tensors and sums. The fixed-point and return-square orders,
strict component recipes, counit IsIso clauses, whole-system realization, conditional
equality and both naturality clauses retain their accepted statements. No statement
correction or added Tor/perfectness hypothesis is made. The helper theorem's
natural-language proof is included in its docstring and it is listed among this
node's declarations, as a coordinate part of the rationalization clause.

## Compile repair and final self-check by Q04

The first retry dry run exposed saved-packet interface errors. `levelIdentity_existsUnique`
now writes identity on underlying sections as HEq, retaining exactly the same
normalization across the two coefficient-action presentations. The ordinary pullback
and section definitions remain transparent where their canonical comparisons are
elaborated and opaque during the recursive finite recipes. `rationalSectionMap`
explicitly selects the small Grothendieck module localizations on both sides of
exact scalar extension. The pure-tensor formula is written as `a • Q.map f`,
which is exactly a tensor f and uses the localization category's own scalar action,
avoiding competing module instances. All helpers, including the rational coordinate
comparison and its uniqueness theorem, are now listed in lean.declarations.

The second self-reading retained the six H2 definition owners and checked the H3
recurrence directly against `frobeniusPointTransportRational` and its tensor/size-descent
definition. The main source statement, proof, and proof dependencies are unchanged.
The only node changes are the Lean binding and added definition/interface owners.
The minimum period, diagonal quotients, nonadjacent quotients, zero objects, and all
raw rational Hom tensors and sums remain covered without finite-reduction perfectness.

Profiling found that the specialized `Point` structure caused costly kernel expansion
of the geometric fibre when generating its recursor. `ReturnPoint` now bundles
the same four fields over explicit category objects and endomorphisms; `Point` specializes it to the exact
fibre, its structure map, the point Frobenius, the Galois Frobenius and Phi^m.
Its fields and equations are unchanged, including the order of the return square.
The six existing-data probes also include `ScalarLocalization.coefficientMap`,
which fixes the scalar identification used by the rational Hom comparison.

The final self-check records 53 public declarations, matches the main theorem
signature verbatim, verifies the eight sorry-only theorem bodies and all source
docstrings, and finds no overlength line or remaining profiler/check command.
`coefficientComparison` now has an explicit isomorphism signature, keeping the
canonical tensor-generator characterization while avoiding repeated expansion
of that predicate during the derived quotient compatibility statement.
