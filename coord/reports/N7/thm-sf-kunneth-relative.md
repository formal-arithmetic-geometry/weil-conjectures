## Worker report

The module `Sheaf.Paper.RelativeKunneth` states `WeilConjectures.relativeKunneth`.
The theorem has a sorry proof and its docstring contains the complete six-step
assembly argument from the node. Its canonical map is real data:
`relativeKunnethIso` composes `R.factors cg ch 0` through `5`, and
`relativeKunnethMap` is that composite's hom. The normalized presentation fixes
all six components by full inclusion to the datum's recorded maps. The theorem
concludes existence of a presentation, then applies to every normalized
presentation. No map is chosen from that existence theorem.

Hypotheses and clauses, read against the unchanged DAG statement:

- `D : FiniteFieldDatum` includes p prime, a positive, the cardinality p^a,
  the finite base field and its algebraic closure. `C : D.CoefficientDatum`
  includes the coefficient prime, its inequality with p and the algebraic closure
  of Q_l. `E`, its field/algebra/finite-dimensional instances, and `n, hn` retain
  the finite extension and positive quotient exponent. The original Padic
  valuation-ring, uniformizer and quotient definitions are reused.
- `S : SixFunctorDatum D C E n hn` is exactly A1--A6. `s : PodCoefficientStage`
  ranges over finite, completed integral, rational and common algebraically closed
  coefficients. `PodCoefficientStage.domain` imposes exactly finite Tor in the
  first two stages and the whole constructible category in the field stages.
- `Q.Y` is B, `Q.X` is X, `Q.Y'` is Y and `Q.X'` is T. All are finite type
  over k by `SixFunctorSpace`. Separatedness of B is the instance on `Q.Y.obj.hom`;
  separatedness of f,g is explicit. The projection separatedness instances are
  consequences of these geometric hypotheses, retained to select the existing
  restricted pullback API. `Q.square` and `relativeProductFibreProductIso` identify
  T with the actual scheme pullback and retain both projections. The compactified
  square and arbitrary cg,ch are presentations of the given compact support,
  not properness assumptions on f or g. Q carries f's compactification and its
  base-changed compactification for v. The final structure map is `Q.f' ≫ Q.g`.
- `relativeProductTerms ... 0` is Rh!(u*K tensor v*L), and term 6 is
  Rf!K tensor Rg!L. The factors are composition in its inverse-paper direction,
  inverse PF_v, inverse exchange tensored with identity and whiskered by Rg!,
  symmetry whiskered by Rg!, inverse PF_g and final symmetry, in that order.
  `projection_eq`, `exchange_eq`, `signedNormalization`, `tensorNormalization`
  and `compositionNormalization` pin these to the existing supplied constructions;
  they are not arbitrary endpoint isomorphisms. The main first conjunct says
  `IsIso ((relativeKunnethMap R cg ch).app (K,L))` for all finite-Tor K,L.
- The next conjunct is the actual bifunctor naturality equation, for arbitrary
  a:K→K' and b:L→L', using the two endpoint expression functors. Both inputs and
  all their morphisms are quantified.
- Finite reduction and scalar extension use the given
  `A : RelativeProductCoefficientData R R'` with `A.RecordedComparison`, whose
  cases pin its primitive functor and maps to identity, finite quotient, ramified
  finite scalar extension with subsequent quotient, integral scalar extension,
  integral reduction, rationalization, finite-field transition and inclusion into
  the algebraic closure. The conclusion is the composite square for that same A:
  A.functor.map(kappa) followed by A.objectIso at 6 equals A.objectIso at 0 followed
  by changed kappa. No existential replacement A or relative-product square is
  assumed. The primitive forward A5 equations in A are part of the supplied
  coefficient comparisons; the statement concludes the square for the six-arrow
  composite including inverses.
- Proper compatibility concludes existence of proper coordinates and applies to
  every such normalized restriction J. `R.ProperNormalization J` asserts actual
  direct projection and exchange normalization, including identity-open finite
  normalization. The additional equation conjugates the composite by the
  recursively built specified proper identifications at terms 0 and 6 and
  identifies it with the composite of the six proper factors. The selector q can
  replace any proper occurrences, including only h. It never requires g proper
  when f is proper.
- Geometric base change quantifies Q', a second presentation R', compactifications,
  and `RelativeKunnethCube`. Its b has arbitrary separated finite-type source base;
  the three actual Cartesian squares are those for f,g,h. The source/target/corner,
  morphism and compactification equations fix every exchange to the same geometric
  cube. Existence of `RelativeKunnethCubeComparisons` is a conclusion, not an added
  hypothesis. The structure only records primitive tensor pullback, pullback
  composition and exchanges: its fields do not contain the final Künneth square.
  `tensorNormalization` pins tensor pullback to
  `relativeKunnethFiniteTensorComparison`, `canonicalIntegralPullbackTensor`,
  `canonicalRationalPullbackTensor` or `canonicalCommonStagePullbackTensor`.
  The composition fields are pinned to the original supplied pullback compositor
  around the commutative square; exchange fields are pinned to
  `relativeProductExchange S s` on the three compactified squares.
  `sourceIso` is exchange_h followed by the external-product monoidal/composition
  comparison. `targetIso` is monoidal pullback followed by exchange_f,exchange_g
  in that order. The theorem states the equality between exactly these two routes.
- For B=Spec k, `RelativeKunnethClosedSquare` has ordinary closed i,j and their
  product r, pinned by both projection equations. `relativeKunnethClosedFormula`
  is unfolded separately at all four stages, keeping the actual coefficient
  universes rather than lifting rational coefficients to a different category.
  Its three terms are the existing `finiteCompactSections`,
  `integralCompactSections`, `rationalCompactSections` or `qbarCompactSections`;
  the integral/rational full subcategories are included into their actual module
  derived categories and Qbar uses `pointFdQbarRealization`. The left inputs are
  the ordinary pullbacks along i,j. The right input is the ordinary pullback along
  r of the actual external tensor. The asserted derived isomorphism has exactly
  tensor(RΓc(Z,i*K),RΓc(W,j*L)) and RΓc(Z×W,r*(K box L)) as endpoints. It is the
  closed-restriction compact formula, never Ri! or cohomology with supports.

Dependencies read and used:

- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`, its four preservation and
  exchange/projection axioms, closed structures and normalized coefficient changes.
- `Sheaf.Paper.ConstructibleProjectionMates`: `compactSupportProjectionComponent`,
  `CompactSupportFiniteProjection.component`, partialTensor and fixed realization.
- `Sheaf.Paper.CtfCoefficientStageSelectors`: all original four-stage selectors.
- The restored normalized factor definitions and theorem interfaces described below.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`, through
  `OrdinaryCompactCohomology`: the four actual compact-sections definitions.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: ordinary support meaning retained
  separately, as required by the node's distinction.
- `DerivedPullbackTensorIso`, `FinitePullbackTensorComparison`,
  `CompletedPullbackTensorComparison`: actual signed braiding and tensor pullback.
- Proof imports `RelativeProductInputDomains`, `PointFibreDerivedTensor`,
  `FiniteTorStability` and Mathlib closed-immersion/proper geometry implement the
  proof steps. The base-change factor sibling has no usable live module; no new
  theorem about its six factors is introduced here. The main proof retains that
  DAG dependency and its docstring explains the same pasting argument.

Edge cases checked: n=1, identity maps and identity coefficient change, zero
complexes, empty schemes and empty fibre products, nonproper f,g, only h proper,
f proper without g proper, arbitrary base change including identity, negative and
odd shifts (the signed symmetry is fixed), integral completed tensor, rational
localization, common finite-field transition and further extension. No nonempty,
flatness, extra amplitude bound or equality of site/coefficient universes is added.
The closed formula is typed at each existing coefficient-complex universe.

Searches: msearch LeanFinder for relative Künneth compact support and for normalized
finite-Tor six-factor restrictions returned condensed tensor/projectivity and
quasi-separated-space lemmas, not this statement. Loogle on IsIso/Functor.map_isIso
rejected an unknown identifier; it was not treated as a negative mathematical
result. Mathlib CategoryTheory grep for Kunneth/externalProduct/relativeProduct
found only generic external products; grep for RelativeProductPresentation,
relativeProductFactors and relativeProductTerms found zero. LeanSearch for relative
Künneth compatibility and the expression-chain comparisons returned unrelated
linear-map/product and condensed lemmas. Project rg in both WeilConjectures and
Sheaf found the finite-only upstream Etale relativeKunnethIso and its naturality,
which were read; they omit the integral/rational/common stages and all required
compatibilities. The exact item-id grep in WeilConjectures did not find a full
match. DAG and blueprint searches for relative product found the current theorem,
coherence and kv-map nodes and the stale factor-module record, not a definition
owner for the normalized construction. Exact logged outputs for the new definition
are included in its mathlib_searches.

Validation: all three delivered modules compiled through scompile against the live
published build. Auto-bound implicits are disabled. The final preflight and push
are run through deliver2. The main theorem and three restored dependency theorems
have sorry-only proofs with natural-language proof docstrings. The construction
module has no sorry. No local source-library or git mutation was performed.

## New nodes

`def-sf-relative-product-factors` owns the normalized operation-expression chain,
finite-Tor presentation, canonical factors, primitive coefficient data, proper
replacement and recorded-comparison predicates. These definitions were previously
owned only by the now-absent theorem module. They were recovered from immutable
reviewed source 9b9a43ec1 and extracted without changing their data. The module
replaces the old theorem-owned selector import with the newly landed owning
selector module; the signed-braiding import is explicit. The new node introduces
no alternative tensor or map and proves no existence. Searches and provenance are
in its required fields. The main item gains this definition dependency only.

## Dependency modules

`lem-sf-relative-product-coefficient-factor-squares`: its recorded module is absent
from the local read clone, the live source server and the published object build.
A module-mode probe failed and the server confirmed the missing object. The
reviewed implementation remains in the shared clone's immutable object store;
it was read without any git command or clone mutation. The three theorem
interfaces and their proof docstrings are restored unchanged; their construction
definitions move unchanged into the owning definition module above. The dependency
JSON changes only lean, with a note describing the repair. All three modules then
compile cleanly together. No downstream theorem is used to construct its own map.

Final normalization check: the finite monoidal-pullback field is conjugated by
`relativeProductFiniteTensorIso`, `S.finitePullback`, the unique unit-normalized
`pullbackTensorFiniteRealization`, and `proEtaleCanonicalTensorComparison` on the
datum's actual K-flat tensor models. This avoids requiring heterogeneous equality
between different closed tensor presentations. Both operation-coordinate endpoint
identifications are included. The finite comparison is real data and compiles.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
