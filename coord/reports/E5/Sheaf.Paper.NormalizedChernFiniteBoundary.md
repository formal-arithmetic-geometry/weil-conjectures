## What changed

Replaced the assigned theorem's original sorry with a complete reduction to the
proved integral normalization and one strictly smaller scalar/evaluation
obligation. Its signature, original public import, and blueprint unit route are
preserved. All other delivered modules and nodes are new; no other existing
module or node is changed.

The integral proof first works in arbitrary categories. Right adjunction
naturality and cancellation move the normalized integer generator across the
adjunction; left naturality moves the given integer-to-shifted-units arrow
outside its adjunct. The target normalization identifies the remaining adjunct
with the positive Kummer boundary, including the prescribed shift-addition map.
Specialization uses the actual reduction model and only the first two fields of
the supplied normalization record.

The remaining scalarFiniteBoundary concerns scalar extension and finite
evaluation of an arbitrary integral coefficient-linear arrow, under scalar-unit
normalization alone. It uses neither lineBundleClass nor its Kummer boundary
normalization. Its docstring and node give the K-flat-resolution, adjunction,
section and endpoint-transport argument. The assembly applies that scalar
comparison to firstChernR and substitutes the proved integral equality.

The actual underlying-arrow and positive-boundary composites are constructed
before specializing their categories. The named actual Kummer complex shares
its canonical zero witness and proved exactness. Named predicates are exactly
the concrete equality or HEq formulas, permitting their category endpoints to
be checked once and reused by later proofs. These are constructions and proved
comparisons, rather than additional obligations.

Verification: lcompile.py --all compiled all 21 sandbox modules successfully.
Every file was below 60 seconds; the slowest, TowerFiniteChernAssembly, took
53.8 seconds. Debug profiling options and temporary probe modules are removed.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.SpTowerClasses.finiteChernNormalization_of_normalized
(node lem-sfb-normalized-chern-finite-boundary) by a complete reduction.
The other proved public declarations are:

- towerKummerShortExact
- forgetEvaluatedArrow_firstChernR
- finiteChernNormalization_of_arrowComparisons
- integralArrow_of_normalized
- integralEvaluation_of_normalization
- towerKummerBoundary_eq_raw
- towerKummerBoundary_composite
- towerKummerBoundary_evaluation
- towerKummerComposite_eq_raw

The three private helpers normalizedExtension_arrow,
normalizedDerivedExtension_arrow and finiteBoundaryEquality_transport are also
proved. All definitions construct actual arrows, complexes or explicit
comparison predicates. No definition contains sorry.

Added exactly one hole:
AlgebraicGeometry.ProEtale.SpTowerClasses.scalarFiniteBoundary,
node lem-sfb-tower-scalar-finite-boundary, in
lean/Sheaf/Paper/TowerScalarFiniteBoundary.lean, with proof exactly by sorry.
There is no sorry in the assigned module.

This is a decomposition: one upper hole closed and one strictly smaller
obligation added, net zero holes removed. It is not counted as a complete proof
of the original obligation. The remaining statement was checked conceptually
on the zero arrow and the empty scheme. Its formulas require no nonzero finite
coefficient ring and no flatness assumption on the root module.

## No longer needed

Removed the unused public import Sheaf.Paper.TowerClassFinite from the new
TowerIntegralBoundaryData module; the finite-evaluation module imports it
directly. No original imports removed and no global modules or nodes pruned. The original
reduction, Chern, finite and diagonal definitions remain needed. The original
proof dependencies def-sp-tower-class-reduction,
def-coef-semilinear-system-models and def-sp-tower-class-diagonal are accounted
for in the lower nodes; this is not global pruning.

## Where the brief, the DAG or earlier work was wrong

The assigned source was temporarily absent because of its rework quarantine.
Its archive and Lean attachment were retained; the shared source has since been
restored. No statement dispute, target change or unit-route change was needed.

The main implementation difficulty was repeated conversion of the concrete
category witnesses. The Kummer field's functor-category zero presentation and
the abelian structure's zero presentation are definitionally equal but costly
to compare repeatedly. The named actual complex and exactness proof share the
canonical presentation. A local preference for CategoryStruct.toQuiver in the
new boundary module avoids another equivalent quiver presentation. Generic
arrow constructors and named exact comparison predicates avoid repeated
expansion in later proofs. No existing category instance, definition or data
record is changed.

## New nodes

`def-sfb-canonical-kummer-complex`, `lean/Sheaf/Paper/TowerCanonicalKummerComplex.lean`: For Kummer data k [def-sp-tower-class-systems], towerKummerComplex is the actual three-term complex of roots, power-transition units and constant units, with the given inclusion and power maps and their zero-composite proof. It uses the zero-morphism witness induced by the named abelian-category structure, so derived-category constructions share that witness. No object or morphism is changed.

`def-sfb-integral-boundary-normalization`, `lean/Sheaf/Paper/TowerIntegralBoundaryData.lean`: For variable coefficient towers R,A and their ring-object map φ, ChernData c [def-sp-tower-class-chern], and f : single(integers) → single(units)[1], IntegralBoundaryNormalization l R A φ c f is exactly Fact of the equality underlyingChernArrow l c (c.unitIso.inv ≫ c.reduction.model.derived.map f ≫ c.rootIso.hom) [def-sfb-tower-underlying-arrow] = f ≫ towerKummerBoundary l c.kummer [def-sfb-positive-kummer-boundary]. The standard Fact.out field is precisely this equality; no additional condition or chosen object is supplied.

`def-sfb-kummer-boundary-evaluation-equality`, `lean/Sheaf/Paper/TowerKummerEvaluationData.lean`: For Kummer data k, an arrow f : single(integers) → single(units)[1], and n : ℕ, KummerBoundaryEvaluationEquality l k f n is precisely HEq of mapSingleArrow (abEvaluation T n) 2 (f ≫ towerKummerBoundary l k [def-sfb-positive-kummer-boundary]) and mapSingleArrow (abEvaluation T n) 2 (kummerComposite (ShortComplex.mk k.inclusion k.power k.zero) k.exact f) [def-sp-tower-class-finite]. The exact evaluation includes its existing single and shift comparisons.

`def-sfb-kummer-boundary-raw-equality`, `lean/Sheaf/Paper/TowerKummerBoundaryRawData.lean`: For Kummer data k and an arrow f : single(integers) → single(units)[1], KummerBoundaryRawEquality l k f is precisely f ≫ towerKummerBoundary l k [def-sfb-positive-kummer-boundary] = kummerComposite [def-sp-tower-class-finite] (ShortComplex.mk k.inclusion k.power k.zero) k.exact f. This is the actual equality, without added hypotheses or existential witnesses.

`def-sfb-positive-exact-boundary`, `lean/Sheaf/Paper/PositiveExactBoundary.lean`: In an abelian category C with its derived category, for any short complex s and proof hs of short exactness, positiveExactBoundary s hs is the connecting arrow hs.singleδ shifted once, followed by the inverse shift-addition comparison from shift one then shift one to shift two. Its source is single(s.X3)[1] and target single(s.X1)[2].

`def-sfb-positive-kummer-boundary`, `lean/Sheaf/Paper/TowerPositiveKummerBoundary.lean`: For a Kummer sequence k in abelian towers [def-sp-tower-class-systems], towerKummerBoundary is its actual connecting morphism shifted once, followed by the canonical shift-addition inverse from shifts 1 and 1 to shift 2. Its source is the single units tower shifted by 1 and its target is the single roots tower shifted by 2.

`def-sfb-scalar-chern-arrow`, `lean/Sheaf/Paper/TowerScalarChernArrow.lean`: For Chern data c [def-sp-tower-class-chern] and any integral arrow f from the unit of Rrings in degree zero to c.rootModule shifted by two, scalarChernArrow is the actual composite of c.scalarUnit.inv, c.scalar.T.map f, the canonical scalar shift comparison, and lineComparison shifted by two. Its explicit source is unit T (Arings l E T) and its explicit target is line l E c shifted by two. This copies the existing firstChern construction with its integral argument left arbitrary; it is fully constructed, with no chosen data or hole.

`def-sfb-scalar-finite-boundary`, `lean/Sheaf/Paper/TowerScalarFiniteBoundaryData.lean`: For Chern data c and an arbitrary integral arrow f from the Rrings unit to c.rootModule shifted by two, and any level n, ScalarFiniteBoundary is the actual finiteBoundaryEquality [def-sp-tower-class-finite] of scalarChernArrow [def-sfb-scalar-chern-arrow] after evaluation, target transport by lineEvaluation and forgetting scalars. The source map is finiteQuotient, the target map is finiteRootMap, and the integral comparison arrow is finite evaluation of underlyingChernArrow [def-sfb-tower-underlying-arrow] of f, with integerGenerator and rootForget at its endpoints. It assumes no integral Kummer normalization and is a fully constructed proposition, with no chosen object or hole. The standard Fact wrapper stores precisely this equality in its out field; no additional condition or data is supplied.

`def-sfb-tower-underlying-arrow`, `lean/Sheaf/Paper/TowerClassArrowTransport.lean`: For ChernData c [def-sp-tower-class-chern] with variable ring towers R and A and their system-ring map, underlyingChernArrow takes an integral coefficient-linear arrow f:unit R→rootModule[2] to the actual abelian-tower arrow from integers to roots[2]. It is the single map of integerGenerator, followed by mapSingleArrow for the recorded exact forgetting functor, followed by the shifted single map of rootForget. Its endpoint category and derived witnesses are explicitly those of Ab T [def-sp-tower-class-systems]. No source, target or scalar normalization is assumed.

`def-sfb-underlying-single-arrow`, `lean/Sheaf/Paper/UnderlyingSingleArrow.lean`: Given an exact additive functor G from an abelian category C to an abelian category D, both with their derived categories, q : I → G(X), y : G(Y) → J and f : single(X) → single(Y)[2], underlyingSingleArrow G q y f is single(q) followed by mapSingleArrow G 2 f [def-sp-tower-class-reduction] and the shift by two of single(y).

`lem-sfb-canonical-kummer-exact`, `lean/Sheaf/Paper/TowerCanonicalKummerExact.lean`: For every Kummer datum k [def-sp-tower-class-systems], its actual named complex towerKummerComplex [def-sfb-canonical-kummer-complex] is short exact. The assertion has no additional hypothesis.

`lem-sfb-chern-data-integral-normalization`, `lean/Sheaf/Paper/TowerIntegralChernNormalization.lean`: For ring-sheaf towers R and A, their system-ring map φ, ChernData c [def-sp-tower-class-chern], and a coefficient-unit map q, assume the existing ChernData.Normalized record for c and q. For every integer-to-shifted-units arrow f, the transported conjugated arrow [def-sfb-tower-underlying-arrow] satisfies IntegralBoundaryNormalization [def-sfb-integral-boundary-normalization], using the actual named positive Kummer boundary [def-sfb-positive-kummer-boundary]. Only the first two fields of the normalization record enter the proof; the scalar field is unused.

`lem-sfb-chern-evaluation-comparison`, `lean/Sheaf/Paper/TowerChernEvaluationComparison.lean`: For Chern data c [def-sp-tower-class-chern], each line bundle L and level n, applying forgetEvaluatedArrow [def-sp-tower-class-finite] to scalarChernArrow [def-sfb-scalar-chern-arrow] of firstChernR gives exactly mapSingleArrow of finiteForget applied to evaluatedChern. This is recorded as HEq, so the constructed endpoint types are transported explicitly. No normalization hypothesis is needed: it is an identity of the constructions.

`lem-sfb-chern-finite-assembly`, `lean/Sheaf/Paper/TowerFiniteChernAssembly.lean`: For Chern data c [def-sp-tower-class-chern], assume IntegralBoundaryNormalization [def-sfb-integral-boundary-normalization] for every lineBundleClass and ScalarFiniteBoundary [def-sfb-scalar-finite-boundary] for every integral arrow and finite level. Then c satisfies the original FiniteChernNormalization [def-sp-tower-class-finite]. This is the fully proved substitution of the integral Kummer equality into scalar/finite compatibility.

`lem-sfb-integral-evaluation-comparison`, `lean/Sheaf/Paper/TowerIntegralEvaluationComparison.lean`: Let R and A be ring-sheaf towers, φ their system-ring map, and c ChernData [def-sp-tower-class-chern]. For any integer-to-shifted-units arrow f and level n, IntegralBoundaryNormalization [def-sfb-integral-boundary-normalization] implies that exact evaluation [def-sp-tower-class-finite] of the underlying conjugated integral arrow [def-sfb-tower-underlying-arrow] is HEq to exact evaluation of the positive Kummer composite with f. This is the image of the integral morphism equality under mapSingleArrow for abEvaluation; R, A and φ remain variables. The positive boundary is the actual arrow towerKummerBoundary [def-sfb-positive-kummer-boundary], with its canonical endpoints.

`lem-sfb-kummer-boundary-raw-comparison`, `lean/Sheaf/Paper/TowerKummerBoundaryRawComparison.lean`: For Kummer data k and any integer-to-shifted-units arrow f, composition f ≫ towerKummerBoundary l k [def-sfb-positive-kummer-boundary] equals the original kummerComposite [def-sp-tower-class-finite] on ShortComplex.mk k.inclusion k.power k.zero and k.exact.

`lem-sfb-kummer-composite-comparison`, `lean/Sheaf/Paper/TowerKummerCompositeComparison.lean`: For a Kummer sequence k [def-sp-tower-class-systems] and integer-to-shifted-units arrow f, f followed by towerKummerBoundary [def-sfb-positive-kummer-boundary] equals kummerComposite [def-sp-tower-class-finite] for the actual named complex towerKummerComplex [def-sfb-canonical-kummer-complex] and its proved short exactness towerKummerShortExact [lem-sfb-canonical-kummer-exact]. This is equality before finite evaluation.

`lem-sfb-kummer-evaluation-comparison`, `lean/Sheaf/Paper/TowerKummerEvaluationComparison.lean`: For any Kummer sequence k [def-sp-tower-class-systems], integer-to-shifted-units arrow f and level n, exact evaluation of f followed by towerKummerBoundary [def-sfb-positive-kummer-boundary] is HEq to exact evaluation of kummerComposite for k and f [def-sp-tower-class-finite]. No coefficient tower or scalar data occur.

`lem-sfb-kummer-raw-composite-comparison`, `lean/Sheaf/Paper/TowerKummerRawComparison.lean`: For Kummer data k [def-sp-tower-class-systems] and any integer-to-shifted-units arrow f, kummerComposite [def-sp-tower-class-finite] using towerKummerComplex [def-sfb-canonical-kummer-complex] and towerKummerShortExact [lem-sfb-canonical-kummer-exact] equals kummerComposite using the original literal complex ShortComplex.mk k.inclusion k.power k.zero and k.exact.

`lem-sfb-tower-scalar-finite-boundary`, `lean/Sheaf/Paper/TowerScalarFiniteBoundary.lean`: Let $\ell$ be prime, let $E/\mathbf Q_\ell$ be finite, and let $T$ be a scheme. Fix Chern data $c$ [def-sp-tower-class-chern], assuming only its scalar-unit normalization [def-sp-tower-class-reduction]. For any integral coefficient-linear arrow $f:R_T[0]\to c.rootModule[2]$ and level $n\geq0$, scalar-extend $f$ using $c.scalarUnit^{-1}$, the canonical scalar shift comparison, and the universal lineComparison. Evaluate, identify the target by the pure-tensor lineEvaluation [def-sp-tower-class-diagonal], and forget finite scalars. After precomposition with finiteQuotient, this equals finite evaluation of the underlying integral arrow, precomposed with integerGenerator and postcomposed with rootForget, followed by finiteRootMap [def-sp-tower-class-finite]. The equation is finiteBoundaryEquality with its two canonical endpoint transports. No integral source normalization, Kummer target normalization, or line-bundle construction of $f$ is assumed. The underlying integral arrow is the generic endpoint-transport composite [def-sfb-tower-underlying-arrow]. The scalar-extended arrow is the constructed scalarChernArrow [def-sfb-scalar-chern-arrow]. The displayed equality is the constructed proposition ScalarFiniteBoundary [def-sfb-scalar-finite-boundary].

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
