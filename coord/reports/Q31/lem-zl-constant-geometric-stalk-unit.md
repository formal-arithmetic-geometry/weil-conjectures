## Worker report

The module `Sheaf.Paper.ConstantGeometricStalkUnit` states the finite, completed
integral and rational constant-unit stalk calculation. All theorem proofs are
`sorry`; definitions contain actual adjunction, cochain, localization, scalar
extension or uniquely normalized comparison data. The stalk declarations belong to
`lem-zl-constant-geometric-stalk-unit`; the new definition module belongs to
`def-zl-finite-regular-coefficient-comparisons`. Both records list their declarations.
The node statement is unchanged. The new definition node and the already recorded
inverse-image comparison definition are added to `stmt_deps`. There are no dependency
record repairs.

Hypotheses and conventions:

- `D : FiniteFieldDatum.{u}` supplies p, a, q, the finite base field and its
  algebraic closure, with all their specified algebra structures.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` express the coefficient convention.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` are the finite coefficient extension. The result
  uses only this extension, so no choice of its embedding in the chosen algebraic
  closure is needed. The integers, uniformizer and quotients are precisely
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer` and
  `coefficientExtensionRing`, rather than new coefficient constructions.
- `Y₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType Y₀.hom]` and
  `[QuasiCompact Y₀.hom]` mean finite type exactly as the dependency convention.
  `D.geometricFiber Y₀` is Y and `Spec (.of D.k)` is s. No separatedness,
  smoothness, reducedness, connectedness or rational-point hypothesis is imposed.
- `m : ℕ` denotes exponent m+1, so every positive finite coefficient level occurs.
- `n : ℕ`, `hn : 1 ≤ n` denote every positive return exponent, using `n-1`
  with `localPositivePower`, whose argument r denotes exponent r+1.
- `x : D.extensionPoints Y₀ n hn` is an extension-valued point over k₀.
  `ι : D.extensionSubfield n hn →+* D.k` with
  `hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k`
  ranges over EVERY base-field embedding of that finite extension into k.
  This includes but does not restrict to its chosen subfield inclusion.

Clause-by-clause correspondence:

1. The actual finite regular sheaf is `finiteConstantCoefficientObject`; its
   pullback unit multiplication is `finiteUnitHom`, the transpose of section one
   under `sfIntrinsicConstantModuleAdjunction`. `finiteUnitHom_isIso` postpones
   only the inverse identities. `finiteUnit` uses the exact single comparison.
   `finiteUnit_canonicalWeil` identifies this multiplication with the specified
   c_m lambda_m: composing with kappa (the inverse of lambda) gives c_m already
   on the degree-zero regular cochain. Localization gives the same derived map.
2. The integral regular object is `integralConstantCoefficientObject`.
   `integralChainUnit_existsUnique` prescribes its full strict Roos map by the
   actual finite adjunction generators AND zero shifted component.
   `integralChainUnit` chooses the uniquely specified map; its data are not
   chosen from mere nonemptiness. `integralChainUnit_isIso` states the
   quasi-isomorphism. `integralUnit` uses its inverse with the published
   good-representative comparison. `integralUnit_canonicalWeil` fixes agreement
   with `constantWeilIntegralTheta` when the map is an isomorphism.
3. `embeddingPoint` is the actual fiber-product lift of `Spec.map ι ≫ x.left`.
   Its only compatibility proof is separately named `embeddingPoint_compatible`.
   `embeddingPoint_return` is the semilinear return equality of scheme maps,
   for every allowed embedding, not an assumed return or equality of points.
4. `finiteCanonicalPullbackComposition` is the prescribed ringed-site compositor,
   transported to intrinsic coordinates by the uniquely unit-preserving
   `openSquareDerivedPullbackModel`.
   `finiteWeilIterate` iterates the canonical finite unit maps with it.
   `finiteTransportIterate` iterates the ACTUAL `frobeniusPointTransportFinite`.
   `finiteOperator` composes transport, the return comparison and the pulled
   iterated Weil map, in that order. Its return comparison includes the actual
   compositor, the equality of scheme maps, and the second compositor.
5. `integralStalk`, `integralWeilIterate`, `integralTransportIterate` and
   `integralOperator` use the published full constructible integral category,
   `constantWeilConstructibleIntegralTheta`, the specified chosen
   `integralPullbackComposition`, and `frobeniusPointTransportIntegral`.
   The choice of compositor here is the one already prescribed by the
   dependency, not a new existential comparison.
6. `finiteSection` and `integralSection` are the actual constant-section maps
   on coefficients. `section_isIso` states their invertibility; the integral
   clause uses the completed ring sheaf and completeness, not the ordinary
   constant integral sheaf. `finiteSectionsUnit` and `integralSectionsUnit`
   pass through the exact single-complex comparison. `finiteStalkUnit` and
   `integralStalkUnit` compose pullback-unit and section identifications to
   give the two displayed derived stalk isomorphisms with A_m[0] and O_E[0].
   Their `ULift.{u+1}` coefficients are the dependency's exact section universe;
   no equality of site and coefficient universes is added.
7. `finiteOperator_unit` and `integralOperator_unit` assert T ≫ e.hom = e.hom
   for these actual operators and these fixed isomorphisms. Since e is an
   isomorphism, this is precisely e^(-1) T e = identity (and T = identity).
   These are equalities in the entire derived category, not just H^0 or
   independently observed equalities at finite reductions.
8. Rational coefficients are the published `constantWeilRationalComplex` and
   the actual `localFrobeniusOperator` with `embeddingPoint_return`.
   `rationalRegular` is tensor-unit multiplication O_E tensor E → E.
   `rationalFibreComparison` retains `localPullbackObjectIso`, the published
   rational-fiber object comparison, and the size-descent counit.
   `rationalStalkUnitLarge` is integralStalkUnit tensor E followed by this
   regular multiplication. `rationalStalkUnit_existsUnique` specifies the
   small rational isomorphism uniquely by its lifted normalization square;
   `rationalStalkUnit` selects that uniquely prescribed isomorphism with E[0].
   `rationalOperator_unit` states that the ACTUAL rational local operator is
   identity in these coordinates.
9. Finite reductions are expressed in `finiteUnit_reduction` on every
   adjunction generator and every site test object, using the actual
   `integralCoefficientSheafTransition`. This determines the full sheafified
   tensor square by linearity, and exact single/point sections give the
   derived geometric-stalk square. It is not a transition defined by
   conjugating a coefficient quotient through the isomorphisms being proved.
10. `integralUnit_projection` gives every ACTUAL Roos first coordinate and
    product projection of the integral unit on every regular section, with
    scalar action by the actual limit projection. The zero shifted component
    was fixed in `integralChainUnit_existsUnique`. Thus it specifies all
    completed-unit projections before localization. `section_reductions`
    identifies the finite section reductions and the completed section
    projections with the literal coefficient quotient homomorphisms. Combined
    with the two unit normalizations these are precisely the stalk-unit
    reduction/projection squares. Since the local operators equal identities,
    the same squares commute with their operator equalities.
11. `rationalStalkUnit_existsUnique` is the explicit rationalization square for
    the identifications; `rationalOperator_scalar` is the explicit square for
    the actual operators, under `rationalFibreComparison`. It tensors the
    integral operator with E, never a torsion finite quotient with E.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`,
  `extensionSubfield`, `extensionEmbedding`, `extensionPoints`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the actual finite
  coefficient rings, with `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.ConstantWeilStructure`: `constantWeilIntegralComplex`,
  `constantWeilIntegralGood`, `constantWeilReducedUnitSection`, the strict
  tower and Roos endomorphism, `constantWeilIntegralTheta`,
  `constantWeilIntegralObject`, `constantWeilConstructibleIntegralTheta`,
  `constantWeilRationalObject`, `constantWeilRationalComplex`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `D.geometricFrobenius`.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`, the actual
  finite/integral transports, and `frobeniusPointPrimeInvertible`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`,
  `localPullbackObjectIso`, `localPointComplex`, `localFrobeniusOperator`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFibreIntegralAmbient`,
  `pointFibreModuleLift`, `pointFibreSizeLift`, `pointFibreRationalLarge`,
  `pointRationalFibreObjIso`, and the published section exactness instances.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`,
  `constructibleIntegralPullback`, `rationalDerivedPullback`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: completed integral
  sheaves and the actual constant-to-completion map. The underlying sections
  and sheaf quotients come from its published coefficient-germ dependency.
- `Sheaf.Paper.SfRationalizationKaroubi`: raw rational localization.
- `Sheaf.Paper.IsomorphismDerivedPullback`: recorded isomorphism inverse-image
  and completed coefficient interfaces, also imported directly as required.
- `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison`:
  `inverseImageFiniteIntrinsicPullbackComparison`, the normalized comparison
  between the coefficient-sized tensor pullback and intrinsic presentation.
- `Sheaf.Paper.FiniteRegularCoefficientComparisons` (new definition node):
  `finiteRegularCoefficientComplex`, `finiteRegularKappa`, `finiteRegularLambda`,
  `finiteRegularComparison`, `finiteCanonicalPullbackComposition`. The first four
  are transparent aliases of the existing `canonicalCoefficient…` declarations;
  the final definition uses the exact
  `integralFiniteCanonicalPullbackComposition` from
  `Sheaf.Paper.IntegralFinitePullbackComposition`, conjugated by
  `openSquareDerivedPullbackModel` from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`.
  The reduction theorem is retained as a proof dependency, rather than a
  statement dependency for its incidental plain definitions.
- Mathlib: exact-functor derived/single comparisons, `DerivedCategory.Q`,
  `CochainComplex.mappingCocone`, `Pi.π`, `limit.π`, tensor-unit multiplication,
  full-subcategory isomorphisms and ring/module categories.

The plain imports retain all recorded proof-dependency modules, including the
finite-section theorem, constant-ring coherence, pullback composition, normalized
integral comparison realization, whole-system transport powers, completed scalar
comparison, and `spectralNorm.completeSpace`. The source expansion's eight proof
steps are reflected in the theorem docstrings, with the integral reconstruction
explicitly on whole strict systems rather than detection from unrelated reductions.

Edge cases checked: empty Y has no x but arbitrary-point unit constructions remain
valid; n=1 uses argument zero of localPositivePower; m=0 is exponent one and is
included in every finite formula; degree of x may properly divide n; arbitrary
base-field embeddings are retained; ramified E uses the actual chosen DVR
uniformizer quotients; nonreduced and nonseparated finite-type Y₀ are allowed.
Integral coordinates use completion even though the ordinary constant sheaf is not
itself asserted complete. Rational coordinates use E[0] in the small published
category, with its explicit larger section-universe comparison.

Searches for an existing statement:

- `msearch.py ... leanfinder "The geometric stalk of a constant coefficient sheaf
  is the coefficient ring, and the local Frobenius acts as the identity"`:
  eight unrelated ordinary scheme/Zariski stalk hits, including
  `ModuleCat.Tilde.stalkIso`; no geometric Weil operator normalization.
- `msearch.py ... loogle "CategoryTheory.Sheaf, CategoryTheory.Limits.limit"`:
  two coherent/sequential-limit hits; neither states this calculation.
- `msearch.py ... grep "constant.*(stalk|Frobenius)|stalk.*constant"`:
  nine rank-at-stalk and ordinary constant-stalk hits; none includes the actual
  finite/integral/rational Weil transports and comparison squares.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for constant stalk,
  constant Weil, normalized unit and the item id: the existing constant
  coefficient, pro-etale stalk and Weil-structure modules supply the objects,
  but no declaration states this local operator normalization. The nearby
  normalized-coefficient-unit-realization node is a different realization
  obligation and has no usable declaration of this statement.
- The requested source-item-id search in `lean/WeilConjectures` found no
  declaration already owning this item.

No statement dispute or source correction was needed.

## Second reading by Q31

Re-read the node and the complete module clause by clause, with particular checks
of the return direction, the r+1 exponent convention, every embedding, exact
single-complex comparisons and the rational size descent. The initial chosen
embedding restriction was removed before delivery. The finite-unit comparison
is stated on its actual cochain representatives and the completed projection on
its actual strict Roos coordinates. No additional worker was started, as the
dispatcher's instructions prohibit it; the maintainer supplies the independent
mathematical review.


## New nodes

`def-zl-finite-regular-coefficient-comparisons` supplies the definition interface
requested in the return: the finite regular complex and c_m, kappa_m/lambda_m,
plus the prescribed finite compositor in intrinsic coordinates. Its source is
the item's constant-sheaf expansion, steps 2 and 3, with Stacks 03D6 and 0D6D.
A DAG grep of the exact existing names finds only the reduction theorem node;
there was no definition node carrying these data. `blueprint_refs.py search
'finite regular coefficient'` found zero matches. LeanSearch returned eight
general complex-unit statements, Loogle returned six ordinary module-pullback
unit declarations, and the Mathlib grep found zero exact-name matches. The
complete msearch outcomes are in the node's mathlib_searches. Project inspection
found the existing finite constructions and the unit-normalized coordinate
bridge, which are reused directly. The four aliases have exactly the original
data, with no copied definition body or extra choice. The added compositor is
the published canonical specialization transported across that bridge. All
definitions have actual data; this definition module adds no theorem holes.

## Returned delivery repair

1. Removed `lem-pod-canonical-coefficient-pullback-reduction` from the added
statement dependencies. `finiteUnit_canonicalWeil` now uses the regular complex,
kappa and coefficient map through the new definition node's transparent
interface. Its lambda is recorded too. The existing theorem remains available
for the proof route; none of its asserted conclusions is used to fabricate data.

2. Deleted the local `finiteComposition` and removed it from lean.declarations.
Every use in `finiteWeilIterate`, `finiteTransportIterate`, and `finiteOperator`
now calls the new definition's `finiteCanonicalPullbackComposition`. Its middle
factor is literally `integralFiniteCanonicalPullbackComposition`; the outer
factors are the published, uniquely unit-preserving coordinate changes. Thus
the recurrence and both return-comparison legs use the compositor prescribed by
`def-weil-local-frobenius-trace`, including its termwise K-flat normalization.
No duplicate of `sfIntrinsicDerivedPullbackComp` remains.

Re-read both modules and the new node. The four aliases preserve all binders
and the positive-level m+1 convention. The compositor has direction composite
pullback to successive pullbacks: intrinsic composite -> tensor composite ->
tensor iterated -> intrinsic iterated. Its inverse therefore has exactly the
direction needed in point transport. The edge cases m=0 and n=1 remain present,
and no condition on nonemptiness, separation or the geometric point is added.
The original node's statement, proof and proof dependencies remain unchanged.
No other agent was started, in accordance with the dispatcher's instruction.

Validation of the repaired sources: `scompile.py Q31
lem-zl-constant-geometric-stalk-unit` compiled each of the two delivered modules
against current server sources without diagnostics (13.0 s and 50.8 s, under the
unchanged 60-second per-file limit). The local attempt timed out; the wrapper's
server confirmation completed cleanly. Checked that the item differs from the
current read clone only in lean and additions to stmt_deps; its statement and
proof route are unchanged. Both source files meet the 100-character limit.

The push-time server confirmation subsequently hit the unchanged 60-second
limit on the stalk module. Repaired import elaboration by adding `no_expose` to
the finite compositor definition: its implementation remains the same canonical
coordinate transport, while consumers use its public signature without unfolding
that composite of natural isomorphisms. This is a module transparency adjustment,
not a statement or construction change. Validation was restarted on both files.

A development-only profiler run identified costly typeclass synthesis in the
return comparison's untyped `congrArg` lambda. Added its explicit scheme-morphism
argument type in both the finite and integral return comparisons, preserving
the exact maps and equality. Removed every profiling option before validation.
The compositor remains hidden with no_expose, with its signature fully public.
