## Worker report

The delivery defines the complete local-Frobenius construction in
`lean/Sheaf/Paper/LocalFrobeniusTrace.lean`, namespace `WeilConjectures`.
The primary declaration is `localFrobeniusTrace`; `localClosedPointTrace` is the
closed-point counterpart. There is no statement correction or dependency repair.
All definition data are explicit. The five postponed helper theorems state the
compatibility equations, returns, and positive residue degree already asserted
in this definition node, and carry its blueprint tag and natural-language proofs.
They do not choose an unspecified operator or unspecified comparison.

Hypothesis and clause correspondence:

- The global p,a,q,k₀,k datum is `D : FiniteFieldDatum`. The chosen prime,
  inequality l ≠ p, and chosen algebraic closure of Q_l are `c : D.CoefficientDatum`.
  The finite extension contained in that closure is
  `E : Padic.FiniteCoefficientFields c.l c.Qbar`; the coefficient carrier is `E.val`.
  Internal constructions work with any finite-dimensional extension of `Padic l`;
  the two primary entry points specialize to the exact chosen subextension.
- The finite-type model is `Y₀ : Over (Spec (.of D.k₀))` with
  `[LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]`, exactly finite type.
  No separatedness hypothesis appears. Its geometric fibre is
  `(D.geometricFiber Y₀).left`. Its geometric Frobenius is
  `(D.geometricFrobenius Y₀).hom`, and that of s is `(frobeniusPointIso D).hom`.
- The input `K : sfWeilComplex D l hl Y₀ E` is the dependency's fixed pair.
  `K.carrier` is For(K); `K.str` is theta: Lg_Y^*For(K) ≅ For(K).
  This is the fixed-pair category, not the upstream derived category of Weil sheaves.
- An arbitrary geometric point is `x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left`.
  The algebraic closure in D supplies its algebraic closedness.
  `localDerivedStalk` is the recorded `rationalDerivedPullback` along x, applied
  to K.carrier; it realizes K_xbar. `localPointComplex` applies
  `pointRationalFibre` and lands in `(DerivedCategory.pointFiniteDimensional E).FullSubcategory`.
- The stalk in degree j is the value of `DerivedCategory.coefficientFdCohomology E j`
  on that complex. This is exactly the stipulated interpretation of H^j(M)_xbar.
  Its finite-dimensionality and finite support are the two clauses of
  `localPointComplex ... |>.property`, inherited from `pointFiniteDimensional`.
- `localPositivePower g n` has exponent n+1. Thus `localWeilIterate ... K 0 = K.str`
  realizes theta^[1]. Its successor first applies `localPullbackComposition`,
  then L(g_Y^(n+1))^*theta and finally theta^[n+1], realizing the displayed recurrence.
  The positive-exponent indexing is internal; public extension-point operations
  take `n : ℕ`, `hn : 1 ≤ n`, and use n-1. No n=1 case is dropped.
- `localPullbackObjectIso` uses the recorded object equation of rational pullback.
  `localPullbackComposition` applies `sfRationalConstructibleLocalization.mapIso`
  to the specified integral comparison from `integralPullbackComposition` and
  identifies its endpoints by these object equations. The integral comparison
  is the recorded one with the prescribed finite reductions and associativity.
  There is no arbitrary natural-isomorphism assumption or new pullback notion.
- `localPointTransport` is `frobeniusPointTransportRational` followed only by the
  canonical identification of its raw integral pullback object with the actual
  rational pullback object. `localPointTransportIterate` composes this at N, GN,
  and each later pullback, then applies the inverse composition comparisons.
  It realizes precisely I^[n]_N with the correct direction.
- `localReturnComparison` uses the equality
  `x ≫ g_Y^n = g_s^n ≫ x` between scheme morphisms and the two specified composition
  comparisons. It never asserts `x ≫ g_Y^n = x`.
  `localFrobeniusOperator` is the composite of iterated point transport, the
  point-fibre image of this middle comparison, and the point-fibre image of
  Lx^*theta^[n]. `localFrobeniusCohomology` applies the recorded cohomology functor.
- Finite-extension points use exactly `x : D.extensionPoints Y₀ n hn`.
  `localExtensionPoint` is the actual fibre-product lift of
  `Spec(F_(q^n) ⊂ k) ≫ x.left` and the identity of Spec(k), using the named
  compatibility theorem. `localExtensionPoint_return` is the reparametrized
  return asserted in the node: gamma^n fixes the unique finite subfield.
  `localExtensionFrobenius` and `localExtensionFrobeniusCohomology` use that
  theorem, so callers have no additional return hypothesis.
- A closed point is `y : {y : Y₀.left // y ∈ closedPoints Y₀.left}`.
  `localClosedPointDegree` is the finrank of the actual scheme residue field,
  with the algebra induced by `Y₀.hom.residueFieldAlgebraMap y.val`.
  `localClosedPointDegree_pos` states its positivity, from closed-point field
  finiteness. The chosen k₀-embedding is a ring homomorphism ι from that residue
  field to D.k, together with `hι` saying its composite with the structure map
  equals `algebraMap D.k₀ D.k`. A field ring homomorphism is injective, so this
  is precisely a k₀-embedding, without an additional injectivity assumption.
  `localClosedPoint` is the fibre-product lift using
  `Spec.map ι ≫ Y₀.left.fromSpecResidueField y.val`.
  `localClosedPoint_return` supplies the degree-r return. `localClosedFrobenius`
  and `localClosedFrobeniusCohomology` apply the same operator at exponent r.
- `localAlternatingTrace` uses `∑ᶠ j : ℤ` of `(j.negOnePow : ℤ)` times
  `LinearMap.trace E ...` of the induced linear map. This is a finite sum:
  the point-complex property makes H^j zero outside a finite set, hence the
  trace summand is zero there. The use of `finsum` chooses no arbitrary interval
  or truncation and includes every positive and negative cohomological degree.
  `localExtensionTrace` and `localClosedTrace`, and their complete-datum wrappers,
  give the two traces requested by the node, with values in E itself.

Dependency declarations read and used (directly or by the listed public imports):

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `CoefficientDatum`,
  `geometricFiber`, `extensionSubfield`, `extensionEmbedding`, `extensionPoints`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its imports:
  `Padic.coefficientExtensionIntegers`, uniformizer, quotient coefficient rings,
  `Padic.finite_coefficientExtensionRing`; the coefficient structures are inherited
  by the rational categories and composition comparison.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`, `sfWeilFrobeniusPullback`,
  `sfWeilPrimeInvertible` (the latter derives invertibility, without an extra hypothesis).
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalDerivedPullback_existsUnique`, `constructibleIntegralPullback`.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`.
- `Sheaf.Paper.CoefficientCohomologyModules`: `DerivedCategory.coefficientFdCohomology`,
  the restriction of `DerivedCategory.homologyFunctor` from Mathlib's derived category.
- `Sheaf.Paper.IntegralFinitePullbackComposition` and
  `Sheaf.Paper.IntegralPullbackComposition`: the finite normalized comparison and
  `integralPullbackComposition`, respectively; the latter's recorded finite reduction
  is the former, and its actual isomorphism is localized here.
- `Sheaf.FieldTheory.UniqueSubfieldOfClosure`:
  `FiniteField.exists_unique_subfield_of_closure`, used by the subfield definition
  and the proof plan for the finite-field return.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointPrimeInvertible`, `frobeniusPointTransportRational`.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldAlgebraMap`, `Scheme.fromSpecResidueField`.
- `Mathlib.LinearAlgebra.Trace`: `LinearMap.trace`.
- `Sheaf.AlgebraicGeometry.ClosedPointField`:
  `closedPoint_iff_residueField_trdeg_zero_and_finite` in the degree/return proof plans.

Edge cases checked before and during writing: n=1 gives theta itself and a single
point transport; r=1 gives the same one-step closed-point construction. The empty
model has no finite-extension points or closed points, so both entry points are
vacuous without a nonemptiness restriction. The zero complex gives zero traces.
A constant rank-one complex with canonical datum has local trace 1; a shift by
one changes the sign, including negative-degree representatives. No cohomological
range [0,2d] or separatedness is imposed. The generic operator has a return argument
only as an internal construction; finite-extension and closed-point entry points
supply the return from the named theorems.

Searches for existing declarations:

- `msearch.py ... leanfinder "Local geometric Frobenius endomorphism on cohomology
  of a Weil complex and alternating trace"`: eight Witt-vector isocrystal hits,
  no matching sheaf/derived point-fibre construction.
- `msearch.py ... loogle "LinearMap.trace"`: twelve ordinary trace hits, used for
  the trace summands; none constructs the local Frobenius operator.
- `msearch.py ... grep "localFrobenius|local_frobenius|WeilComplex|WeilSheaf"`:
  zero Mathlib hits.
- `rg` for localFrobenius/local_frobenius/alternatingTrace in the source project
  and `lean/Sheaf`: upstream `WeilSheaf/LocalFrobenius.lean` and trace-series files,
  and `RealSheavesSetup.Setup.localFrobenius`; no exact current-category match.
  The upstream LocalFrobenius module was opened: it explicitly says its alternating
  trace does not use the derived stalk, and its signatures use PadicAlgCl, the
  derived category of Weil sheaves and a distinguished AlgebraicClosure k₀.
  These do not give this node's finite-E fixed-pair construction with arbitrary
  fixed base-field closure and derived point complex. RealSheavesSetup is a
  different real-sheaves setup, not the recorded rational constructible category.
- `rg` for rational composition comparisons under `lean/Sheaf/Paper` and
  `lean/Sheaf/SixFunctors`: no existing comparison on these rational pullbacks.
  The required comparison is defined by localizing the recorded integral one;
  no theorem about an unspecified rational comparison is assumed.
- `msearch.py ... leansearch` was additionally requested for the full local
  derived-stalk/Frobenius/alternating-trace concept; result: eight ring/Witt-vector Frobenius hits, no matching derived-stalk or
  Weil-complex construction.

No STATEMENT-DISPUTED issue was found. No new nodes or dependency modules are needed.

## Second reading by Q103

A final rereading by the same dispatched worker (no second agent was started;
the independent maintainer review follows delivery) matched the node and the file
clause by clause as above. The important checks were: theta has direction Lg* M ≅ M;
the recurrence uses L(g^n)*theta before theta^[n]; the point return is reparametrized;
the middle comparison has source L(g_s^n)*Lx* M and target Lx*L(g_Y^n)*M;
the point transport precedes the pullback of theta; positive exponents use n-1
only after n≥1; residue-field embeddings are over k₀; the trace uses integer
cohomological signs, and E rather than Qbar. A preliminary compiler failure from
abbreviated `.ofHom` was repaired to `CommRingCat.ofHom`. The finite sum was written
as Mathlib `finsum` to avoid choosing a cohomological cutoff. All data definitions
were checked to contain no `sorry`; the five named compatibility/return/degree
assertions alone postpone proofs. The module and node tag every such assertion
as part of this node's expressly stated construction.

## Validation

All compilation uses the prescribed `scompile.py` wrapper, file by file within
its default 60-second limit. Final compile and dry-run results are appended below.

Final standalone `scompile.py`: clean sandbox compile (23.3 s) and library-module
compile (50.0 s), with no errors or warnings. No global build was run.
`deliver2.py Q103 def-weil-local-frobenius-trace --no-push` returned
`OK (dry run): commit ad40b45cf6 passes the preflight and compiles; nothing pushed`.
The only changed node field is `lean`; the primary signature matches the source
verbatim, all 28 declarations are listed, and every line is at most 96 characters.
