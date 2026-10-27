## Worker report

This stage-2 delivery states `QuadraticSeries.integral_closure` in
`Sheaf.RingTheory.QuadraticSeriesIntegralClosure`. The theorem has only `sorry`
as its proof. Six auxiliary abbreviations give the displayed polynomial,
quadratic equation, curve quotient, coefficient quotient, and coordinate classes.
They have explicit data and introduce no alternative general algebra notions.
The node is unchanged except for its `lean` record; there are no new nodes or
dependency repairs.

The earlier worker's stale-assignment conclusion confused stages: the ledger's
2026-10-22 04:50 entry records NQ's stage-1 split, and the live node has no `lean`
record. This delivery uses that reviewed split without modifying it.

Source read: literature/stacks-project/curves.tex, Tag 0C4A,
lemma-2-branches-delta-1, proof Cases I and II, especially lines 3990-4020.
Case II interchanges the coordinates relative to the source, as the node requests.
The split case is retained by using the quadratic quotient algebra rather than
assuming that quotient is a field.

Hypothesis and clause correspondence:

- A field F: `(F : Type u) [Field F]`, with an explicit universe `u` and no
  restriction on characteristic, cardinality, perfection or algebraic closure.
- The three coefficients: `(a b c : F)`; the two assumptions are precisely
  `ha : a ≠ 0` and `hdisc : b ^ 2 - 4 * a * c ≠ 0`.
- R = F[[X,Y]]/(aX²+bXY+cY²): `CurveRing a b c` is the quotient of
  `MvPowerSeries (Fin 2) F` by `Ideal.span {equation a b c}`. The equation uses
  `MvPowerSeries.C` and the variables indexed by 0 and 1.
- L = F[Z]/(aZ²+bZ+c): `CoefficientAlgebra a b c` is
  `AdjoinRoot (polynomial a b c)`, definitionally this exact quotient by the
  singleton-generated ideal. The polynomial has the original coefficient a,
  rather than silently replacing the quotient by another presentation.
- z, x, y: z is `AdjoinRoot.root (polynomial a b c)`; x and y are explicitly
  `Ideal.Quotient.mk` applied to `MvPowerSeries.X 0` and `.X 1`.
- The substitution j is an existential `CurveRing a b c →ₐ[F] PowerSeries L`.
  Its first conjunct specifies EVERY coefficient of j([H]): the coefficient at
  n is the finite sum over 0 ≤ i ≤ n of the coefficient of X^i Y^(n-i) in H,
  mapped from F to L and multiplied by z^i. Thus it states the actual canonical
  substitution, with no arbitrary map or chosen unknown definition. The following
  two conjuncts explicitly state j(x)=C(z)*X and j(y)=X (X in this one-variable
  target denotes t). Specifying all coefficients uniquely specifies j on the
  quotient, since the quotient map is surjective.
- Injectivity: `Function.Injective j`.
- Its image is exactly F+tL[[t]]: for every target h, membership `∃ r, j r = h`
  is equivalent to `∃ d : F, ∃ g : PowerSeries L,
  h = PowerSeries.C (algebraMap F L d) + PowerSeries.X * g`.
  This uses the given coefficient embedding, not arbitrary L-constants.
- Reducedness: `IsReduced (CurveRing a b c)`.
- Total ring of fractions: Mathlib's `FractionRing (CurveRing a b c)` is
  `Localization (nonZeroDivisors (CurveRing a b c))`; it is available for an
  arbitrary commutative ring, with no `IsDomain R` hypothesis. In particular,
  the split quadratic case is not lost.
- Finite as R-module: the `Module.Finite` conjunct passes explicitly the
  module structure `@Algebra.toModule _ _ _ _ j.toRingHom.toAlgebra`.
  Its scalar action is r • h = j(r)*h; no extra module/algebra structure is
  quantified over or assumed.
- Identified with the integral closure inside Q(R): an injective ring hom k
  from L[[t]] to `FractionRing R` satisfies
  `k.comp j.toRingHom = algebraMap R (FractionRing R)`. For every w in Q(R),
  `w ∈ integralClosure R (FractionRing R) ↔ ∃ h, k h = w`.
  Injectivity and this exact range identify B with the integral closure,
  and the commuting triangle makes the identification an R-algebra one.
- Extension of (x,y): `Ideal.map j.toRingHom (Ideal.span {x a b c, y a b c}) =
  Ideal.span {PowerSeries.X}`.
- The non-zero-divisor y=t: `y a b c ∈ nonZeroDivisors R`, together with the
  corresponding regularity of `PowerSeries.X` in B and the equation j(y)=X.
- All identifications respect j: every image, module action and ideal map uses
  the same j, and k's commuting triangle ties the integral closure to it.

Dependency declarations used (their source declarations and docstrings were read):

- `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`, finitely supported coefficient
  families with convolution; used through the public AdjoinRoot import.
- `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries`, with genuine arbitrary
  formal coefficient families; the one-variable specialization is
  `Mathlib.RingTheory.PowerSeries.Basic`, `PowerSeries`.
- `Mathlib.Algebra.Algebra.Hom`, `AlgHom`, and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Ideal.Quotient.algebra` and
  `Ideal.Quotient.mkₐ`; the coordinate abbreviations use `Ideal.Quotient.mk`.
  `Ideal.span` and `Ideal.map` give the displayed ideal and its extension.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`, is finite generation of
  the whole module, exactly the recorded finite-module dependency.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`, has
  carrier `{w | IsIntegral R w}`; `IsIntegral` means a root of a monic polynomial
  via the structure map. No new integral-closure predicate is defined.
- The monic-quotient proof dependency uses `AdjoinRoot.powerBasis'`, and
  `Polynomial.Monic.free_adjoinRoot` / `.finite_adjoinRoot`, in
  `Mathlib.RingTheory.AdjoinRoot`. Its module is already a public import for L.
- The normality proof dependency is `PowerSeries.noetherian_normal_domain`,
  `WeilConjectures.RingTheory.PowerSeriesNormalDomain`, imported privately.
  Its full signature requires a Noetherian integrally closed domain and concludes
  all three properties for its power series ring. The proof applies it to each
  field factor of L; no domain condition on L itself is added.

The theorem docstring carries all nine steps of the reviewed proof, including
homogeneous division, the explicit image preimage, characteristic-independent
field/product calculation, two generators and integral equation, and compatible
total fraction embeddings. Nothing is proved in this delivery.

Edge cases checked before writing:

- F=R, a=1,b=0,c=1 gives the nonsplit coefficient algebra C and normalization C[[t]].
- A split quadratic, including c=0 with b nonzero, gives L=F×F; no field or
  domain assumption on L, R or B appears anywhere.
- Over F_2, a=b=1,c=0 gives the split case, whereas a=b=c=1 gives F_4.
  The discriminant is b² in characteristic two, so both remain included.
- Degree n=0 of the coefficient formula is the original constant, since the
  summation is over the singleton {0}; degree n=1 gives the requested x/y images.
- a=0 and zero discriminant are precisely excluded by the node, with no extra
  c≠0, 2≠0 or irreducibility condition. There is no empty-field case.
- `FractionRing` is the total fraction ring even for zero divisors; this was
  checked directly in Mathlib/RingTheory/Localization/FractionRing.lean:709-717.

Searches actually run through the prescribed `msearch.py Q13 <item>` wrapper:

- LeanFinder: "The normalization of a formal plane curve defined by a nondegenerate
  quadratic form over a field is the power series ring over its quadratic
  coefficient algebra". Eight results, primarily Weierstrass-curve coordinate
  rings and norm formulas; none states this formal quadratic normalization.
- Loogle: `"PowerSeries", "integralClosure"`. Zero results.
- Mathlib grep: `quadratic.*(PowerSeries|MvPowerSeries)|integralClosure.*PowerSeries|PowerSeries.*integralClosure`.
  Zero results.
- LeanSearch: "The integral closure of F[[X,Y]] modulo a nondegenerate quadratic
  form is (F[Z]/(aZ^2+bZ+c))[[t]]". Eight general integral-closure declarations,
  including `IsIntegralClosure.of_isIntegrallyClosed` and `integralClosure`;
  none supplies the substitution, kernel, image or quadratic model.
- Project rg over lean/WeilConjectures and lean/Sheaf:
  `quadratic.*[Ss]eries|[Ss]eries.*quadratic|quadraticSeries|lem-sfb-quadratic-series-integral-closure`.
  Only `FormalBinaryMorse` (changes a given series to its quadratic part) and
  `PowerSeriesQuadraticIdeal` (a different quadratic-ideal statement) matched.
  No existing declaration states this node.
- Name search over Mathlib, both project roots, and dag/lean_names_upstream.json:
  `namespace QuadraticSeries|QuadraticSeries\.|quadratic.*(normalization|integral.closure)`.
  No matches; all seven full declaration names are new.

No statement correction, disputed statement or unusable dependency was found.
The retained sandbox contained only dispatcher brief markers before this work.
Validation: prescribed scompile.py compiled both its sandbox view (6.1 s) and
library-path view (4.1 s), with exit 0 and no warnings or errors.

## Second reading by Q13

This is a worker self-check, not a claim of an independent agent review: the
item-specific dispatcher brief forbids starting other agents and assigns the
independent review to the maintainer. I reread the live statement and the complete
Lean signature together. The checks above account for both hypotheses, all
quotient objects, the canonical coefficient substitution, the two coordinate
images, injectivity, the exact wedge image, reducedness, the j-induced finite
module, ideal extension, regularity, the total fraction ring and its commuting
integral-closure embedding. The split and characteristic-two cases are retained.
No mismatch requiring a change was found; no stage-1 proof or review field changed.
