## Worker report

The complete statement already exists as
`AlgebraicGeometry.Scheme.betti_symmetry` in
`WeilConjectures.ZetaFunction.BettiSymmetry`. The delivery records it with
`existing: true`; no Lean module, definition, proof, or supplementary assumption
is introduced. The node copy changes only `lean`. The full published source was
read through `scompile.py --source`, including the section binders, docstring,
statement, and proof. It is newer than the older local source checkout.

Sources: the node's master blueprint file
`sec-zeta-weil/sk-thm-weil4/thm-weil-final-betti.md`, and the current snapshot's
same node and `sec-zeta-weil/sk-thm-betti/_section.md`. The latter states exactly
the Betti, endpoint, and simple-pole assertions of the existing theorem.

The signature in `lean.statement` is verbatim from the published declaration.
Its section parameters are `k₀ : Type u`, `[Field k₀]`, `[Finite k₀]`,
`X : Scheme.{u}`, `[X.Over (Spec (CommRingCat.of k₀))]`, `d : ℕ`,
`[IsProper (X ↘ Spec (CommRingCat.of k₀))]`,
`[SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]`, and
`[GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))]`.

Hypothesis and clause correspondence:

| Node | Existing Lean |
| --- | --- |
| A finite field k₀ = F_q of characteristic p | `k₀`, `Field k₀`, `Finite k₀`; `q` is `Nat.card k₀`, and `p` is `ringChar k₀`. Every finite field is covered, not just a specified presentation of F_q. |
| A fixed algebraic closure k and X = X₀ × k₀ k | The geometric base change is internal to `WeilSheaf.adicConstant k₀ l X` and its ordinary cohomology. The conclusion is invariant under the unique base-compatible isomorphism between choices of algebraic closure. No different geometric fibre is substituted. |
| X₀ is a k₀-scheme | `X.Over (Spec (CommRingCat.of k₀))`, with structure map `X ↘ Spec (CommRingCat.of k₀)`. |
| Smooth, proper, geometrically connected, pure dimension d ≥ 0 | `SmoothOfRelativeDimension d`, `IsProper`, and `GeometricallyConnected` on that structure map, with `d : ℕ`. Over a field, smoothness of relative dimension d is smoothness with pure geometric dimension d. Smooth connected schemes over an algebraically closed field have disjoint regular irreducible components, hence one component; the local relative dimension is the geometric dimension. Properness already supplies finite type and separatedness. Geometric connectedness includes nonemptiness. |
| The polynomials Pᵢ in Z[T], 0 ≤ i ≤ 2d | `P : Fin (2 * d + 1) → Polynomial ℤ`; this enumerates exactly the integers in the stated closed interval. |
| Pᵢ is the integral Frobenius factor for every prime ℓ ≠ p | `hP : ∀ i, IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)`. This predicate quantifies over every `l : ℕ` with `Fact l.Prime` and `Fact (ringChar k₀ ≠ l)` and requires polynomial coefficient extension to equal `frobeniusCharpolyRev`. |
| Pᵢ(0) = 1 | This follows already from the integral-factor predicate because `coeff_zero_frobeniusCharpolyRev` is 1 and integer coefficient extension is injective. Thus the missing separate normalization binder drops no hypothesis and admits no additional family. |
| F is geometric Frobenius on ordinary cohomology | `frobeniusCharpolyRev` is the local polynomial of `(WeilSheaf.adicConstant k₀ l X).cohomology i`. Its operator is the recorded geometric Frobenius, not an independently supplied operator. Ordinary `.cohomology` is formed with `derivedLowerStar`; compact cohomology is a separate declaration. |
| bᵢ = deg Pᵢ | `(P i).natDegree`; `weilBettiNumber P (i : ℕ)` is this same value by `weilBettiNumber_natCast`. Normalization excludes the zero polynomial. |
| bᵢ = dim over Q_ℓ of Hⁱ for every ℓ ≠ p | The first conjunct quantifies over every admissible prime and every degree and equates `(P i).natDegree` to `Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier`. The recorded family explicitly uses algebraic-closure coefficients. Flat coefficient extension identifies this with Hⁱ(X,Q_ℓ) tensored to its algebraic closure and preserves dimension. See the representation checks below. |
| bᵢ = b₂d₋ᵢ | The second conjunct is `(P i.rev).natDegree = (P i).natDegree`. `Fin.rev` has value `2*d - i.val`; equality is symmetric. |
| b₀ = b₂d = 1 | The next two conjuncts are `(P 0).natDegree = 1` and `(P (Fin.last (2 * d))).natDegree = 1`. |
| P₀(T) = 1 - T | `P 0 = 1 - Polynomial.X`. |
| P₂d(T) = 1 - q^d T | `P (Fin.last (2 * d)) = 1 - C ((Nat.card k₀ : ℤ) ^ d) * Polynomial.X`. |
| Z = product Pᵢ to exponents (-1)^(i+1) | The associated rational function is the odd parity product divided by the even parity product. Its identification with the zeta series is supplied by the integral-factor theorem, not an additional hypothesis of Betti symmetry. |
| A pole of order exactly 1 at T = 1 | The penultimate conjunct says that the even product, mapped coefficientwise to Q[T], has root multiplicity 1 at 1, and the odd product is not a root there. Thus cancellation cannot change this multiplicity in the reduced denominator. |
| If d ≥ 1, a pole of order exactly 1 at T = q^(-d) | The final implication has hypothesis `1 ≤ d` and the same two conditions at `((Nat.card k₀ : ℚ) ^ d)⁻¹`. |

Representation checks, not statement corrections:

1. The published `WeilConjectures.ZetaFunction.CohomologicalFamily` module
   explicitly documents its algebraic-closure coefficient convention and the
   flat base-change identity
   Hⁱ(X,Q_ℓ) tensor Qbar_ℓ = Hⁱ(X,Qbar_ℓ). Its definitions
   `Scheme.frobeniusCharpolyRev` and `Scheme.IsIntegralFrobeniusFactor` are the
   very declarations recorded by the corresponding dependency nodes. This is
   scalar extension of the same cohomology, not restriction of scalars, whose
   dimension would be wrong. Mathlib's `Module.finrank_baseChange` in
   `Mathlib.LinearAlgebra.Dimension.Constructions` gives the dimension equality.
   The ordinary cohomology construction in `WeilConjectures.WeilSheaf.Cohomology`
   was also read: `.cohomology` uses `derivedLowerStar`; its compact counterpart
   uses `derivedLowerShriek`. The constant-object construction in
   `WeilConjectures.WeilSheaf.Constant` supplies its canonical Weil structure.
2. For poles, set N equal to the odd rational polynomial product and D equal to
   the even product. All factors have constant coefficient 1, so N,D are nonzero
   and the fraction N/D is nonzero. If m_c(D)=1 and N(c)≠0, the gcd removed in a
   reduced presentation cannot vanish at c, so the monic reduced denominator
   has m_c=1. Conversely the weight separation in the node's proof rules out
   contributions of every factor except the relevant endpoint; this yields
   precisely the two parity-product clauses. This is the concrete simple-pole
   encoding used by the published theorem, including exclusion of cancellation.
   `RatFunc.denom` and `Polynomial.rootMultiplicity` are exactly the node's
   recorded rational-function and pole-order interfaces.
3. `SmoothOfRelativeDimension` is the standard equivalent encoding of the
   node's geometric hypothesis over a field. It does not add equidimensionality
   beyond the explicitly stated pure dimension. The source
   `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` documents and
   states `smoothOfRelativeDimension_iff_topologicalKrullDim_eq` in the smooth
   irreducible case and localizes smooth morphisms by relative dimension.

Dependency declarations read and used to identify the match:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, `.extensionPoints`, `.pointCount`, `.CoefficientDatum`.
- `Sheaf.Paper.GeometricHypotheses`:
  `WeilConjectures.FiniteFieldDatum.IsSmoothOfPureDimension`; the same module
  specifies use of Mathlib's `IsProper` and `GeometricallyConnected`.
- `Sheaf.Paper.GlobalGeometricFrobenius`:
  `WeilConjectures.globalGeometricFrobenius` and
  `globalGeometricFrobeniusOnCohomology`, transport followed by the Weil structure.
- `WeilConjectures.ZetaFunction.CohomologicalFamily`:
  `AlgebraicGeometry.Scheme.frobeniusCharpolyRev`,
  `IsIntegralFrobeniusFactor`, and `coeff_zero_frobeniusCharpolyRev`.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`:
  `commonStageCompactWeilCohomology`, `adicOrdinaryCohomology`,
  `adicCompactCohomology`. These retain the recorded general coefficient
  interfaces; they are not redefined or imported by a new duplicate statement.
- `Mathlib.Algebra.Polynomial.Eval.Defs`: `Polynomial.map`, the unique integer
  coefficient map specialized in `IsIntegralFrobeniusFactor`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`; `natDegree` for its degree.
- `WeilConjectures.ZetaFunction.BettiNumbers`:
  `AlgebraicGeometry.weilBettiNumber` and `weilBettiNumber_natCast`.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- The node's older `Comparator.Weil.Definitions` record points to the definitions
  now imported as `Weil.Definitions`: `Scheme.Hom.pointCount`,
  `Scheme.Hom.zetaSeries`, `AlgebraicGeometry.IsWeilFactorization`.
  Their actual definitions were read in the local source. The integrality
  theorem is available in the published
  `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` as
  `Scheme.integral_frobenius_factors` and
  `isWeilFactorization_of_isIntegralFrobeniusFactor`; its full source was read.
  No repair of the historical record is needed to record an already existing
  theorem. In particular `IsWeilFactorization` is not mistaken for a theorem
  proving the existence or uniqueness of integral factors.
- `Mathlib.RingTheory.HahnSeries.PowerSeries`: `HahnSeries.ofPowerSeries` for
  the rational-power-series interpretation; `RatFunc` in
  `Mathlib.FieldTheory.RatFunc.Defs` and its reduced denominator; and
  `Polynomial.rootMultiplicity` in `Mathlib.Algebra.Polynomial.Div`.

Edge cases checked before selecting the match:

- d=0 is included: the index type is `Fin 1`, zero and last agree, both
  endpoint factors are 1-T, both Betti numbers are 1, and the second pole clause
  is guarded by `1 ≤ d`. The rational function has a single simple pole at 1.
- The empty scheme is excluded by geometric connectedness, as in the source.
- Cohomology degrees 0 and 2d are included. Every integer in the stated range
  corresponds to exactly one element of `Fin (2*d+1)`; there is no natural-number
  subtraction that silently includes out-of-range integer degrees.
- All primes distinct from the characteristic, including 2 where admissible,
  are quantified over; no fixed auxiliary prime or coefficient embedding is
  assumed. Finite fields have cardinality at least 2.
- For d≥1 the two rational points are distinct, and the top factor has a simple
  root at q^(-d). For P¹, P=(1-T,1,1-qT) and b=(1,0,1), giving both simple poles.
- Universe `u` is arbitrary in the existing theorem and does not require an
  equality between a scheme universe and a new independent coefficient universe.

Searches actually run through the prescribed msearch wrapper:

- LeanFinder: `Betti numbers smooth proper finite field Frobenius integral
  polynomials symmetry simple poles zeta`; eight unrelated results, including
  `Polynomial.cardPowDegreeIsAdmissible` and number-field Dedekind-zeta lemmas.
- LeanSearch: `Betti symmetry smooth proper finite field Frobenius cohomology
  zeta simple poles`; eight unrelated results, including properness and Witt
  vector Frobenius lemmas. No exact Mathlib theorem.
- Loogle: `Polynomial.rootMultiplicity, RatFunc.denom`; no hits.
- Wrapper grep: `betti|Betti|WeilFactorization`; no hits. This no-hit output is
  recorded faithfully; the direct source searches below located upstream work.
- Direct `rg` in the upstream `WeilConjectures` tree for `betti`, `Betti`, and
  `IsWeilFactorization` found the old BettiNumbers symmetry lemma and references
  from IntegralFactors and Statement. Searching `thm-weil-final-betti` there
  found no literal identifier. The old symmetry lemma alone omits most clauses.
- Direct `rg` in `lean/Sheaf/Paper` and `lean/Sheaf/Targets` for `betti|Betti`
  found curve-family Betti cardinalities, not this statement.
- The recorded `prop-endpoints` dependency names the newer
  `WeilConjectures.ZetaFunction.BettiSymmetry` module. Reading its full published
  source with `scompile.py --source` found the complete `Scheme.betti_symmetry`
  theorem. Its hypotheses, every conjunct, and the geometric/coefficient
  conventions were then checked as above. This existing match takes priority
  over writing a second theorem.

No new nodes, dependency modules, statement corrections, or disputed statements.
The dry run checks the recorded declaration with an actual imported `#check`.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
