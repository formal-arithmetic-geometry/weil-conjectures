## Worker report

The module `Sheaf.Paper.ArithmeticRoots` states
`WeilConjectures.arithmetic_roots` with `sorry`. No theorem is proved.
The only other declarations are two instances assembled from existing Mathlib
results: the base field has characteristic `D.p`, and a coefficient prime is
therefore different from `ringChar D.k₀`. Their definitions contain no `sorry`.
No new nodes or dependency records are needed; the item changes only in `lean`.

Sources read: the item's full node and proof; the statement and proof at
`literature/blueprint/master/blueprint/sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots.md`;
the same statement in the main-20261015 snapshot; and all eight statement-dependency
nodes, with the full signatures and docstrings of their declarations. The current
upstream family and reciprocal-root modules were read through `scompile.py --source`
because they are absent from the old slopmaster2 checkout.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum` contains prime `p`, exponent `a ≥ 1`, `q = p^a`, a field
  `k₀` with exactly `q` elements and the specified algebraic closure `k`.
- `X₀ : Scheme` and `[X₀.Over (Spec (.of D.k₀))]` give the scheme over the base.
  `[IsProper ...]` supplies properness and finite type;
  `[GeometricallyConnected ...]` gives geometric connectedness, including nonemptiness.
- `d : ℕ` and `hsmooth : D.IsSmoothOfPureDimension (Over.mk ...) d` supply exactly
  smoothness and pure dimension `d` of `D.geometricFiber ...`, the node's `X`.
  The ordinary cohomological family already performs geometric base change; it
  does not take an independently chosen second scheme.
- `i : ℤ`, `hi₀ : 0 ≤ i`, and `hi : i ≤ 2 * (d : ℤ)` retain the integer degree and
  both endpoint cases.
- `P : Polynomial ℤ`, `hP₀ : P.coeff 0 = 1`, and
  `hP : Scheme.IsIntegralFrobeniusFactor D.k₀ X₀ i P` give the integer factor,
  normalization and coefficientwise equality for every prime simultaneously.
  The recorded upstream family is over `PadicAlgCl l`; its module explicitly uses
  the flat scalar-extension identification from the rational family. Equality there
  is equivalent to the node's rational coefficient equality, since the coefficient
  embedding is injective. Neither existence nor uniqueness of `P` is assumed.
- `Qbar : Type v` with `Field`, `Algebra ℚ` and `IsAlgClosure ℚ` retains any fixed
  algebraic closure of the rationals, independently of the scheme universe.
- `P.reverse` is Mathlib's finite coefficient reversal, precisely
  `U^(P.natDegree) P(U⁻¹)`. The first conclusion `P.reverse.Monic` is the monicity
  clause. There is no need for an extra variable or definition for `r_i`.
- `(P.reverse.map (Int.castRingHom Qbar)).IsRoot α` is exactly the reciprocal-root
  condition in the fixed rational algebraic closure. `IsIntegral ℤ α` is the
  algebraic-integer clause.
- `IsWeilNumber D α (i : ℝ)` unfolds to `α ≠ 0` and, for every ring homomorphism
  `τ : IntermediateField.adjoin ℚ {α} →+* ℂ`, the norm equality
  `‖τ (IntermediateField.AdjoinSimple.gen ℚ α)‖ = (D.q : ℝ)^((i : ℝ)/2)`.
  Thus it renders both the displayed embedding clause and the Weil-number clause.
  Ring homomorphisms of these characteristic-zero fields automatically fix ℚ.
- `∀ C : D.CoefficientDatum` ranges over each prime distinct from `p` and each
  specified coefficient closure. `j : C.AlgebraicNumberRealization D Qbar` is the
  recorded rational algebra isomorphism onto `algebraicClosure ℚ C.Qbar`, and
  `((AlgEquiv.toEquiv j) α : C.Qbar)` composes it with the actual intermediate-field inclusion.
- To express the recorded ordinary cohomology with this chosen closure, the statement
  quantifies over all coefficient isomorphisms
  `e : PadicAlgCl C.l ≃ₐ[Padic C.l] C.Qbar`. Such isomorphisms exist by
  `IsAlgClosure.equiv`. This is a choice of coordinates, not an extra mathematical
  assumption: the assertion holds for every such identification, not just one.
  The realized scalar is nonzero and its inverse is a root of
  `(Scheme.frobeniusCharpolyRev ...).map e.toRingHom`. This is exactly the reciprocal
  root convention of the recorded `Polynomial.ordinary_reciprocal_roots`.
- The eigenvalue clause uses `.HasEigenvalue` on the linear map obtained by applying
  `ModuleCat.extendScalars e.toRingHom` to the Frobenius of the recorded ordinary
  cohomology of `WeilSheaf.adicConstant`, explicitly taken as the first component
  of `WeilSheaf.ordinaryCompactWeilSheafCohomology`. This is the concrete module
  `C.Qbar ⊗[PadicAlgCl C.l] H^i(X, PadicAlgCl C.l)`, with operator `1 ⊗ F`.
  It expresses ordinary cohomology after scalar extension as requested; the
  compact-support component is not used. No arbitrary map is a hypothesis.
- The final universal quantifier over `β` satisfying `(P.map ...).IsRoot β`, and then
  every embedding of `ℚ(β)`, states precisely the ordinary-root norm
  `(D.q : ℝ)^(-(i : ℝ)/2)`. These are all ordinary roots, not just a selected inverse.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.CoefficientDatum`, and its geometric-fibre convention (publicly
  imported through the recorded dependent modules).
- `Sheaf.Paper.GeometricHypotheses`: `FiniteFieldDatum.IsSmoothOfPureDimension`;
  properness and geometric connectedness use the existing scheme-morphism classes.
- `Sheaf.Paper.AlgebraicNumberRealization`:
  `FiniteFieldDatum.CoefficientDatum.AlgebraicNumberRealization` and `ratAlgebra`.
- `Sheaf.Paper.WeilNumbers`: `WeilConjectures.IsWeilNumber`.
- `WeilConjectures.ZetaFunction.CohomologicalFamily`:
  `AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor` and `frobeniusCharpolyRev`.
- `WeilConjectures.ZetaLinearAlgebra.ReciprocalRoots`:
  `Polynomial.ordinary_reciprocal_roots`, using its existing `IsRoot` and nonzero
  convention, and `LinearMap.reciprocal_roots_eigenvalues` for the proof plan.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` retains, via public imports,
  `AlgebraicGeometry.WeilSheaf.ordinaryCompactWeilSheafCohomology`. Its ordinary
  component is definitionally `F.cohomology i`, which is the cohomology used here.
  The newer common-stage compact specialization is not substituted for ordinary H^i.
- Stated proof dependencies are imported: `Polynomial.reciprocal_polynomial_of_constantCoeff_one`,
  `WeilConjectures.embedding_extension_and_intrinsic_weights`, the recorded weight
  purity declarations, `LinearMap.reciprocal_roots_eigenvalues`, and
  `Polynomial.IsRoot.map`. The other proof-only nodes have no published statement
  yet and are referenced by their IDs in the full seven-step proof docstring.

Edge cases checked before writing: `d = 0` and `i = 0` are allowed; `i = 2d` is
allowed; `P = 1` has monic reverse and no roots, so the root conclusions are vacuous;
`P = 0` is excluded exactly by `hP₀`; nonzero constant terms rule out zero ordinary
roots, and `IsWeilNumber` includes nonzero reciprocal roots. Geometric connectedness
excludes an empty scheme exactly as in the node. The prime `p = 2` causes no
exception, and neither coefficient continuity nor a complex embedding is assumed.
All variables and universes are explicitly bound, with both auto-implicit options off.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "The reciprocal roots of the integral Frobenius polynomial
  are algebraic integers and Weil numbers of weight i". Eight finite-field polynomial
  expansion hits; none states this result.
- `msearch.py ... loogle`: `Polynomial.reverse, IsIntegral, IsWeilNumber`.
  No hits; Mathlib does not know `IsWeilNumber`.
- `msearch.py ... leansearch`: "reciprocal roots integral Frobenius factor Weil number".
  Eight finite-field polynomial expansion hits, no matching theorem.
- `msearch.py ... grep`: `arithmetic_roots|ArithmeticRoots|IsWeilNumber|IsIntegral.*reverse`.
  No Mathlib hits.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item ID,
  `arithmetic_roots|arithmeticRoots|IsIntegralFrobeniusFactor|frobeniusCharpolyRev`:
  no matching theorem in the old checkout. The upstream-name index likewise has
  no arithmetic-roots binding.
- `rg` in `lean/Sheaf` for the item ID and arithmetic-roots names found only the
  reciprocal-polynomial helper, not the whole theorem.
- The current `lean/WeilConjectures` contains
  `AlgebraicGeometry.Scheme.riemann_hypothesis` in `ZetaFunction.FinalTheorems`.
  Its full signature and docstring were read. It covers reciprocal integrality and
  Weil weights in ℂ, ordinary weights in ℂ, and eigenvalues in `PadicAlgCl l`.
  It does not state monicity or the arbitrary rational closure and realization clauses,
  and takes smooth-relative-dimension instances. It is therefore not an exact
  `existing: true` match to this node; the new statement retains the exact recorded
  geometric predicate and every requested closure and realization.
- Additional Mathlib source lookup found `charP_of_card_eq_prime_pow` and
  `ringChar.eq`, used directly to assemble the two instances, and `IsAlgClosure.equiv`
  for the existence of coefficient identifications. No new definition of these notions.

No statement correction or statement dispute is needed.

## Second reading by Q63

Author's self-check only; the dispatcher requests no additional agents and the
maintainer supplies the independent review. Reopened the node and Lean file together.
The hypothesis and clause mapping above checks both bounds on the integer degree,
normalization and all-prime equality for the integral factor, monicity, integrality,
every simple-field embedding, the fixed rational closure, every adic realization,
the nonzero reciprocal-root equation, the actual scalar-extended ordinary Frobenius
operator and all ordinary-root norms. The closure isomorphism is universally
quantified and its tensor functor is applied to the existing Frobenius, so no
extra chosen action or stronger assumption has been introduced. The smoothness predicate is supplied with explicit finite-type and quasi-compact
instances inferred from the existing properness hypothesis: this resolves the
bundled `Over.mk` instance lookup without adding assumptions. No statement text
or dependency list was changed. Compilation and preflight results are recorded below.

Validation: the initial fully elaborated statement passed `scompile.py`, including
the live library confirmation, without errors or warnings (40.1 s local and 39.1 s
server). The final spelling explicitly selects the ordinary component of the
recorded ordinary/compact interface; the delivery dry run compiles that final file.

The final `deliver2.py Q63 prop-arithmetic-roots --no-push` returned
`OK (dry run): commit 5ac7e9222a passes the preflight and compiles; nothing pushed`.
This checked the final ordinary-component spelling, the complete node record,
the report and exactly the three packet paths. No Lean errors or warnings remained.
