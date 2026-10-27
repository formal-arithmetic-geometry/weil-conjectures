## Worker report

The module `Sheaf.Analysis.Calculus.CoordinateWeightedAdjoint` states
`CoordinateDifferentialOperator.weightedAdjoint_spec`. Its two real-data helper definitions
are `CoordinateDifferentialOperator.firstOrder` (the displayed L) and
`CoordinateDifferentialOperator.weightedAdjoint` (the displayed Q). They belong to the item's
own coordinate expression; neither introduces an independent mathematical notion. The sole
postponed proof is the named theorem `weightedAdjoint_spec`, with all five accepted DAG proof
steps in its docstring. No theorem is proved, and no definition contains a postponed proof.

The previous ending concerned stage 1, not this stage-2 task. The live node is split, reviewed,
in the stage-2 queue, and has no Lean record. The stage-handoff paragraph of
`coord/brief-stage2.md` explicitly authorizes recording the statement without reopening the
accepted split. There is no released repair note for this item. The natural-language node,
its statement dependencies, and its accepted proof are preserved.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The fields are the existing Mathlib types `ℝ` and `ℂ`, with their standard `Field` instances.
  `Fin m → ℝ`, `Fin r → ℂ`, and `Fin s → ℂ` are the real coordinate and complex vector spaces.
  `hm : 1 ≤ m`, `hr : 1 ≤ r`, and `hs : 1 ≤ s` retain exactly the three positive dimensions.
- `U : Set (Fin m → ℝ)` and `hU : IsOpen U` give the open coordinate domain. Functions on U
  are represented by arbitrary functions on the ambient space. All smoothness, pointwise
  conclusions and integrals are restricted to U. Every function defined on U admits an
  arbitrary extension, and on an open set its derivatives at points of U are independent
  of that extension. Thus this representation excludes no local section and adds no
  global regularity, boundedness or support assumption.
- `H_E` and `H_F` have precisely the square matrix sizes r and s. `hE` and `hF` assert real
  `ContDiffOn ℝ ∞` of each entry. This is exactly smoothness into a finite matrix space,
  without selecting a matrix norm convention. `hEpos` and `hFpos` use Mathlib
  `Matrix.PosDef`, which includes the Hermitian condition as its first conjunct and strict
  positivity of the Hermitian quadratic form on all nonzero finitely supported vectors
  as its second. For finite index sets these are all vectors. Mathlib's `ComplexOrder`
  means positivity is real strict positivity with zero imaginary part, as required for
  a Hermitian quadratic form. No separate Hermitian hypothesis is omitted.
- `ρ` is real-valued, `hρ` asserts real smoothness on U, and `hρpos` is pointwise strict
  positivity on U. This is the same datum as the source's smooth positive-valued function.
  The canonical coercion `(ρ x : ℂ)` is used in complex scalar products.
- `A` is indexed by `Fin m` and has size s by r. `B` has the same size. `hA` and `hB` assert
  smoothness of every matrix entry on U.
- `firstOrder A B u x` is exactly the sum of `(A j x).mulVec` applied to
  `fderiv ℝ u x (Pi.single j 1)`, plus `(B x).mulVec (u x)`. Thus the derivatives are real
  coordinate derivatives, with the zero-order term and all coordinates retained.
- `weightedAdjoint H_E H_F ρ A B v x` uses the genuine Mathlib nonsingular matrix inverse
  of `(ρ x : ℂ) • H_E x`, applied to the negative sum of the coordinate derivatives of
  `(ρ y : ℂ) • (((A j y).conjTranspose * H_F y).mulVec (v y))`, plus the positive term
  `(ρ x : ℂ) • (((B x).conjTranspose * H_F x).mulVec (v x))`. This is the displayed Q,
  including differentiation of the density and of both varying matrix factors.
  `Matrix.conjTranspose` is exactly conjugation followed by transposition. Under the
  hypotheses the square matrix is invertible, so its totalized inverse has its ordinary
  mathematical value. No arbitrary inverse or arbitrary map is supplied as input.
- The first conclusion gives smooth r by s coefficient matrices `C j` and `D` and states
  that Q agrees on U, for every smooth v, with `firstOrder C D v`. This is precisely the
  assertion of differential order at most one with smooth coefficients. In particular,
  this representation also makes Qv smooth for smooth v; it is not merely an integral
  identity. The existence of coefficients is the usual definition of a coordinate
  differential operator of order at most one.
- The second conclusion quantifies over all `a b : ℂ` and all smooth `v w`, and states
  pointwise on U that Q(a v + b w) = a Qv + b Qw. This expresses the claimed complex
  linearity on smooth sections, without asserting linearity of totalized derivatives
  on nonsmooth functions outside their intended domain.
- The last conclusion quantifies over arbitrary smooth `u` and `v` on U. Its disjunction
  says either there is a compact K inside U with u zero on U minus K, or there is such
  a K for v. This is equivalent to compact support contained in U: the closure in ℝ^m
  of the nonzero locus within U is a closed subset of K, hence compact and contained
  in U; conversely the closed support itself may be used as K. It does not require
  both supports to be compact, and imposes no restrictions outside U.
- `∫ x in U` is the Bochner integral with the standard Lebesgue `volume` measure on
  `Fin m → ℝ`. The left integrand is
  `(∑ i, star (firstOrder A B u x i) * ((H_F x).mulVec (v x)) i) * (ρ x : ℂ)`, exactly
  (Lu)†H_F v ρ. The right integrand is the same row-vector pairing with u, H_E and the
  actual `weightedAdjoint ... v`, exactly u†H_E Qv ρ. The equality is in ℂ. No extra
  integrability hypothesis is imposed: compactness of either support yields convergence
  as in the accepted proof.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, full class signature at line 180
  and its preceding docstring; the standard instances for ℝ and ℂ are used.
- Proof dependency `lem-sfb-smooth-nonzero-complex-reciprocal`: `ContDiffOn.inv` in
  `Mathlib.Analysis.Calculus.ContDiff.Operations`, lines 802–804; its exact nonvanishing
  hypothesis and real-scalar specialization were read. Imported as a proof dependency.
- Proof dependency `lem-sfb-continuous-compact-support-integrable`:
  `Continuous.integrable_of_hasCompactSupport`, `Mathlib.MeasureTheory.Function.LocallyIntegrable`,
  lines 621–625. Its continuity, compact-support and measure hypotheses were read.
- Proof dependency `lem-sfb-scalar-integrable-integration-by-parts`:
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`,
  `Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts`, lines 226–237. The exact
  signature requires differentiability only on the other factor's `tsupport`, with
  all three products integrable, and the ambient finite-dimensional/add-Haar hypotheses.
  Imported as a proof dependency. Search services show an older stronger global-
  differentiability signature; the current local source, not the service index, is used.

Source review: read the current blueprint direct-images proof (3), the node's agent-written
local-coordinate proof, and Kong's PDF §6.1, Lemmas 6.2–6.3 (printed pp.21–22), at
https://cims.nyu.edu/~wk805/files/Complex_Geometry_Notes.pdf. Kong gives the formal-adjoint
identities; the explicit variable-matrix coordinate formula is the DAG's supporting
calculation and is correctly not attributed verbatim to Kong. No source-based correction
is needed.

Edge cases checked before writing:

- Empty U: every local smoothness/positivity requirement and pointwise identity is vacuous;
  the support witness can be empty, and both restricted integrals are zero. No nonemptiness
  hypothesis was added.
- m = r = s = 1 with H_E = H_F = ρ = 1: Qv = -∑ conjugate(A_j) ∂_j v
  minus derivatives of conjugate(A_j), plus conjugate(B)v, with the correct adjoint sign.
- A = 0: Q is the smooth zero-order weighted conjugate transpose of B.
- Variable positive density or Gram matrix: the derivative in Q includes these factors,
  so the missing-density-derivative counterexample to a naive adjoint does not arise.
- u compact and v arbitrary, and v compact and u arbitrary, are separate alternatives;
  neither the domain nor the other section/coefficient matrices are assumed bounded.
- Zero sections allow the empty compact support. The stipulated positive dimensions are
  retained verbatim rather than silently permitting or requiring additional rank cases.

Existing-declaration searches, all on 2026-10-24:

- `msearch.py ... leanfinder`: "A first order differential operator with smooth complex matrix
  coefficients and positive Hermitian weights has a smooth weighted formal adjoint given by
  integration by parts". Eight hits, including Laplacian and Schwartz-space integration
  identities; none states this local variable-weight matrix result.
- `msearch.py ... loogle`: "Matrix.PosDef, fderiv, MeasureTheory.integral". Zero hits.
- `msearch.py ... grep`: "weighted.*[Aa]djoint|formalAdjoint|formal_adjoint" in Analysis.
  Five hits concerning `LinearPMap.IsFormalAdjoint` and its Hilbert-space adjoint. Read its
  signature/docstring: it is a predicate for partially defined maps with fixed inner
  products, not this weighted open-domain coordinate expression.
- `msearch.py ... leansearch`: "integration by parts for a first order differential operator
  with variable positive Hermitian matrix weights". Eight hits; scalar/bilinear global
  integration-by-parts and Schwartz-map formulas supply analytic ingredients but not an
  exact declaration. The current scalar integration theorem is the recorded proof leaf.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`, by the exact node id and the patterns
  `weighted.*[Aa]djoint|formalAdjoint|formal_adjoint`, finds no statement of the item.
  `HermitianDolbeaultData.lean` contains a global formal-adjoint identity as a data field,
  not this first-order coordinate formula; its metric pairing has a different manifold
  interface and does not duplicate these local operator helpers.
- `rg` over Mathlib, both project source roots and `dag/lean_names_upstream.json` for
  `coordinate.*[Aa]djoint|Weighted.*[Aa]djoint|coordinateFirstOrder|coordinateWeighted`
  finds no matching declaration. Names of both helpers and the theorem were also checked.

No statement dispute, missing dependency or new node is present. The example CompactObject
module is currently withdrawn and contains no declarations; the required current module
header, public sections and source docstrings are followed instead.

Validation: each delivered file is compiled through `scompile.py`; dry-run and push use
`deliver2.py`. The first compile diagnosed absent norm instances for matrix-valued
`ContDiffOn`; rendering smoothness entrywise removes that implementation issue without
changing the mathematical statement.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
