## Worker report

The module `Sheaf.RingTheory.BinaryQuadraticOrderCorrection` states
`MvPowerSeries.exists_binary_quadratic_order_correction`, with exactly one postponed
proof (`sorry`) and no new definitions. The node is unchanged except for `lean`.

Source read: `literature/stacks-project/curves.tex`, Tag 0C49,
`lemma-nodal-algebraic`, lines 3872–3960, especially the polar expansion, the polar
basis argument, and “Continuing in this fashion by induction” in (2) implies (3).
The node spells out that induction step with error `f-Q(x,y)` and positive correction.

Clause-by-clause rendering:

- The field is `(F : Type u) [Field F]`, with arbitrary explicitly bound `u`.
  The series ring is `MvPowerSeries (Fin 2) F`, with `u=X 0`, `v=X 1`.
  Polynomials use `MvPolynomial (Fin 2) F`.
- `a b c : F` and `hdisc : b ^ 2 - 4 * a * c ≠ 0` are precisely the coefficient
  and nondegeneracy hypotheses. No characteristic hypothesis or invertibility of 2
  is imposed.
- `Q` is the actual polynomial `aU²+bUV+cV²`, as specified by the defining equality
  `hQ`. `MvPolynomial.aeval ![x, y] Q` is its evaluation in the series ring.
- `p` is the ideal `(u,v)`, specified by `hp` as the span of the two variables.
  The equality binders `hQ` and `hp` simply name the objects defined by “Q=…” and
  “p=(u,v)” in the node. They impose no condition on `a,b,c,F` or the series.
- `r : ℕ`, `hr : 2 ≤ r`, and `f x y` supply exactly the order and series data.
  `hx` and `hy` express `x-u,y-v ∈ p²`; `hE` expresses `f-Q(x,y) ∈ p^(r+1)`.
- `H` is a polynomial, and `hH` identifies its canonical image in the series ring
  with `homogeneousComponent (r+1) (f-Q(x,y))`. This is exactly the polynomial of
  coefficients of total degree r+1; with two variables that support is finite.
  It neither selects an arbitrary error polynomial nor imposes vanishing at degree
  r+1. Its canonical inclusion has exactly the polynomial's coefficients.
- The witnesses are polynomials `A B`; `A.IsHomogeneous r ∧ B.IsHomogeneous r`
  says all their monomials have total degree r, allowing zero.
- The next equality is `H=L₁A(u,v)+L₂B(u,v)`. The polar factors are
  `((2*a) • X 0 + b • X 1)` and `(b • X 0 + (2*c) • X 1)`.
  Coercion of a polynomial to series is its evaluation at the formal variables.
- The final universal binders specify exactly `x'=x+A(x,y)` and `y'=y+B(x,y)`
  by equalities. These variables are quantified after the witnesses `A,B`.
  For every witness choice made by the theorem there is exactly one pair satisfying
  these equalities; thus this encodes the node's “putting x',y'”, without additional
  assumptions on the original data or an existence-only coordinate replacement.
- The next four conjuncts give `x'-x,y'-y ∈ p^r` and `x'-u,y'-v ∈ p²` individually.
- The fifth conjunct gives `Q(x',y')-Q(x,y)-H ∈ p^(r+2)`, with the exact sign of H.
- The sixth gives `f-Q(x',y') ∈ p^(r+2)`. It is included explicitly, not left as an
  informal consequence.

Dependency declarations read and used:

- `def-weil-pbc-multivariate-power-series` records `MvPowerSeries` in
  `Mathlib.RingTheory.MvPowerSeries.Basic`; its definition and docstring were read
  at lines 83–87. That module also supplies variables, coefficients, algebra
  structure, and `MvPolynomial.toMvPowerSeries` (lines 821–835, read).
- `def-weil-pbc-mv-polynomial-ring` records `MvPolynomial`,
  `MvPolynomial.aeval`, and `MvPolynomial.algHom_ext`. Read the declaration and
  docstring of `MvPolynomial` in `Mathlib.Algebra.MvPolynomial.Basic` lines 80–83,
  `algHom_ext` there at lines 431–439, and `aeval` in
  `Mathlib.Algebra.MvPolynomial.Eval` lines 584–611. The statement uses the first
  two; the uniqueness clause identifies the evaluation with the canonical one.
- The sole proof dependency records `power_series_mem_combined_ideal_pow_iff` in
  `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`.
  Its full source, signature and proof docstring were read; it is imported as a
  proof dependency (plain `import`), while statement imports are public.
- Additional Mathlib APIs read: `MvPolynomial.IsHomogeneous` in
  `Mathlib.RingTheory.MvPolynomial.Homogeneous`, lines 47–50, and
  `MvPowerSeries.homogeneousComponent` / `coeff_homogeneousComponent` in
  `Mathlib.RingTheory.MvPowerSeries.Order`, lines 705–715. These provide the exact
  existing notions, so no helper definition or new node is needed.

Edge cases checked mathematically:

- `H=0`: choose `A=B=0`. The homogeneity predicate allows zero in every degree.
  The input error then has order at least r+2, and all six final conjuncts hold.
- Characteristic 2, `Q=UV`, `H=u^(r+1)`, `x=u,y=v`: choose `A=0,B=U^r`.
  The polar factors are v,u and the correction equals H exactly.
- Characteristic 2, `Q=U²+UV+V²`, same H and coordinates: the same correction
  has quadratic remainder `u^(2r)`, in p^(r+2) for r≥2.
- Characteristic zero, `Q=U²+V²`, same H: choose `A=U^r/2,B=0`; the remainder
  is `u^(2r)/4`. At r=2 this is precisely the allowed degree-4 remainder.
- At r=2 the estimates `2r≥r+2` and `r≥2` are tight. Nothing excludes this case.
  An error with order greater than r+1 gives H=0. The characteristic-2 square
  `U²+V²` is correctly excluded by its zero discriminant.

Searches actually run for this item via `msearch.py Q21 <item>`:

- LeanFinder: “A binary quadratic with nonzero discriminant admits homogeneous
  coordinate corrections raising a formal power series error by one degree”.
  Eight hits on Weierstrass preparation and elliptic curve formulas; no match.
- Loogle: `MvPowerSeries.homogeneousComponent, MvPolynomial.IsHomogeneous`.
  Successful query, zero hits.
- LeanSearch: “A nondegenerate binary quadratic admits homogeneous coordinate
  corrections improving the order of a formal power series approximation”.
  Eight hits including `MvPowerSeries.homogeneousComponent_of_order`,
  `homogeneousComponent_of_lt_order_eq_zero`, homogenization, and nondegenerate
  bilinear forms; no theorem stating this correction.
- Mathlib grep: `homogeneousComponent|polar|Morse` in `RingTheory/MvPowerSeries`.
  Sixteen hits on homogeneous components, substitution, and truncation, no match.
- Direct rg over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for
  `binaryQuadratic|binary_quadratic|quadratic.*correction|polar.*correction|lem-trf-binary-quadratic-order-correction`
  returned no matches. Broader searches for homogeneous components and quadratics
  found standard homogeneous-polynomial results and the distinct quadratic-series
  normalization module, not this correction theorem.
- Direct `grep -rn` for the item id in `lean/WeilConjectures` returned no matches.
  A full declaration-name rg in both project trees, Mathlib and the upstream name
  index also returned no matches.

The initial module compiled cleanly in both sandbox and library mode through
`scompile.py` (1.9 s and 1.8 s). The final module also explicitly imports the
recorded polynomial-ring dependency's Basic module; the delivery dry run checks
this exact final source. No statement dispute, source fault, or correction arose.

## Second reading by Q21

I reread the node's complete statement and proof against the final signature and
its source before delivery; no other agent was started, as required by the brief.
This is a separate reading pass by the same worker, not a claim of independent
review. The maintainer supplies the independent review.

The field and arbitrary characteristic, three coefficients and discriminant,
two variables and variable ideal, lower bound r≥2, both identity-linear-part
hypotheses, and error f-Q(x,y) all match their binders. In particular, the error
sign is positive f minus Q, so the witnesses must add the polar correction; the
signature uses addition in both coordinate equalities. H is the polynomial with
exactly the degree-r+1 coefficients of that error, through the actual coefficient
preserving coercion. The polar factors use u,v, while correction evaluation uses
x,y; these are distinct as required. The witnesses have degree r in the inclusive
homogeneity sense, permitting zero. All four ideal membership conclusions and
both remainder conclusions are present. The equality-bound Q,p,H and x',y'
merely express the five definitions in the node and do not introduce any further
mathematical condition. All type and universe variables are explicit. No Lean
or node mismatch was found. The only change during the pass was to add the
explicit Basic import for the recorded polynomial-ring dependency.
