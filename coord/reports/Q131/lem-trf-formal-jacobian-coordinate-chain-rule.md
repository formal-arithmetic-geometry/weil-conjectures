## Worker report

The module `Sheaf.RingTheory.FormalJacobianCoordinateChainRule` defines the transported
coordinate partial derivative `coordinatePartial`, and the two Jacobian matrices
`jacobianQ` and `jacobianP`. It states `formal_jacobian_coordinate_chain_rule` with the
field `F`, arbitrary `n : ℕ` (including `n = 0`), a coordinate family `y`, an algebra
isomorphism `φ`, its coordinate equation `hφ`, and the recorded regular-system
hypothesis `hreg`. The conclusion renders the two chain-rule formulas, invertibility of
the constant Jacobian via explicit two-sided finite-sum identities over `F`, and the two
matrix inverse identities over the power-series ring. The empty case is represented by
`Fin 0`, empty sums, and empty matrices.

Dependencies used are `MvPowerSeries` from `Mathlib.RingTheory.MvPowerSeries.Basic`
(the DAG mathlib leaf `def-weil-pbc-multivariate-power-series`),
`IsLocalRing.IsRegularSystemOfParameters` from
`Sheaf.RingTheory.IsRegularSystemOfParameters`, and `Matrix` from
`Mathlib.LinearAlgebra.Matrix.Defs` (the DAG mathlib leaf `def-weil-matrix`). The
Noetherian instance for finite-variable power series is imported from
`Mathlib.RingTheory.MvPowerSeries.Equiv`.

The statement hypotheses render as follows: `F` and `[Field F]` give the field; `n` and
`Fin n` give the finite variable index including zero; `y` gives the second parameters;
`φ` is the specified `F`-algebra isomorphism; `hφ` states `φ(X_k)=y_k`; and `hreg`
uses exactly the dependency's regular-system predicate. Clause (1) is the pair of
`∀ h i` and `∀ h k` derivative equalities. Clause (2) is the existential matrix `Q₀`
whose entries are constant coefficients and whose two finite-sum products are the
identity entries. Clause (3) is the pair of finite-sum matrix inverse identities for
`jacobianQ y` and `jacobianP φ`.

Searches made before writing: `msearch.py leanfinder` for a formal power-series
coordinate chain rule (no matching algebraic theorem); `msearch.py loogle` for
`MvPowerSeries pderiv comp chain rule` (0 hits, unknown `pderiv`); `msearch.py grep`
for derivative/chain-rule names in `Mathlib/RingTheory/MvPowerSeries` (no matching
chain-rule theorem); `rg` over the project and source for the item and Jacobian names
(no existing declaration). Mathlib's `MvPowerSeries.pderiv` was inspected in
`Mathlib/RingTheory/MvPowerSeries/Derivative.lean`; substitution APIs do not state
this coordinate-change theorem.

Edge cases checked: `n = 0` is admitted by all binders and empty sums; `n = 1` has
ordinary one-variable derivatives; constant and zero series are covered by the universal
`h` binders; no characteristic restriction is introduced.

## Second reading by Q131

Independent maintainer reading of immutable delivery
`5e565964b0e80305f8db70cc8da78eae57abb563`, performed on 2026-10-18.
The worker did not perform this reading; this section replaces its placeholder.

I read the item node, all three statement-dependency nodes, the complete delivered
module, and Stacks `curves.tex:4064–4092`, label
`lemma-fitting-ideal-well-defined` (Tag 0C4B). The source explicitly invokes the
invertible Jacobian for a second regular system of parameters and the chain rule.
The node expands those omitted details. No statement correction is needed.

Hypothesis and conclusion audit:

- `{F : Type u} [Field F]` and `(n : ℕ)` render an arbitrary field and any finite
  number of variables. `MvPowerSeries (Fin n) F` is precisely the coefficient-family
  power-series ring recorded by the dependency, with its Cauchy multiplication.
- `y` is the ordered family of second parameters. `List.ofFn y` retains its order
  and length. `hreg` uses the recorded `IsLocalRing.IsRegularSystemOfParameters`:
  the list spans the maximal ideal and its length equals the Krull dimension.
  I read this definition at `Sheaf/RingTheory/IsRegularSystemOfParameters.lean:27–29`
  and checked Stacks algebra Tag 00KU, `definition-regular-local:14614–14626`.
  The Noetherian instance is inferred for finite-variable power series over a field
  (`MvPowerSeries.Equiv:217–228`), so it imposes no additional hypothesis.
- `φ` is the given F-algebra coordinate isomorphism and `hφ` fixes its images of
  the variables. This is not an arbitrary map substituted for a canonical construction:
  isomorphisms preserve the maximal ideal and all its powers; separatedness makes
  such an F-algebra isomorphism with these variable images the stated coordinate map.
- `coordinatePartial φ k h = φ (pderiv F k (φ.symm h))` is the specified transported
  termwise derivative. I read Mathlib `Derivative.lean:49–53,126–140`; the coefficient
  formula is the formal derivative in every characteristic.
- `jacobianQ y k i` is ∂y_k/∂x_i, while `jacobianP φ i k` is ∂x_i/∂y_k.
  Their row/column order agrees with the node and with Mathlib `Matrix`.
- The first two conjuncts quantify over every series and every coordinate and give
  both chain-rule formulas in the required multiplication order.
- The existential Q₀ is pinned entrywise to the constant coefficient of Q. Its next
  two clauses give Q₀ P(0) = 1 and P(0) Q₀ = 1. Thus it states invertibility over F;
  specifying P(0) as inverse follows from the node's clauses and adds no assumption.
- The last two conjuncts are entrywise QP = 1 and PQ = 1 over the power-series ring.
  They give exactly the two-sided inverse required, including the stated P.

Edge cases: `Fin 0` admits the empty family, list, matrices and sums; identities are
vacuous entrywise, and the coefficient ring identification is Mathlib's
`MvPowerSeries.isEmptyEquiv`. For n = 1 the formulas have the usual orientation.
Zero and constant series are included by the universal series binders. No nonzero
series, characteristic-zero, positivity, or extra universe assumptions occur.
As orientation/characteristic checks, y = ax with a ≠ 0 gives Q = a, P = a⁻¹;
y = x + x² in characteristic 2 gives Q = P = 1. A triangular two-variable change
y₀ = x₀ + x₁², y₁ = x₁ gives the mutually inverse triangular matrices in all
characteristics. All variables and the coefficient universe u are bound.

Searches: I independently searched the group's `lean/Sheaf`, upstream
`WeilConjectures`, and Mathlib `RingTheory/MvPowerSeries` for transported partials,
coordinate/Jacobian names, and derivative composition/substitution formulas.
The hits were the existing partial derivative API, polynomial Jacobian presentations,
and a different quadratic criterion; none duplicates this statement or these transported
coordinate helpers. Mathlib `Derivative.lean` contains no substitution chain rule.
The worker records LeanFinder, Loogle, LeanSearch and grep searches; its grep no-hit
claims for `pderiv` are not evidence of absence (the declaration exists and was read).
The actual derivative is reused, not redefined.

All three helpers have explicit data and source/blueprint docstrings. The only theorem
body is `by sorry`. The theorem docstring records polynomial truncation and separation,
the cotangent-space calculation, and the inverse identities, corresponding to all
three DAG proof steps. No hollow definition, private dependency copy, stronger
hypothesis, pro-etale substitute, or dropped enhanced-category machinery occurs.
The item and its dependencies do not appear in the route-pivot dropped list, and no
repair note for this item exists at the inspected `origin/newtargets-dag` ref.

Compiler evidence: the supplied report/packet contained no explicit per-file compile
transcript. I reproduced compilation of the exact immutable file with:

```
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q131 \
  lem-trf-formal-jacobian-coordinate-chain-rule \
  snapshot/lean/Sheaf/RingTheory/FormalJacobianCoordinateChainRule.lean
```

Exit code 0. The wrapper reported server compilation using a private overlay:
`Sheaf/Stage2/Sandbox0.lean` (1.8 s) and
`Sheaf/RingTheory/FormalJacobianCoordinateChainRule.lean` (2.2 s), with no warnings
or errors. No global build, live Lean write, or repository mutation was performed.
An initial invocation without the `snapshot/` prefix failed before compilation because
that relative file did not exist; the corrected command above compiled the intended file.

Findings and repairs: H11, the supplied second-reading section was a placeholder;
this independent reading replaces it. The missing-helper record rule also requires
recording the module's helpers in `lean.declarations`; the accompanying Lean-record
replacement lists all three and the main theorem. The recorded `lean.statement`
matches the theorem signature byte for byte. Maximum Lean line length is 83.
The Lean file and mathematical node statement require no changes.
