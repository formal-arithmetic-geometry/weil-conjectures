## Worker report

The module `Sheaf.TraceFormula.FormalJacobianQuadraticCriterion` states the reviewed
three-way criterion. It defines the reduced formal Jacobian matrix
`MvPowerSeries.formalJacobianMatrix`, its `(n - 1)`-minor ideal
`MvPowerSeries.formalJacobianIdeal`, and the quotient image of the power-series maximal
ideal `MvPowerSeries.formalJacobianMaximalIdeal`. The theorem then states the equivalence
between (a) depth one plus equality of the Jacobian ideal with the quotient maximal ideal,
(b) a nondegenerate binary quadratic hypersurface by a complete local `F`-algebra
(`AlgEquiv`) isomorphism, and (c) the same conclusion by a ring (`RingEquiv`) isomorphism.
The theorem proof is `sorry`, as required for stage 2; its docstring records the complete
proof route from the node's ten proof steps.

The field `F : Type u` with `[Field F]` renders the base field. The natural numbers
`n s : ℕ` and `hn : 2 ≤ n` render the number of formal variables (with the required
lower bound) and the finite length of the chosen presentation. The ideal
`I : Ideal (MvPowerSeries (Fin n) F)`, the containment
`hI : I ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) F)`, the list
`f : Fin s → MvPowerSeries (Fin n) F`, and
`hgen : I = Ideal.span (Set.range f)` render respectively `I ⊆ 𝔫` and the assertion
that the displayed finite list generates `I`.

`formalJacobianMatrix F n s I f` has rows `Fin n`, columns `Fin s`, and entry
`Ideal.Quotient.mk I (MvPowerSeries.pderiv F i (f j))`; this is termwise formal
partial differentiation followed by passage to `R = T/I`. Its minor ideal is
`Matrix.minorIdeal n s (n - 1) ...`, with the empty-minor convention supplied by the
recorded minor-ideal construction. The quotient maximal ideal is the image under
`Ideal.Quotient.mk I` of `IsLocalRing.maximalIdeal T`, rendering `𝔪 = 𝔫/I`.
The first conclusion clause is
`Ideal.depth (formalJacobianMaximalIdeal F n I) (T ⧸ I) = 1` together with
`formalJacobianIdeal F n s I f = formalJacobianMaximalIdeal F n I`, exactly (a).

For (b), the theorem quantifies `a b c : F`, requires
`b ^ 2 - 4 * a * c ≠ 0`, and asks for `Nonempty` of an `AlgEquiv` from `T/I` to
`MvPowerSeries (Fin 2) F` modulo the singleton quadratic
`C a * X 0 ^ 2 + C b * (X 0 * X 1) + C c * X 1 ^ 2`. The casts `C a`, `C b`, and
`C c` are the canonical coefficient inclusions into the power-series ring. This is the
complete local `F`-algebra isomorphism clause. For (c), the same quantified
coefficients and discriminant condition are paired with `Nonempty` of a `RingEquiv`,
which deliberately forgets `F`-linearity. The final proposition is written as
`(a ↔ b) ∧ (b ↔ c)`, which is the exact meaning of the source's statement that all
three conditions are equivalent. The discriminant is retained as written and therefore
also covers characteristic two; no division by two is introduced.

Dependency declarations used:

* `def-weil-pbc-multivariate-power-series`: Mathlib
  `MvPowerSeries` in `Mathlib.RingTheory.MvPowerSeries.Basic`, with variables
  `Fin n` and coefficient field `F`.
* `def-weil-matrix`: Mathlib `Matrix` in `Mathlib.LinearAlgebra.Matrix.Defs`.
* `def-weil-pbc-matrix-determinant`: Mathlib `Matrix.det` in
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`; the module uses the project's
  canonical `Matrix.minorIdeal` construction for the generated minor ideal.
* `def-weil-pbc-depth`: `Ideal.depth` in `Sheaf.RingTheory.Depth`, with the ideal
  argument instantiated by the quotient maximal ideal and the module by `T ⧸ I`.

The module additionally imports `Sheaf.LinearAlgebra.Matrix.MinorIdeal` for the
canonical generated-minor construction and Mathlib's
`Mathlib.RingTheory.MvPowerSeries.Derivative` for `MvPowerSeries.pderiv`. The three
proof-only auxiliary nodes `lem-trf-formal-jacobian-minor-invariance`,
`lem-trf-regular-surface-depth-one-principal`, and `lem-trf-formal-binary-morse` remain
statement dependencies of the postponed proof, but have no declarations yet and are
therefore not imported into this statement-only module.

Edge cases checked: `n = 2` (the smallest permitted number of variables), `s = 0`
(empty generating list, yielding the span of the empty range), `n - 1 = 0` (the empty
minor convention), too few rows or columns, the zero Jacobian matrix, the field case
`I = ⊥`, the properness forced by `hI`, and characteristic two (where the displayed
matrix interpretation of the discriminant remains valid without dividing by 2). The
statement does not impose nontriviality, finite dimensionality, separability, or an
independent universe on the index set.

Searches made: the retained stage-1 searches in the node used `msearch.py` LeanFinder,
Loogle, grep, and LeanSearch for Jacobian-minor/Fitting-ideal criteria and found no exact
match. I additionally ran `rg -n 'derivative|deriv|pderiv|partial'` over Mathlib's
`RingTheory/MvPowerSeries` sources, finding and reading `MvPowerSeries.pderiv` in
`Mathlib.RingTheory.MvPowerSeries.Derivative`; `rg -n 'formal-jacobian-quadratic-criterion'
` over the source and project trees found no existing declaration. I read the complete
signatures and docstrings of all four recorded statement dependencies and the canonical
`Matrix.minorIdeal` declaration. No exact existing theorem was found, so a new module
was required. No statement correction, new definition node, dependency repair, or
`STATEMENT-DISPUTED` flag is needed.

## Review by Q11

I reread the node statement, its source place (Stacks Curves Tags 0C4C and 0C49), all
four statement-dependency records, and the generated Lean signature. Every source
hypothesis is present: field, `n ≥ 2`, finite presentation, ideal containment, and
finite generation. The Jacobian uses the canonical termwise `pderiv`; the ideal and
maximal ideal are formed in the quotient; and all three equivalence clauses retain the
same coefficient field and discriminant. The `AlgEquiv` clause records (b), while the
`RingEquiv` clause records the non-`F`-linear (c) clause. The smallest-variable,
empty-list, empty-minor, and characteristic-two cases elaborate and are not excluded.

Validation command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q11 lem-trf-formal-jacobian-quadratic-criterion`
completed cleanly for the module; the only postponed proof is the expected `sorry`.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
