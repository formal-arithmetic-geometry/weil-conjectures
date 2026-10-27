## Worker report

The module `Sheaf.RingTheory.FormalJacobianGeneratorMinorExpansion` states
`MvPowerSeries.formalJacobian_generator_minor_expansion`, with one `sorry` and no new
definitions. The mathematical statement and all existing dependency lists are unchanged.

Hypotheses and objects, matched to the node:

- The arbitrary field is `(F : Type u) [Field F]`, with explicitly declared universe `u`.
- The nonnegative integers `n,s,l` are `(n s l : ℕ)`. The formal power-series ring is
  `MvPowerSeries (Fin n) F`; there is no positivity or characteristic assumption.
- The arbitrary ideal is `I : Ideal (MvPowerSeries (Fin n) F)`; it need not be proper.
- The original list is `f : Fin s → MvPowerSeries (Fin n) F` and membership is
  `hf : ∀ b : Fin s, f b ∈ I`. No generation hypothesis is imposed.
- The coefficient matrix is `C : Matrix (Fin l) (Fin s) (MvPowerSeries (Fin n) F)`.
  Every occurrence of the new list entry `g a` is expanded as `∑ b : Fin s, C a b * f b`.
- The derivative is exactly `MvPowerSeries.pderiv F i`, and the quotient homomorphism
  is `Ideal.Quotient.mk I`. The quotient ring is inferred from this map.
- The quotient Jacobians are written entrywise using `Matrix.of`, with list entries as
  rows and variables as columns. The coefficient residue matrix is `C.map (Ideal.Quotient.mk I)`.

Conclusions, matched clause by clause:

- The first conjunct quantifies over every `a : Fin l` and `i : Fin n` and states the
  full derivative identity, including the second sum `∑ b, pderiv F i (C a b) * f b`.
- The second conjunct is equality of the new quotient Jacobian with the residue matrix
  multiplied by the old quotient Jacobian. It is a matrix identity, not just an ideal containment.
- The final conjunct quantifies over every `r : ℕ`, `A : Finset (Fin l)`,
  `B : Finset (Fin n)`, `hA : A.card = r`, and `hB : B.card = r`.
  The selected minor is formed using `Matrix.submatrix`, and the determinant is `Matrix.det`.
  `A.orderEmbOfFin hA` and `B.orderEmbOfFin hB` list the selected indices increasingly.
  The right hand sum ranges over precisely `{S : Finset (Fin s) // S.card = r}`.
  Each `S.val.orderEmbOfFin S.property` increasingly selects the same columns of the
  residue coefficient matrix and rows of the old quotient Jacobian. The two determinants
  are multiplied in the order given by the node. `Fin` replaces one-based finite indexing
  by zero-based finite indexing without changing its order or its subsets.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`.
  This dependency has a `mathlib_match`, so no replacement Lean record is needed.
- `Mathlib.LinearAlgebra.Matrix.Defs`: `Matrix`, `Matrix.of`, `Matrix.map`, `Matrix.submatrix`.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`: `Matrix.det`.
- Proof-only imports retain `Mathlib.RingTheory.Kaehler.Basic` (the recorded
  `KaehlerDifferential`, `.D`, and `.linearMapEquivDerivation`, together with the derivation
  interface) and `WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` (`Matrix.cauchy_binet`).
  Its full statement and proof were read; it applies with sizes `r` and `s` after selecting
  the outer rows and columns. No dependency interface repair is necessary.
- `Mathlib.Data.Finset.Sort` and `Mathlib.Data.Fintype.Powerset` provide increasing
  enumerations and the finite index type of cardinality-constrained subsets.
- `Mathlib.RingTheory.Ideal.Quotient.Operations` supplies the actual quotient map.

The source was read in `literature/stacks-project/curves.tex`, generator-change proof
of `lemma-fitting-ideal-well-defined` (Tag 0C4B), and `algebra.tex`,
`item-cauchy-binet` (Tag 0F0K). The theorem docstring records all four DAG proof steps
and the source for subsequent proof work.

Edge cases checked before writing: `s = 0` makes each linear combination and both
product-rule sums zero; `l = 0` or `n = 0` permits the empty matrices and leaves only
zero-size selections where appropriate. For `r = 0`, the determinant of each empty
matrix is one and the intermediate subset type has exactly the empty subset. For
`s < r`, that subtype is empty, so the same unrestricted minor formula asserts a zero
left determinant. For `r > l` or `r > n`, there are no cardinality-compatible `A,B`.
The unit ideal gives the zero quotient ring, which is permitted. All field
characteristics are included. No additional edge-case conjunct or hypothesis is needed.

Searches made through `msearch.py` on 2026-10-24:

- LeanFinder: `Jacobian of finite linear combinations of formal power series modulo an ideal
  equals coefficient matrix times Jacobian and each selected minor satisfies Cauchy Binet`.
  Eight hits, including `Algebra.SubmersivePresentation.jacobianOfHasCoeffs`,
  `Algebra.PreSubmersivePresentation.jacobiMatrix_naive`,
  `Algebra.SubmersivePresentation.sum_jacobianRelationsOfHasCoeffs_mul_relationOfHasCoeffs`,
  and `Algebra.PreSubmersivePresentation.jacobian`; none concerns the arbitrary formal
  power-series lists and ideal of this statement.
- Loogle: `MvPowerSeries.pderiv, Matrix.det`; zero hits.
- Mathlib grep: `jacob.*minor|minor.*jacob|pderiv.*det|det.*pderiv`; one hit, the
  documentation of `MvPowerSeries.pderiv.ext`, which does not state this formula.
- The same regexp was searched with `rg` in both `lean/WeilConjectures` and `lean/Sheaf`.
  Polynomial presentation results and `FormalJacobianMinorInvariance` were inspected;
  the latter concludes equality of minor ideals and does not give the current identities.
  Searching the exact item id in `lean/WeilConjectures` found no existing declaration.
- A further search for quotient Jacobians found
  `MvPowerSeries.quotientJacobian` in `FormalPowerSeriesContinuousDifferentials`.
  Its full definition is a linear map over the ideal generated by its input list;
  it is not the matrix over an arbitrary containing ideal required here. The present
  theorem simply writes the required entries, introducing no competing definition.
- The proposed declaration and module names were searched in Mathlib, the project,
  and `dag/lean_names_upstream.json`; no collision was found.

No statement dispute, correction, new node, or dependency module is needed.

Validation: `scompile.py` compiled the sandbox statement and the named library module
cleanly on the server (1.4 seconds each). The only proof is the required `sorry`.
The node record stores the final theorem signature verbatim.

The prescribed `deliver2.py --no-push` completed successfully: the three-file packet
passed server preflight and compilation. Independent statement review is left to the
maintainer, as required by the dispatcher brief; no second worker was started.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
