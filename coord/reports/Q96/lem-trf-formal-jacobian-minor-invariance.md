## Worker report

The module `Sheaf.RingTheory.FormalJacobianMinorInvariance` states
`MvPowerSeries.formalJacobian_minorIdeal_invariance`, with its sole proof `sorry`.
Source read: Stacks Project `curves.tex`, Tag 0C4B,
`lemma-fitting-ideal-well-defined`, the statement and both proof paragraphs.
The node statement is unchanged. No new definitions or dependency repairs are needed.
The existing, landed node `def-trf-minor-ideal` is added to `stmt_deps` because
its actual definition is used rather than duplicated.

Hypotheses and clauses, matched individually:

- A field F: `(F : Type u) [Field F]`, with explicit universe `u`.
- Nonnegative n, r and finite generating-list length s: `(n s r : ℕ)`.
- T = F[[x_1,...,x_n]]: `MvPowerSeries (Fin n) F`. Its standard variables
  are `MvPowerSeries.X`. The Mathlib definition is the coefficient family
  `(Fin n →₀ ℕ) → F`, with its Cauchy-product algebra structure.
- An ideal I contained in the variables' ideal: `I : Ideal ...` and
  `hI : I ≤ Ideal.span (Set.range (X : Fin n → ...))`.
- A finite generating list of I: `f : Fin s → ...` and
  `hf : Ideal.span (Set.range f) = I`. This already certifies finite generation;
  there is no additional arbitrary generating set or stronger finiteness condition.
- Termwise derivatives: `pderiv F i (f j)`. Read Mathlib's full definition:
  coefficient at d is `coeff (d + Finsupp.single i 1) (f j) * (d i + 1)`.
- The quotient Jacobian: `fun j i ↦ Ideal.Quotient.mk I (pderiv F i (f j))`.
  Its rows index generators j : Fin s and columns index variables i : Fin n,
  exactly the orientation fixed by the node's proof and the source display.
- The r-minor ideal: `Matrix.minorIdeal s n r` of that matrix. Its actual
  definition is the ideal span of determinants selected by increasing row and
  column subset embeddings. The unique zero-size minor is 1, hence D_0 is top;
  if either dimension is too small the indexing type is empty, hence D_r is bottom.
- Independence from the generating list: the first conjunct quantifies over every
  length l and every `g : Fin l → ...` with `Ideal.span (Set.range g) = I`, and
  equates the two ideals in the SAME ring `MvPowerSeries (Fin n) F ⧸ I`.
- Every replacement regular parameter list: the second conjunct quantifies over
  `y : Fin n → ...`, and uses the recorded dependency predicate
  `IsLocalRing.IsRegularSystemOfParameters (List.ofFn y)`.
- Using the F-algebra coordinates T = F[[y]]: the algebra equivalence
  `e : MvPowerSeries (Fin n) F ≃ₐ[F] MvPowerSeries (Fin n) F` satisfies
  `∀ i : Fin n, e (X i) = y i`. This is the coordinate isomorphism, not an
  arbitrary Jacobian map or an assumed chain rule. The domain's formal variables
  represent Y_i. Every regular parameter system has such coordinates, as confirmed
  by the existing `MvPowerSeries.exists_algEquiv_full_parameters_field` in
  `Sheaf.RingTheory.PowerSeriesFullCoordinatesField` (read its signature and
  docstring). Coordinates are already stipulated in the node; their isomorphism
  is represented explicitly, with no continuity or characteristic restriction.
- Differentiating the SAME elements of I in the new coordinates:
  `e (pderiv F i (e.symm (f j)))` first expresses f_j in the y coordinates,
  differentiates there, and returns to T. Reduction still uses `Ideal.Quotient.mk I`.
  The second equality is therefore equality of ideals in the original quotient;
  it does not move I by e or differentiate y_j instead of f_j.
- The conjunction gives both independent changes; their simultaneous application
  follows by applying the generator clause and then the coordinate clause.

Dependency declarations read and reused:

- `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries` (through the derivative import).
- `Mathlib.LinearAlgebra.Matrix.Defs`, `Matrix` (through the minor-ideal import).
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, `Matrix.det` (used by `Matrix.minorIdeal`).
- `Sheaf.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters`: maximal-ideal generation and length = Krull dimension.
- `Sheaf.LinearAlgebra.Matrix.MinorIdeal`, `Matrix.minorIdeal`:
  the existing node `def-trf-minor-ideal`, whose source and complete definition were read.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`, `MvPowerSeries.pderiv`:
  the existing termwise derivation (no helper copy).
- `Mathlib.RingTheory.MvPowerSeries.Inverse` and `.Equiv` provide the local and
  Noetherian instances needed to use the recorded parameter predicate on T.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Ideal.Quotient.mk`, is the quotient ring map.

Proof-plan imports: `WeilConjectures.LinearAlgebra.Matrix.CauchyBinet`
(`Matrix.cauchy_binet`, read through `scompile.py --source`, since the old local
upstream checkout lacks this published source) and
`Sheaf.LinearAlgebra.Matrix.MinorIdealInclusions` (`Matrix.minorIdeal_inclusions`,
full source read). `lem-trf-formal-jacobian-coordinate-chain-rule` currently has
no recorded Lean module, so it cannot yet be imported; its use and full role are
in the theorem's proof docstring. It is a proof prerequisite, not a missing
notion needed to type this statement.

Edge cases checked before writing:

- n = 0: T is F, the variables' ideal is zero, I is zero, parameter lists and
  matrices have no columns. D_0 = top and all positive-size minor ideals = bottom.
- s = 0 or l = 0: the corresponding span is zero. When only one list is shorter
  than r, the other positive-size minors vanish by Cauchy--Binet's empty sum,
  not merely by the definition's oversized convention.
- r = 0: the empty determinant contributes 1 on both sides, for every list.
- r greater than n or the number of rows: the appropriate minor index is empty.
- I = zero: generators are zero; the positive-size Jacobians vanish.
- Repeated or zero generators and arbitrarily long lists remain covered.
- Identity coordinates, permutations, y = x + x², and y = x + x^p in characteristic p
  are included. In characteristic p, p is the field's natural-number cast in
  the termwise derivative, so no characteristic-zero premise is implicit.
- A coordinate map need not preserve I: we transport the derivative, not I;
  reducing the differentiated same f_j modulo I is the intended construction.
- The finite index types are universe zero and the coefficient field has arbitrary
  explicit universe u; no small-universe quantification over test objects is used.

Searches for an existing statement:

- `msearch.py leanfinder`, query "Jacobian minor ideals of formal power series independent
  of generators and coordinates": eight hits, all polynomial submersive-presentation
  Jacobian constructions, not this formal minor-ideal invariance theorem.
- `msearch.py loogle`, query `MvPowerSeries.pderiv, Matrix.minorIdeal`:
  no hits; the service does not know the project declaration `Matrix.minorIdeal`.
- `msearch.py leansearch`, query "Formal power series Jacobian minor ideal independent
  of generators and regular parameters": eight hits, polynomial Jacobians,
  univariate maximal-ideal facts and power-series topology, no exact match.
- `msearch.py grep`, query `jacobian.*(minor|invar)|minor.*jacobian`:
  no Mathlib hits.
- `rg` of Mathlib for `def pderiv|theorem coeff_pderiv` found the genuine formal
  derivative in `RingTheory/MvPowerSeries/Derivative.lean`, which is used.
- `rg` of the upstream `WeilConjectures` source and project `lean/Sheaf` for
  `pderiv|formalPartial|partialDeriv|coordinateDeriv|formalJacobian|minorIdeal`
  found polynomial derivatives, the first-order coordinate theorem and the existing
  minor-ideal modules; no invariance theorem.
- Upstream search for the item's exact node id returned no hits.
- `tools/blueprint_refs.py search 'formal Jacobian'` returned zero blueprint nodes.
- Exact-name search `formalJacobian_minorIdeal_invariance` in Mathlib,
  upstream declarations, project declarations and `dag/lean_names_upstream.json`
  returned no hits.

There is no statement dispute or correction. The theorem is stated with `sorry`;
no theorem has been proved in this stage-2 delivery.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
