## Worker report

The module `Sheaf.RingTheory.GenericLinearPerturbationJacobian` states
`MvPolynomial.GenericLinearPerturbation.exists_nonzero_parameter_polynomial`.
Its three auxiliary constructions are the displayed specialized equation, the
specified quotient, and a minor's image in that quotient. These belong to the
item's own polynomial construction and are listed in `lean.declarations`.
Every definition has real data; the sole postponed proof is the item's theorem.
No statement correction, dependency repair, or new node is needed.

Source read: `literature/stacks-project/examples-defos.tex`,
`lemma-jouanolou-type-thing` (Tag 0E7U), lines 2933–2995. The node makes the
rank-deficient incidence argument explicit as a principal parameter open and
includes the elementary empty-equation extension. Its six-step proof is included
in the theorem docstring, including the source's derivative-index correction.
The source only asserts smoothness over an open, but its proof excludes the
entire rank-deficient incidence over the generic parameter. Clearing a denominator
therefore gives exactly the stronger full-rank open recorded by this node.

Hypothesis and clause correspondence:

- A field `k`: `(k : Type u) [Field k]`.
- Nonnegative integers `c,N` with `c ≤ N`: `(N c : ℕ) (hc : c ≤ N)`.
- The `c` polynomials in `N` variables: `f : Fin c → MvPolynomial (Fin N) k`.
  Mathematical variables numbered `1,…,N` are Lean's `0,…,N-1`.
- Independent parameters indexed by `0 ≤ i ≤ N`, `1 ≤ j ≤ c`:
  `MvPolynomial (Fin (N + 1) × Fin c) k`. The row index includes the constant
  coefficient; the equation index is shifted by one from the paper.
- Existence of a nonzero parameter polynomial: `∃ H, H ≠ 0 ∧ …`.
- Every field extension with its unital map:
  `∀ (L : Type (max u v)) [Field L] (φ : k →+* L), …`.
  The arbitrary universe `v` permits larger extensions. Using `max u v` avoids
  an undersized, possibly vacuous universe for test fields; smaller presentations
  are transported by their canonical universe lift. No algebra structure or
  perfection, characteristic, infinitude, or finite-generation assumption is added.
- Every parameter tuple: `b : Fin (N + 1) → Fin c → L`.
- The open condition: `MvPolynomial.eval₂ φ (fun ij ↦ b ij.1 ij.2) H ≠ 0`.
  Evaluation uses exactly the given coefficient homomorphism.
- The specialized equations: `equation φ f b j` is
  `MvPolynomial.map φ (f j) + C (b 0 j) + ∑ i, C (b i.succ j) * X i`.
- The algebra `B`: `Quotient φ f b` is definitionally
  `MvPolynomial (Fin N) L ⧸ Ideal.span (Set.range (equation φ f b))`.
- All maximal minors of the `c × N` matrix: for each embedding
  `r : Fin c ↪ Fin N`, `minor φ f b r` is the quotient image of
  `Matrix.det (fun j l ↦ MvPolynomial.pderiv (r l) (equation φ f b j))`.
  Embeddings list distinct columns in all possible orders. Every usual increasing
  column selection occurs; reordering only multiplies a minor by a sign, so the
  generated ideal is exactly the ideal of all `c × c` minors.
- These images generate the unit ideal:
  `Ideal.span (Set.range (minor φ f b)) = ⊤` in the specified quotient.
- Smoothness of the specified spectrum map:
  `Smooth (Spec.map (CommRingCat.ofHom (algebraMap L (Quotient φ f b))))`.
  This is the canonical scalar map of the quotient's actual `L`-algebra structure.
- For `c = 0`, the choice `H = 1` is explicit: `(c = 0 → H = 1)`.
  The parameter index set is empty, so its multivariate polynomial ring is
  canonically `k`; there is one empty column embedding and `Matrix.det` gives its
  determinant `1`. The empty range of equations generates the zero ideal.
- The zero algebra is allowed: there is no `Nontrivial` binder on the quotient.
  A unit-ideal conclusion and smoothness of its empty spectrum remain meaningful.

Recorded statement dependencies used, with full definitions and docstrings read:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`; also `MvPolynomial.map`, `eval₂`, `aeval`
  and `algHom_ext` were inspected in Basic/Eval for coefficient extension and
  the universal polynomial-ring interface.
- `def-weil-pbc-polynomial-partial-derivative`: `MvPolynomial.pderiv`,
  `Mathlib.Algebra.MvPolynomial.PDeriv`.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` (including its Leibniz formula).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

`Ideal.Quotient.mk` and the canonical quotient algebra structure use Mathlib's
quotient definitions, not a separate construction. The corresponding proof
node `def-weil-pbc-algebra-hom-quotient` is already in `proof_deps`.
All recorded proof-dependency modules are imported privately unless already
needed publicly for the statement: transcendence degree and algebraic-adjoin
bound, quotient algebra, localization at primes and module localization,
standard smoothness, localization away, the nonzero maximal minor theorem,
maximal ideals, the affine smoothness comparison, smoothness on a localization
cover, and standard smooth implies smooth. Mathlib matches are imported from
the files their records name.

Edge cases checked mathematically before writing:

- `c = 0`, arbitrary `N`: `H = 1`, one empty minor `1`, polynomial affine space.
- `N = 0`: `c ≤ N` forces `c = 0`, hence the spectrum of `L` itself.
- `c = N > 0`: the minors are the square determinant with all column orders;
  the unit-ideal condition is determinant invertibility in the quotient.
- Quotient zero, e.g. one nonzero constant equation after specialization: no
  nontriviality or nonempty-spectrum condition obstructs the conclusion.
- Finite fields: nonzero `H` need not have a rational nonvanishing point; the
  theorem correctly gives a conditional assertion for each tuple and field.
- Characteristic `p` and inseparable inputs, such as `x^p`: the added linear
  coefficient contributes directly to the derivative; no separability is assumed.

Searches for an existing statement or reusable construction:

- `msearch.py … leansearch "Generic linear perturbations of polynomial equations
  have full rank Jacobian"`: eight results, all pre/submersive presentation
  Jacobian APIs, including `jacobian_isUnit` and `jacobiMatrix`; none produces
  a nonzero universal parameter polynomial for arbitrary input equations.
- `msearch.py … leanfinder "Generic affine linear perturbations of arbitrary
  polynomial equations have maximal Jacobian minors generating the unit ideal
  over every field extension"`: eight results, again pre/submersive presentation
  APIs. These start with a standard-smooth presentation or an invertible Jacobian.
- `msearch.py … loogle "MvPolynomial.pderiv, Matrix.det"`: zero hits.
- `msearch.py … grep "perturb|jouanolou|smoothing" RingTheory`: zero hits.
- `rg -n 'perturb|jouanolou|generic.*[Jj]acobian|linear.*[Pp]erturb'
  lean/WeilConjectures lean/Sheaf`: unrelated power-series parameter perturbations,
  separable approximations, and the consumer `AffineCompleteIntersectionSmoothing`;
  no theorem matching this item. `grep -rn` of this item's ID in
  `lean/WeilConjectures` also found no match.
- Further `rg` searches for equation, perturbation, quotient, and minor helpers in
  the project found `MvPolynomial.AffineCISmoothing.equation`, which was read in
  full. It takes coefficients in `PowerSeries k` and fixes `PowerSeries.C`; it
  does not handle an arbitrary field `L` and its map `φ`. It is not a duplicate
  of this field-specialized construction. No reusable general perturbation helper
  or canonical maximal-minor ideal for this family was found.

## Second reading by Q38

Author's second reading, under the direct-worker protocol; independent review
is performed by the maintainer. The node and completed module were read together.
The parameter product has `(N+1)c` independent entries, constant row zero is
separate from the `N` linear rows, and `pderiv` differentiates after coefficient
extension. The determinant is formed over `L[x]` before applying the canonical
quotient map. Embeddings exclude repeated columns without excluding any minor;
permuted orders have no effect on the ideal. The quotient in the minor and the
quotient in the smoothness clause are definitionally identical. The same `H`
is quantified before all extension fields and tuples, and the nonvanishing
condition uses `φ`. The explicit `c = 0 → H = 1` clause was checked alongside
the empty determinant convention and the empty parameter index. No mismatch or
node fault was found and no correction was made. No independent second worker
is claimed by this section.
