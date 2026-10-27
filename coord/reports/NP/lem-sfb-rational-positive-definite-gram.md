## Worker report

The delivery states `Matrix.exists_sum_mul_self_of_rat_posDef` in
`Sheaf.LinearAlgebra.RationalPositiveDefiniteGram`. Its sole proof is `sorry`.
No definition, new node, dependency repair, or statement correction is needed.
Only `lean` changes in the item node. The accepted stage-1 split remains intact.
The inherited BLOCKED report concerned a stage-1 unchanged-item submission; the
current queue lists this item at stage 2 and its base node has no Lean record.

Hypothesis and conclusion correspondence:

- The specified fields are the existing Mathlib types `ℚ` and `ℝ`, with
  `Rat.instField` and `Real.instField`. No variable field or alternative embedding
  is substituted for them.
- The nonnegative integer dimension is `{n : ℕ}`. `Fin n` simply relabels the
  indices 1 through n, and includes the empty case.
- The rational n-by-n matrix is `(H : Matrix (Fin n) (Fin n) ℚ)`.
- Symmetry is `(hH : H.IsSymm)`. By `Matrix.IsSymm.ext_iff`, this says
  `∀ i j, H j i = H i j`, equivalent to the node's symmetric entry condition.
- Its entrywise real image is `H.map (fun x : ℚ ↦ (x : ℝ))`.
- Positive definiteness is `hpos : (H.map ...).PosDef`. I read the full
  definition in Mathlib/LinearAlgebra/Matrix/PosDef.lean:161 and the finite-index
  equivalence `Matrix.posDef_iff_dotProduct_mulVec` at line 426. On the finite
  index set `Fin n`, finitely supported vectors are precisely all vectors.
  Real conjugation is the identity, and expanding dot product and matrix-vector
  multiplication gives exactly the node's strict double-sum inequality for
  every nonzero real vector. The included Hermitian condition follows from
  `hH` after the real cast, so it adds no mathematical restriction.
- The asserted nonnegative integer is `∃ (r : ℕ)`; the family of rational vectors
  is `(v : Fin r → Fin n → ℚ)`. Its size is arbitrary, not required to equal n.
- The entire entrywise conclusion is
  `∀ i j : Fin n, H i j = ∑ k : Fin r, v k i * v k j`.
  Both sides are rational. No equality only after casting is used.
- For `r = 0`, the sum over `Fin 0` is empty, exactly as specified.

Dependency declarations read and used:

- `def-weil-field` has status `mathlib`, with match `Field`. Its docstring and
  full signature are in `Mathlib.Algebra.Field.Defs`. The concrete instances
  `Rat.instField` (`Mathlib.Algebra.Field.Rat`) and `Real.instField`
  (`Mathlib.Data.Real.Basic`) were read. They arrive through the statement imports.
- The proof dependency `lem-sfb-rational-symmetric-form-orthogonal-basis` has
  status `mathlib`, with match `LinearMap.BilinForm.exists_orthogonal_basis`
  (`Mathlib.LinearAlgebra.QuadraticForm.Basic`, lines 1336–1343). I read its full
  signature, surrounding finite-dimensional hypotheses and docstring. It applies
  over ℚ since 2 is invertible. `Mathlib.LinearAlgebra.Matrix.PosDef` already
  publicly imports that module, so no additional import is needed.
- `Matrix.IsSymm` from `Mathlib.LinearAlgebra.Matrix.Symmetric` and `Matrix.PosDef`
  from `Mathlib.LinearAlgebra.Matrix.PosDef` are the existing notions used here.

Source and proof: I read the item, its entire four-step agent proof, and its
orthogonal-basis dependency. I opened Milne's local PDF at PDF pages 83–84
(printed pages 77–78), II §1, proof of Lemma 1.3. As the node explicitly says,
Milne motivates the split real algebra argument but does not assert this matrix
lemma. The declaration docstring records all four steps: handle n=0; diagonalize
rationally and establish positive diagonal coefficients using real positivity;
express a positive rational a/b as ab copies of (1/b)^2; enumerate the repeated
rational vectors and compute every entry. The source is not misrepresented as
containing a rational Gram theorem.

Edge cases checked before writing:

- n=0: symmetry and positivity are vacuous; choose r=0, the unique empty family,
  with no entry equalities to check. There is no `Nonempty (Fin n)` assumption.
- n=1, H=[2]: two copies of (1) give the desired factorization; a rational square
  factor alone would fail. The statement correctly permits r different from n.
- n=1, H=[1/2]: two copies of (1/2) give 1/2.
- H=[[2,1],[1,2]]: two copies of (1,1/2) and six copies of (0,1/2)
  give all four entries.
- A zero matrix in positive dimension fails the positivity hypothesis; no
  nondegeneracy assumption or eigenvalue data is added separately.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder`, query "Every positive definite rational symmetric
  matrix is a finite sum of outer products of rational vectors": eight hits,
  including `Matrix.PosDef.intCast`, `.one`, `.natCast`,
  `Matrix.PosDef.of_toQuadraticForm'`, and `LDL.diag`. These are special cases,
  positivity bridges, or real/complex decompositions, not the rational theorem.
- `msearch.py ... loogle`, query `Matrix.PosDef, IsSumSq`: zero hits.
- `msearch.py ... leansearch`, query "Every positive definite quadratic form over
  the rationals is a sum of squares of rational linear forms": eight hits,
  including `QuadraticMap.basisRepr_eq_of_iIsOrtho`, `QuadraticMap.PosDef`,
  `IsSquare.isSumSq`, and `Nat.sum_four_squares`. None gives the full rational
  matrix assertion directly.
- `msearch.py ... grep`, query `PosDef|vecMulVec` in `LinearAlgebra/Matrix`:
  25 displayed hits, including outer-product identities and positivity results,
  with no rational outer-square existence theorem.
- Direct `rg` in Mathlib linear algebra, `lean/WeilConjectures`, and `lean/Sheaf`
  for rational Gram/positive-definite and sum-of-outer-square patterns found no
  existing exact statement. Direct node-id search in `lean/WeilConjectures`
  found no declaration. Searching the chosen full declaration name in Mathlib,
  both source trees, and `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py NP lem-sfb-rational-positive-definite-gram` compiled both
its sandbox module and `Sheaf.LinearAlgebra.RationalPositiveDefiniteGram` cleanly
on the live server (3.6 s and 3.3 s). No diagnostics were emitted. All variables
are explicitly bound; there are no universe parameters or file-local notions.
No statement dispute or node fault was found.

## Second reading by NP

This is the submitting worker's second reading, not a claim of independent
review; the dispatcher brief reserves independent review for the maintainer
and prohibits starting other agents. I reopened the node and module and checked
n and r are natural numbers including zero, H and all output vector coordinates
are rational, symmetry is retained, positivity is tested on the real entrywise
image, and every pair of entries has the exact rational finite-sum equality.
The Hermitian component of Mathlib positivity is already implied by rational
symmetry and real casting. No dimensional bound on r, arbitrary field, rational
square root, stronger conclusion, or extra hypothesis appears. The docstring
contains the full agent proof and distinguishes the auxiliary from Milne's
motivating result. No mismatch was found and no source statement was changed.
