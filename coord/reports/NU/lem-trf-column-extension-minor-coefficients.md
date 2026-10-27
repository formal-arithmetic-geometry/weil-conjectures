## Worker report

The module `Sheaf.LinearAlgebra.Matrix.ColumnExtensionMinorCoefficients` states
`Matrix.det_submatrix_eq_sum_columnExtensionMinorCoefficient`, with proof `sorry`.
It also constructs the recursive coefficients in full as
`Matrix.columnExtensionMinorPolynomial` and `Matrix.columnExtensionMinorCoefficient`.
These are the data explicitly introduced by this item, so they belong to its module
and are all listed in `lean.declarations`. No new notion node or dependency repair
is needed. The item is unchanged outside `lean`.

Source read: Stacks Project `more-algebra.tex`, Tag 07Z7,
`lemma-ideals-generated-by-minors`, including its expansion hint. Part (2) concerns
adjoined rows; transposition gives the appended-column situation. The node provides
the agent-supplied recursive certificate rather than claiming that Stacks writes
these coefficients explicitly. The node's blueprint record identifies this as an
auxiliary calculation below `lem-trf-local-term-locality`; it is not a blueprint
unit statement. No source correction or statement dispute arose.

Hypothesis and clause correspondence:

- Nonnegative integers `p,n,r,d` are the explicit natural-number binders
  `(p n r d : ℕ)`. The commutative ring is `{R : Type u} [CommRing R]`, with
  `universe u` explicit and no characteristic, domain, or nontriviality restriction.
- The commuting entry symbols form `MvPolynomial (Fin p × Fin (n+d)) ℤ`.
  Mathlib multivariate polynomials are finite integer linear combinations of monomials.
  `Fin m` uses positions zero through `m-1`, identified with the node's one through `m`.
- The row and column selections `I,J` are maps on `Fin (r+d)` into `Fin p`
  and `Fin (n+d)`, with exactly the increasing-order hypotheses `StrictMono I`
  and `StrictMono J`. Maps from `Fin k` with strict monotonicity are precisely
  increasing lists of length `k` without repetitions.
- `U : Fin r → Fin p` and `V : Fin r → Fin n` range over finite function
  spaces, filtered by `StrictMono`. This enumerates each allowed pair once and
  excludes every non-increasing or repeated list.
- The recursion helper has a natural-number depth and actual list inputs in one
  ambient alphabet. At zero it returns `if I = U ∧ J = V then 1 else 0`.
  At depth `d+1` it sums over `a : Fin I.length`, takes the last column via
  `J.getLast?`, and multiplies the signed variable `MvPolynomial.X (I.get a,j)`
  by the depth-`d` recursion on `I.eraseIdx a.val` and `J.dropLast`.
  The exponent is `a.val + 1 + J.length`, exactly the one-based exponent
  `a+q` in the node. Both deletions retain order.
- `columnExtensionMinorCoefficient p n r d I J U V` supplies `List.ofFn`
  of these maps and embeds `V` by `Fin.castAdd d`, the inclusion of the first
  `n` columns into `n+d`. Thus its depth-zero delta is the requested delta.
- The ambient polynomial ring is held fixed throughout a recursion, representing
  the smaller-alphabet polynomial by the same expression in the larger alphabet.
  This does not add variables to its expression. On valid lists at depth `d>0`,
  removing their greatest selected column leaves column indices less than
  `n+d-1`; further recursive calls only delete more columns. `U,V` appear only
  in the terminal equality test and introduce no symbols. This implements exactly
  the alphabet inclusion specified in proof step 1, including when the greatest
  selected column was already an original column. No arbitrary map or choice is used.
- The definition is total on arbitrary lists: for positive depth with an empty
  column list it returns zero. That branch is never used for a valid positive-depth
  selection since `q=r+d>0`. This totalization imposes no theorem hypothesis.
- The matrix is `B : Matrix (Fin p) (Fin (n+d)) R`. Its first `n` columns are
  the concrete `B.submatrix id (Fin.castAdd d)`, rather than another matrix with
  an equality assumption. The left determinant is `(B.submatrix I J).det`;
  the old minor is `((B.submatrix id (Fin.castAdd d)).submatrix U V).det`.
- Evaluation is `MvPolynomial.eval₂ (Int.castRingHom R) (fun ij ↦ B ij.1 ij.2)`.
  The theorem equates the left determinant to the double finite sum of these
  evaluated coefficients times the corresponding old determinant. Thus the
  coefficients are the recursive data, not existential ideal-membership witnesses.

Dependency declarations read and used:

- `def-weil-matrix`: `Matrix`, `Mathlib.LinearAlgebra.Matrix.Defs`;
  full definition and its matrix-entry docstring read.
- `def-weil-submatrix`: `Matrix.submatrix`, same module; full signature, body,
  and reindexing docstring read. Both this and the preceding module are directly
  publicly imported, as is the determinant module below.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`; the Leibniz definition,
  `Matrix.det_apply`, and docstring read.
- `lem-trf-minor-laplace-coefficient-formula` is only a proof dependency. Its
  node has no `lean` record and no `mathlib_match` in the read repository.
  Therefore there is no module to import for it yet. The theorem docstring
  preserves the exact planned use, singleton last-column Laplace expansion;
  it does not introduce a replacement or rely on that theorem to define data.

Edge cases checked before writing:

- `d=0`: lists for `V` are included by `Fin.castAdd 0`; the delta chooses
  exactly `(U,V)=(I,J)`. The identity reduces to the original minor.
- `r=0`: there is exactly one map from `Fin 0` to each finite index type and
  both maps are strictly monotone. The old determinant is the empty determinant 1.
  The recursion expands all the way to the empty-list delta.
- `r=d=0`: the coefficient and both empty determinants are 1, even if `p=n=0`.
- `q=1,d>0`: necessarily `r=0,d=1`. The sign is `(-1)^(1+1)=1`;
  deleting the unique row and column produces empty lists and coefficient 1.
- `r=d=n=1`, `p=2`: the two row terms have signs minus and plus when expanding
  the second column, giving the usual two-by-two determinant. This also checks
  the one-based sign translation.
- `r>n` implies `r+d>n+d`, so no strictly increasing `J` exists. Similarly
  `r+d>p` forbids `I`. A missing old selection gives an empty filtered sum.
  `p=0` or `n+d=0` has the same valid empty/vacuous cases.
- Arbitrary characteristic, zero ring, and zero divisors are included, since only
  finite sums, products, integer casts, and determinant are used.

Searches made:

- `msearch.py leanfinder`: query "Iterated last column expansion recursively gives
  integer polynomial coefficients expressing minors after adjoining columns in terms
  of original minors". Eight hits, including `Matrix.det_succ_column`, its zero-column
  version, row versions, cofactor comparison, and adjugate primitives. No iterated
  recursive coefficient identity.
- `msearch.py loogle`: `Matrix.det, MvPolynomial`. Five hits, including
  `Matrix.eval_det_mvPolynomialX`, `Matrix.det_mvPolynomialX_ne_zero`, and Jacobian
  polynomial lemmas. None provides these coefficients or this identity.
- `msearch.py leansearch`: "Repeated column expansion expresses larger minors as
  sums of smaller minors with recursively specified integer polynomial coefficients".
  Eight determinant expansion/adjugate/update-column hits; no match.
- `msearch.py grep`: `minor.*(append|adjoin)|cofactor.*recurs|det_succ_column`.
  Four hits in determinant Basic and Bird Correctness; one-step expansion only.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for column-extension/minor-coefficient phrases and all three proposed declaration
  names. Related Fitting, Plucker, and Popescu modules do not state this result;
  none of the proposed declaration names exists. Searching the exact node id in
  upstream and Sheaf sources found no declaration.

Validation: the prescribed `scompile.py` compiled the sandbox and library module
cleanly on the server, each below two seconds, with no diagnostics. Both coefficient
definitions are `noncomputable` only because Mathlib's polynomial semiring instance
is noncomputable; their mathematical data is the fully specified recursion and
contains no postponed proof. The sole postponed theorem is the item's own statement,
with the complete four-step natural-language proof in its docstring. No file-local
notation, private helper, extra axiom, or implicit universe is used.

## Second reading by NU

No second reading by another worker was performed: the dispatcher brief requires
this worker to deliver directly and forbids starting other agents. The maintainer's
independent review reads the delivery. The clause correspondence and edge cases above
are this worker's own checks, not an independent review.
