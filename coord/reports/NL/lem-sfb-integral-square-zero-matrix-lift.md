## Worker report

The module `Sheaf.SixFunctors.IntegralSquareZeroMatrixLift` states
`integral_square_zero_matrix_lift`.  It uses Mathlib's `Matrix` notion for
finite square matrices indexed by `Fin r`, `TwoSidedIdeal R` for the arbitrary
(unital, possibly noncommutative) ring ideal, and `I.ringCon.Quotient` for the
quotient ring of additive cosets.  No definition node was needed: the matrix
notion is the recorded Mathlib leaf `Matrix` in
`Mathlib.LinearAlgebra.Matrix.Defs`.

The statement renders the node clause by clause as follows.

* `R : Type u` with `[Ring R]` is the unital ring.  `I : TwoSidedIdeal R` is
  the two-sided ideal.  The hypothesis
  `hI : ∀ x y : R, x ∈ I → y ∈ I → x * y = 0` is exactly the square-zero
  condition for every pair of ideal elements.
* `r : ℕ` and
  `B : Matrix (Fin r) (Fin r) R` give an arbitrary finite size, including
  `r = 0`, and a square matrix over `R`.
* `D : Matrix (Fin r) (Fin r) I.ringCon.Quotient` is the chosen inverse of the
  entrywise reduction.  `B.map I.ringCon.mk'` is the entrywise quotient matrix;
  `hBD : B.map I.ringCon.mk' * D = 1` and
  `hDB : D * B.map I.ringCon.mk' = 1` say that `D` is a two-sided inverse of
  the reduced matrix.
* `C : Matrix (Fin r) (Fin r) R` is arbitrary, and
  `hC : ∀ i j, I.ringCon.mk' (C i j) = D i j` says entry by entry that it
  lifts the chosen quotient inverse.  The quotient map is surjective, so such
  lifts exist (and for `r = 0` the condition is vacuous).
* The conclusion binds `N := B * C - 1` and `P := C * B - 1`, then states
  `B * (C * (1 - N)) = 1`, `(1 - P) * C * B = 1`, and
  `C * (1 - N) = (1 - P) * C`.  Thus the common corrected matrix is the
  asserted two-sided inverse, with the displayed formulas exactly as in the
  node.

The only statement dependency is the Mathlib declaration `Matrix` from
`Mathlib.LinearAlgebra.Matrix.Defs` (the dependency node `def-weil-matrix`
records this as an existing Mathlib match).  The quotient and ideal APIs used
are Mathlib declarations `TwoSidedIdeal`, `RingCon.Quotient`, and
`RingCon.mk'`; no project declaration is duplicated.

Edge cases checked: `r = 0` (the unique empty matrix, with vacuous lift and
identity products), `I = ⊥` (the square-zero condition is vacuous and the
quotient map is an isomorphism), a noncommutative ring (the formulas preserve
factor order), and the zero ideal element pairs.  The statement imposes no
commutativity or nonzero-size assumption.

Searches for an existing declaration were made as follows.

* `msearch.py ... leanfinder "square zero two sided ideal matrix inverse lifts quotient arbitrary ring explicit correction"`: returned only dual-number, trivial-square-zero-extension, and generic matrix-ideal results; none has this arbitrary-ring quotient statement or the three formulas.
* `msearch.py ... loogle "Matrix map quotient inverse square zero ideal, TwoSidedIdeal RingCon Quotient"`: the service reported `Unknown identifier map`, so no candidate declaration was available.
* `msearch.py ... grep "square.?zero|TwoSidedIdeal|RingCon\\.Quotient" LinearAlgebra/Matrix`: found only imports and the generic `TwoSidedIdeal` matrix ideal API, with no matching lift theorem.
* `rg -n 'integral_square_zero_matrix_lift|square.zero.*matrix|RingCon\\.Quotient'` over the project and source checkouts found no existing declaration.
* The node's recorded LeanSearch, LeanFinder, and Mathlib grep searches were also checked; their candidates (`IsNilpotent.isUnit_quotient_mk_iff`, `TrivSqZeroExt.*`, and matrix inverse lemmas) require commutativity or a split extension and do not state this result.

No `STATEMENT-DISPUTED` issue or node fault was found.  The theorem proof is
left as `sorry` as required for stage 2.

## Second reading by NL

I reread the node and the complete Lean signature.  The ring, two-sided ideal,
and pairwise square-zero hypotheses are all present.  The finite index `r` and
matrix `B` use the same finite-family matrix object as `[def-weil-matrix]`.
The quotient inverse is represented by `D` together with both multiplication
identities, and `hC` is precisely the entrywise lifting condition.  The three
conclusion clauses bind exactly `N = BC - 1` and `P = CB - 1` and retain the
noncommutative multiplication order.  No hypothesis or edge case was added or
dropped, and no mismatch was found.

## Returned-delivery repair check

Return point L at immutable head `478378cf6494` reported that
`lean.declaration` was not declared in the reviewer's fixed file.  In the
retained sandbox packet the actual theorem is named
`integral_square_zero_matrix_lift`, exactly as in `lean.declaration`; its
entire signature also agrees verbatim with `lean.statement`.  The current
main-branch node has no Lean binding and the theorem module is absent there;
all non-Lean fields in the sandbox node agree with that node.  There is no
renaming to record.  The prescribed first dry run of this retained packet
passed compilation and server preflight (dry-run commit `a9f0de2308`).

The repair validation additionally imports
`Sheaf.SixFunctors.IntegralSquareZeroMatrixLift` in a separate scratch consumer
and checks `@integral_square_zero_matrix_lift`, so validation checks the public
export as well as the declaration's spelling.  The mathematical statement and
its single postponed proof are retained.  The record/file self-check also
confirms explicit binding, the sole theorem `sorry`, and the 100-column limit.

The consumer check succeeded through `scompile.py`, both in the sandbox and
in the library-context check.  Lean printed the expected complete theorem type
under the exact recorded declaration name; both files compiled without errors
or unexpected warnings.
