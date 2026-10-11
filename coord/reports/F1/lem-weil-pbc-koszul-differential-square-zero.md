## Worker report

The module `Sheaf.Paper.KoszulDifferentialSquareZero` states that the canonical
Koszul differential selected from `ExteriorAlgebra.koszul_differential` squares to
zero.  The `D.comp D = 0` clause is the equation on the whole exterior algebra;
the second clause expresses its restriction to every homogeneous exterior power.
The binders render the commutative ring `R`, module `E`, and linear form `φ` exactly
as in the node.  `D` is the chosen unique map supplied by
`ExteriorAlgebra.koszul_differential`; the conjunction gives the square-zero
claim and its homogeneous restrictions.

The only dependency declaration used is `ExteriorAlgebra.koszul_differential`
from `Sheaf.Paper.KoszulDifferential` (the exterior algebra itself is Mathlib's
`ExteriorAlgebra` and notation `⋀[R]^n E`).  Empty degree (`n = 0`) is included;
zero modules and arbitrary commutative rings, including characteristic two, are
included by the typeclass binders.  The proof is intentionally `sorry` at stage 2.

Searches made: `msearch.py leanfinder "Koszul differential squares to zero exterior algebra"`
returned only Mathlib exterior-algebra declarations; `msearch.py loogle
"CliffordAlgebra.contractLeft_contractLeft"` returned the related contraction
lemma, which is not this exact declaration; `msearch.py grep "koszul differential
square zero" Mathlib/LinearAlgebra` returned no match.  `rg` over the project and
slopmaster2 found only `Sheaf.Paper.KoszulDifferential` and unrelated projective
space Koszul sequences.  No existing exact declaration was found.

## Earlier second reading (a previous round; superseded)

The declaration was reread against the node.  Its hypotheses bind exactly a
commutative ring, an additive module, and an R-linear map.  The chosen `D` is the
unique map from the dependency statement; the first conjunct is `D ∘ D = 0`, and
the second conjunct states the same vanishing after restricting inputs to each
`⋀[R]^n E`, including degree zero.  No hypothesis or conclusion is omitted.

## Earlier second reading (a previous round; superseded)

The declaration was reread against the node. Its hypotheses bind exactly a
commutative ring, an additive module, and an R-linear map. The chosen `D` is the
unique map from the dependency statement; the first conjunct is `D ∘ D = 0`, and
the second conjunct states the same vanishing after restricting inputs to each
`⋀[R]^n E`, including degree zero. No hypothesis or conclusion is omitted.

## Second reading by F1

The node introduces a commutative ring `R`, an `R`-module `E`, an `R`-linear
form `φ`, and the unique differential `D` supplied by
`ExteriorAlgebra.koszul_differential`.  The first conclusion clause is
`D.comp D = 0`.  The node's “in particular” clause concerns the restrictions
`d_n` for `n ≥ 1`; the Lean renders this pointwise on every
`x : ⋀[R]^(n+1) E` as `D (D (x : ExteriorAlgebra R E)) = 0`.  This is the
restriction composite after coercion, with `n+1` exactly encoding `n ≥ 1`.
The earlier file quantified over `⋀[R]^n E` for all `n`, which included the
unrequested degree-zero restriction; I changed it to `⋀[R]^(n+1) E`.

The binders impose exactly the node hypotheses and no finiteness, Noetherian,
field, characteristic, or universe restrictions.  Empty and zero modules,
`n=0` (the first positive degree in the rendered clause), and characteristic
two are covered.  The dependency declaration and exterior powers are the
recorded `ExteriorAlgebra.koszul_differential` and Mathlib's `⋀[R]^n E`; no
private notion was introduced.  Searches with `msearch.py` (LeanFinder and
Loogle queries for Koszul differential square-zero), and `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, found only the related Clifford
contraction theorem, not this statement.

The corrected module compiles cleanly with `scompile.py`; its proof remains
`sorry` as required for stage 2.  No dependency or node statement was changed.

## Reviewer fix (R-kds1155, stage 2)

The delivered statement took `D := Classical.choose (koszul_differential R E φ)`, an
untied existential that the STATE line KOSZUL forbids. The fixed statement names the
one Koszul differential, `CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E)) φ`
on `ExteriorAlgebra R E` (M1 1ca3df789, step 1 of `koszul_differential`), written out
explicitly (no `let`, which stage 3 cannot unfold). Binders unchanged (R commutative
ring, E an R-module, φ : E →ₗ[R] R); conclusion `D.comp D = 0` and, for the d_n
clause with n ≥ 1, `D (D x) = 0` for x in `⋀[R]^(n+1) E`. Mathlib's
`CliffordAlgebra.contractLeft_contractLeft` proves the pointwise identity for any Q
(checked: closes `D (D x) = 0` at Q = 0), so stage 3 is immediate.
