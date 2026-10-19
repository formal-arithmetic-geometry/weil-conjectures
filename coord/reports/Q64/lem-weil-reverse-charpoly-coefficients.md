## Worker report

The module `lean/Sheaf/LinearAlgebra/ReverseCharpolyCoefficients.lean` states
`LinearMap.charpoly_reverse_coefficients`. It uses the upstream basis-free reverse
characteristic polynomial `LinearMap.charpolyRev F`, which is the determinant
`det (1 - T F)` from the dependency `def-weil-reverse-characteristic-polynomial`.
The theorem has no proof beyond the required `sorry`.

The Lean rendering of each part of the node is as follows. The field and finite-dimensional
vector space are `{K : Type u} [Field K]`, `{V : Type v} [AddCommGroup V] [Module K V]
[FiniteDimensional K V]`; the endomorphism is `(F : V →ₗ[K] V)`. The dimension `n` is
rendered by `Module.finrank K V`. The polynomial `P` is rendered by `F.charpolyRev`.
Clause 1 is `F.charpolyRev.coeff 0 = 1`. Clause 2 is the conjunction
`F.charpolyRev.natDegree ≤ Module.finrank K V` and
`F.charpolyRev.coeff (Module.finrank K V) = (-1 : K) ^ Module.finrank K V * LinearMap.det F`.
Clause 3 in the invertible case is
`IsUnit F → F.charpolyRev.natDegree = Module.finrank K V ∧
F.charpolyRev.leadingCoeff = (-1 : K) ^ Module.finrank K V * LinearMap.det F`.
The noninvertible case is
`¬ IsUnit F → F.charpolyRev.natDegree < Module.finrank K V`.

The statement dependencies used are `FiniteDimensional` (Mathlib,
`FiniteDimensional`), `Module.finrank` (Mathlib, `Module.finrank`), `Polynomial` and its
coefficient/degree/leading-coefficient operations (Mathlib, `Polynomial.coeff`,
`Polynomial.natDegree`, `Polynomial.leadingCoeff`), `LinearMap.det` (Mathlib,
`LinearMap.det`), and `LinearMap.charpolyRev` (upstream module
`WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`). The latter gives the exact
basis-free reverse characteristic polynomial appearing in the node; its source docstring
states that it is the reverse of the characteristic polynomial and its source theorems
include the constant coefficient, full-degree, and leading-coefficient facts for an
invertible determinant. No private definition or extra node was introduced.

The edge cases checked were dimension zero (`charpolyRev = 1`, so the degree and constant
coefficient clauses are consistent), the zero endomorphism (singular, with degree strictly
below the dimension when the dimension is positive), the identity and a one-dimensional
nonzero scalar endomorphism (invertible, with the stated signed determinant leading
coefficient), and a nontrivial Jordan block (no semisimplicity assumption). The constant
coefficient one also ensures that `natDegree` represents the ordinary polynomial degree.

Searches for an existing full statement were made with:

* `msearch.py ... leanfinder` for the full reverse-characteristic-polynomial coefficient
  claim: hits were `LinearMap.charpoly`, `LinearMap.charpoly_monic`,
  `LinearMap.det_eq_sign_charpoly_coeff`, and unrelated eigenspace results; no full theorem.
* `msearch.py ... leansearch` for coefficients and degree of `det (1 - T F)`: hits were
  `Matrix.charpolyRev`, `Polynomial.reverse`, `Matrix.reverse_charpoly`,
  `Polynomial.coeff_reverse`, and `Polynomial.reverse_natDegree`; no full theorem.
* `msearch.py ... loogle 'Polynomial.reverse, LinearMap.charpoly'`: zero hits.
* `msearch.py ... grep 'charpolyRev|reverse_charpoly' LinearAlgebra`: Mathlib supplied
  `Matrix.charpolyRev` and `Matrix.reverse_charpoly`; no combined statement.
* `rg` over `WeilConjectures/` found the upstream definition and separate theorems
  `LinearMap.coeff_zero_charpolyRev`, `LinearMap.natDegree_charpolyRev`, and
  `LinearMap.leadingCoeff_charpolyRev`, but no theorem for the singular case or the full
  conjunction.
* `rg` over `lean/Sheaf` found no existing declaration of this item.

The module compiled cleanly with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q64 lem-weil-reverse-charpoly-coefficients
lean/Sheaf/LinearAlgebra/ReverseCharpolyCoefficients.lean`.

## Dependency modules

The dependency `def-weil-reverse-characteristic-polynomial` had only the matrix-specialized
record `Matrix.charpolyRev`, which does not itself state the basis-free endomorphism notion
used by the node. Its node copy therefore records the exact published upstream declaration
`LinearMap.charpolyRev` in module
`WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix` as an
`existing: true` repair, with the required note. No duplicate dependency declaration or
additional module was needed.

The proof-dependency declarations were also inspected: `LinearMap.charpoly`,
`Polynomial.reverse`, `Matrix.reverse_charpoly`, `LinearMap.charpoly_toMatrix`,
`LinearMap.charpoly_monic`, `LinearMap.charpoly_natDegree`,
`LinearMap.det_eq_sign_charpoly_coeff`, `Polynomial.coeff_reverse`, and
`LinearMap.isUnit_iff_isUnit_det`. Their modules are imported (directly where needed,
otherwise transitively by the upstream reverse-characteristic-polynomial module).
`Module.End.isUnit_iff` identifies `IsUnit F` with bijectivity, so the two implications
in clause 3 use precisely invertibility and its negation. The universes of `K` and `V`
are independently bound, and no characteristic or semisimplicity restriction is imposed.
There is no statement correction and no disputed clause.

## Second reading by Q64

I read the node statement and its source place before checking the Lean signature. The
objects, hypotheses, and conclusion render as follows.

* The field is `K : Type u` with `[Field K]`; the vector space is `V : Type v` with
  `[AddCommGroup V] [Module K V] [FiniteDimensional K V]`; and `F : V →ₗ[K] V` is the
  endomorphism. The independent universes preserve the node's unrestricted field and
  vector-space cases. The dimension `n` is `Module.finrank K V`.
* The polynomial `P(T) = det(1 - T F | V)` is the dependency's basis-free
  `F.charpolyRev : Polynomial K`. This is the exact upstream `LinearMap.charpolyRev`,
  whose definition is `F.charpoly.reverse` and whose source documentation identifies it
  with `det (1 - T F)`.
* Clause 1 is `F.charpolyRev.coeff 0 = 1`; this is exactly the constant-coefficient
  assertion (equivalent to evaluation at zero).
* Clause 2 is the conjunction
  `F.charpolyRev.natDegree ≤ Module.finrank K V` and
  `F.charpolyRev.coeff (Module.finrank K V) = (-1 : K)^Module.finrank K V * LinearMap.det F`.
  It gives both the degree bound and the coefficient of `T^n` in the node's order.
* Clause 3 is split into the node's two implications: `IsUnit F` implies full degree and
  the displayed leading coefficient, while `¬ IsUnit F` implies strict degree inequality.
  `IsUnit F` is the endomorphism-monoid formulation of invertibility, and the upstream
  determinant criterion supplies the equivalence used by the proof plan.

The source sentence in `sk-def-cohfamily/def-weil-smooth-proper-cohomological-family.md`,
order 2856, states constant coefficient one, degree `dim V`, and signed determinant
leading coefficient in the cohomological-finiteness context where the Frobenius operator
is invertible. The node's generic degree bound and singular alternative are the precise
linear-algebra strengthening needed to derive that source sentence; no source hypothesis
is omitted from the node's stated generic claim, and no additional hypothesis is added.

Edge cases were checked. For `Module.finrank K V = 0`, `F.charpolyRev = 1`, so the
constant coefficient and degree-zero clauses hold and every endomorphism is a unit; the
singular implication is therefore vacuous. For positive dimension, the zero map has zero
determinant and strictly smaller reverse degree. The identity and a nonzero scalar map in
dimension one satisfy the unit branch. A Jordan block requires no semisimplicity. In
characteristic two the sign simplifies but the displayed formula remains valid. Empty
index sets do not occur: the only index is the intrinsic finite basis hidden by
`FiniteDimensional`, and no universe equality is imposed.

I repeated the three required searches. `msearch.py` LeanFinder and LeanSearch queries
for the complete coefficient-and-degree theorem found only the separate charpoly and
determinant facts; Loogle found no combined theorem. Grep over Mathlib found
`Matrix.charpolyRev`, `Matrix.reverse_charpoly`, and coefficient/degree reverse lemmas,
but no basis-free combined statement. Grep over `WeilConjectures/` found the exact
upstream `LinearMap.charpolyRev` and its separate `coeff_zero_charpolyRev`,
`natDegree_charpolyRev`, and `leadingCoeff_charpolyRev` declarations, but no theorem
matching this node. Grep over `lean/Sheaf` found no duplicate declaration.

The recorded dependency `def-weil-reverse-characteristic-polynomial` was repaired in the
delivery copy: its old `Matrix.charpolyRev` match was matrix-specialized, so its `lean`
record now points with `existing: true` to the exact published
`WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix.LinearMap.charpolyRev`, with a
note explaining the interface correction. The item module itself needed no textual repair;
its signature remains verbatim equal to the node's `lean.statement`. All declarations
carry the source place and `(blueprint: lem-weil-reverse-charpoly-coefficients)` in their
docstrings, and the theorem remains intentionally unproved with its named `sorry`.

The repaired module compiles cleanly with `scompile.py`; no warnings occur other than the
allowed `sorry` declaration warning.
