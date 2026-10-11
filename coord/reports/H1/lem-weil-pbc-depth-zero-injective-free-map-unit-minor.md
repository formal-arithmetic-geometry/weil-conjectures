## Worker report

The module `Sheaf.RingTheory.UnitMaximalMinorOfDepthZero` states
`Matrix.exists_isUnit_maximal_minor_of_annihilator_eq_maximalIdeal`, with `sorry` as
its only proof. No definition, extra node, dependency replacement, or statement correction
is needed. Its docstring gives all five steps of the node's natural-language proof.

Hypotheses and clauses:
- The commutative ring is `{R : Type u} [CommRing R]`, with its universe explicitly bound.
- Noetherian is `[IsNoetherianRing R]`; local is `[IsLocalRing R]`, whose unique maximal
  ideal is `IsLocalRing.maximalIdeal R`. Local rings are nontrivial in Mathlib, as required
  for a proper maximal ideal.
- The maximal ideal is the annihilator of an element precisely when
  `hdepth : ∃ z : R, ∀ a : R, a * z = 0 ↔ a ∈ IsLocalRing.maximalIdeal R`.
  This is the node's explicit associated-prime witness, with no extra `z ≠ 0` hypothesis.
- Nonnegative integers are `{n p : ℕ}`. The rectangular matrix is
  `A : Matrix (Fin p) (Fin n) R`.
- The map from the finite free coordinate module `Fin n → R` to `Fin p → R` is `A.mulVec`.
  `hinj : Function.Injective A.mulVec` states exactly its injectivity. For finite index sets,
  these coordinate modules are the direct sums in the node, with their standard bases.
  No freeness hypothesis is needed for these concrete free modules.
- The first conclusion is `n ≤ p`.
- The row selection is `r : Fin n → Fin p` with `StrictMono r`, so it selects exactly `n`
  distinct rows in increasing order. The columns are all kept in order by `id`.
  `IsUnit (A.submatrix r id).det` is the asserted unit maximal minor.
- `Ideal.span {d : R | ∃ r : Fin n → Fin p, StrictMono r ∧
  d = (A.submatrix r id).det} = ⊤` is the asserted ideal-of-minors formulation.
  Both equivalent conclusions are recorded as conjuncts, so neither formulation is lost.
  In a local ring a family generates the unit ideal iff one generator is a unit: otherwise
  all generators lie in the maximal ideal. The docstring includes this converse.
- For `n = 0`, `Fin 0` is empty and has exactly one row selection, vacuously strictly
  monotone; Mathlib's determinant of this empty square matrix is one. Thus the stated
  minor and ideal clauses include the convention in the node without an extra definition.

Dependency declarations read and used:
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, explicitly imported.
- `def-weil-matrix`: `Matrix`, `Mathlib.LinearAlgebra.Matrix.Defs`, imported transitively
  through `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
- `def-weil-pbc-free-module`: `Module.Free`, `Mathlib.LinearAlgebra.FreeModule.Basic`.
  Its full signature and basis docstring were read. Here its notion is realized by the
  concrete finite coordinate modules, rather than imposing a redundant class binder.
- `def-weil-pbc-matrix-determinant`: `Matrix.det`,
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, explicitly imported. Read `det_apply`,
  whose permutation/index convention agrees with the node.
- `def-weil-submatrix`: `Matrix.submatrix`, `Mathlib.LinearAlgebra.Matrix.Defs`;
  keeping columns via `id` and selecting rows via the increasing `r` gives the node's minor.

Edge cases checked mathematically before writing: `n = 0` (empty minor one, unit ideal),
`p = 0 < n` (injectivity impossible over a nontrivial ring), `n = p` (the entire matrix),
a field (maximal ideal zero, witness `z = 1`), a local ring with zero divisors such as
`k[ε]/(ε²)` (witness `ε`), and arbitrary characteristic. No domain or field hypothesis is
added. No nonzero rank condition or characteristic restriction is imposed.

Source: the local copy of `literature/stacks-project/algebra.tex` is absent on this machine,
so read the primary source online: [Stacks Tag 00MY](https://stacks.math.columbia.edu/tag/00MY)
and [Tag 00MW](https://stacks.math.columbia.edu/tag/00MW). These give the depth-zero splitting
and the ranks/unit ideals of minors. The node's residue-field proof is an alternative route
explicitly identified in its `proof_origin`; the statement agrees with these sources.

Searches performed with `msearch.py H1 lem-weil-pbc-depth-zero-injective-free-map-unit-minor`:
- LeanFinder: "Over a Noetherian local ring whose maximal ideal is an annihilator, an
  injective rectangular matrix has a unit maximal minor". Eight results: strong rank
  conditions and square-matrix criteria over fields, no exact match.
- Loogle: `Matrix.det, Matrix.submatrix, IsUnit, Function.Injective`. Zero results.
- LeanSearch: "An injective matrix over a Noetherian local ring of depth zero has a unit
  maximal minor". Service unavailable (`Internal Server Error`); no mathematical verdict.
- Mathlib grep: `unit.*minor|minor.*unit|depth.*zero|exists.*submatrix`. Returned mainly
  unrelated seminorm matches; followed up with `minor|exists.*submatrix` in
  `LinearAlgebra/Matrix`. Thirteen results about adjugates, Bird's algorithm and principal
  minors of characteristic polynomials, none giving this statement.
- `rg` of `unit.*minor|minor.*unit|depth.*zero|lem-weil-pbc-depth-zero-injective-free-map-unit-minor`
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and repository `lean/Sheaf`.
  Results concern finite-projective-dimension modules over depth-zero rings and other depth
  statements, not the maximal-minor conclusion. The exact blueprint id has no source match.
- Exact new declaration name searched in Mathlib, WeilConjectures, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: no collision.

Server compilation via `scompile.py`: clean, 1.2 seconds, no errors or warnings.
No statement dispute or mathematical node fault was found.

## Second reading by H1

I independently read the node statement, its dependency records, the Lean module, and
Stacks Tags 00MY and 00MW. The item introduces the following objects and hypotheses, each
rendered by the displayed theorem signature:

- `R : Type u` with `[CommRing R]`, `[IsNoetherianRing R]`, and `[IsLocalRing R]`;
  this is the Noetherian local ring in the node, with no extra finiteness, domain, or
  characteristic assumption. Verdict: exact.
- `n p : ℕ` and `A : Matrix (Fin p) (Fin n) R`; this is a `p` by `n` matrix and includes
  zero dimensions. Verdict: exact.
- `hdepth : ∃ z : R, ∀ a : R, a * z = 0 ↔ a ∈ IsLocalRing.maximalIdeal R`; this is precisely
  the associated-prime/depth-zero witness `Ann(z) = m`, with no added `z ≠ 0`. Verdict: exact.
- `hinj : Function.Injective A.mulVec`; `A.mulVec` is the coordinate map from `R^n` to
  `R^p`, so this is exactly injectivity between the finite free modules. Verdict: exact.

The conclusion is rendered as the conjunction
`n ≤ p`, then an increasing row selection
`∃ r : Fin n → Fin p, StrictMono r ∧ IsUnit (A.submatrix r id).det`, and then
`Ideal.span {d : R | ∃ r : Fin n → Fin p, StrictMono r ∧
 d = (A.submatrix r id).det} = ⊤`. These are respectively the rank inequality, a unit
`n` by `n` row minor (all columns retained), and the equivalent unit ideal of all such
minors. The quantifier order and both conclusion clauses agree with the node. `Fin 0`
handles `n = 0`: the unique row map is vacuously strict-monotone and the empty determinant
is one. `p = 0 < n` is excluded by injectivity over the nontrivial local ring; `n = p`,
fields, zero divisors, and arbitrary characteristic are all covered.

I checked the dependency declarations: `IsNoetherianRing`, `Matrix`, `Module.Free`,
`Matrix.det`, and `Matrix.submatrix` are the recorded Mathlib declarations and match their
nodes. Searches with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`, plus the worker's
LeanFinder/Loogle/LeanSearch searches, found no existing declaration for this statement or
notion. The source reading of Stacks 00MY (exact depth-zero local complexes) and 00MW
(trivial-complex ranks and unit determinantal ideals) supports the stated specialization.

No mismatch was found. I changed no Lean code and no node fields; the node's `lean.statement`
is verbatim the theorem signature. The module compiled cleanly with `scompile.py` (no errors
or warnings).
