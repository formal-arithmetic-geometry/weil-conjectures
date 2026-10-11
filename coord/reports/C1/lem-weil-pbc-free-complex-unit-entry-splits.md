## Worker report

The module `Sheaf.Algebra.Homology.UnitEntrySplits` states
`ChainComplex.exists_splitting_of_isUnit_entry`, with its only proof `sorry`.
No definitions, dependency modules, or new nodes are needed. The node is unchanged except for
its `lean` field.

Source checked: Stacks Project, Algebra, Lemma 10.102.2, Tag 00MT,
https://stacks.math.columbia.edu/tag/00MT (statement and proof). The local literature path named
by the node is absent on this machine, so the source was opened online. The source presents
free modules with chosen basis sizes `n_j`; these sizes are retained, rather than using a
canonical rank that would fail for the zero ring. This is a rendering of the source's ranks,
not a new nontriviality hypothesis or a statement correction.

Hypotheses and clauses, matched individually:

- The commutative ring is `{R : Type u} [CommRing R]`.
- The integer-indexed chain complex is `C : ChainComplex (ModuleCat.{max u v} R) ℤ`.
  `C.d i (i - 1)` is its differential; the complex structure includes its shape and
  square-zero condition. There is no boundedness or exactness assumption.
- Every term is finite free: `n : ℤ → ℕ` and
  `b : ∀ j : ℤ, Module.Basis (Fin (n j)) R (C.X j)` give finite bases.
  This uses the recorded free-module notion: a basis is exactly the witness for
  `Module.Free.exists_basis`, and `Module.Free.of_basis` converts a basis to freeness.
  Specifying chosen bases introduces the coordinates that the node's hypothesis already uses.
  Every finite basis can be reindexed by a `Fin n`.
- The selected differential and its coefficient are `i`, `p : Fin (n i)`,
  `q : Fin (n (i - 1))`, and
  `hunit : IsUnit ((b (i - 1)).repr ((C.d i (i - 1)).hom (b i p)) q)`.
  `repr` computes the target coordinate of the image of source basis vector `p`.
- The complementary complex and identity complex exist as `∃ (C' T : ChainComplex ...)`.
- Every complementary term is finite free: `∀ j, Nonempty (Module.Basis (Fin (n' j)) R
  (C'.X j))`, for the existential sizes `n'`.
- The sizes decrease by exactly one in the selected degrees:
  `n' i + 1 = n i` and `n' (i - 1) + 1 = n (i - 1)`.
  Existence of `p` and `q` ensures that the corresponding original sizes are positive.
- All other sizes stay the same:
  `∀ j, j ≠ i → j ≠ i - 1 → n' j = n j`.
- `T` is zero in every other degree:
  `∀ j, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j)`.
  An additive group with one element is a zero module; no arbitrary vanishing map is used.
- The two terms of `T` are copies of `R`: `e : T.X i ≃ₗ[R] R` and
  `f : T.X (i - 1) ≃ₗ[R] R`. The equation
  `∀ t, f ((T.d i (i - 1)).hom t) = e t` says its differential is the identity on `R`
  under these identifications. All other adjacent differentials are zero because their source
  or target is a zero module. Degrees `i` and `i - 1` are distinct for every integer `i`.
- The binary direct sum is the recorded `DirectSum`, indexed by `Bool`.
  The local abbreviation `M j s` selects `C'.X j` at `false` and `T.X j` at `true`.
  It abbreviates a family of existing bundled modules, defining no new notion.
- The isomorphism is `ψ : ∀ j, (⨁ s : Bool, M j s) ≃ₗ[R] C.X j`.
  A linear equivalence is exactly a linear bijection with its inverse supplied.
- The last equation states compatibility with differentials on
  `DirectSum.lof ... false x + DirectSum.lof ... true t`, for all `x` and `t`.
  Its right side inserts `d' x` and `d^T t` in those same summands, so the sum differential
  is precisely componentwise. Every element of a direct sum over `Bool` is this sum of its
  two components (finite support imposes no extra restriction on a finite set).
  Thus this equation is the node's commuting-square condition on every element, not merely
  on a subset. Its inverse also commutes, giving an isomorphism of complexes.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`,
  `Module.Free.exists_basis`, `Module.Free.of_basis`, and the actual `Module.Basis` witness.
  The record is usable; no duplicate freeness predicate is introduced.
- `def-weil-pbc-direct-sum-modules`: its Mathlib match is
  `Mathlib.Algebra.DirectSum.Basic` / `Mathlib.Algebra.DirectSum.Module`, `DirectSum`,
  its module instance, `DirectSum.lof`, `DirectSum.component`, `DirectSum.induction_on`.
  The statement uses `DirectSum` and `DirectSum.lof` literally. The dependency is a Mathlib
  leaf and requires no `lean` record repair. The signatures and docstrings were read in
  Basic.lean and Module.lean.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `ChainComplex`,
  `HomologicalComplex.X`, `.d`, `.shape`, `.d_comp_d'` supply the chain-complex structure.
- `Mathlib.Algebra.Category.ModuleCat.Basic`: `ModuleCat`, its carrier and module instances,
  and `ModuleCat.Hom.hom` supply the linear maps underlying the differentials.

Edge cases checked before writing:

- Empty bases away from the selected degrees are allowed: `Fin 0` is a valid index type.
  An empty basis in either selected degree cannot meet the unit-entry hypothesis, since
  there can then be no `p` or `q`.
- Size one at either selected degree gives a zero-size complementary basis, as required.
- The zero complex over a nonzero ring cannot supply a unit coefficient. Over the zero ring,
  finite bases with chosen positive sizes can supply the (zero) unit coefficient, and the
  statement still holds with the chosen sizes reduced by one. No use of `finrank` or
  `Nontrivial R` excludes this case.
- Integer degree zero and negative degrees are allowed; no truncation at zero is imposed.
- Arbitrary commutative rings, including rings with zero divisors and every characteristic,
  are allowed; no field, domain, local-ring, or Noetherian hypothesis appears.
- `max u v` accommodates arbitrary module universe sizes while also allowing copies of `R`
  as terms of `T`. No restricted index-set or ring universe creates a vacuous hypothesis.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leanfinder "finite free chain complex differential unit matrix entry
  splits off identity complex"`: eight hits, on chain-complex constructors, Dold--Kan,
  and Karoubi complexes; none states unit-entry cancellation.
- `msearch.py ... loogle "ChainComplex, IsUnit"`: zero hits.
- `msearch.py ... leansearch "chain complex unit matrix coefficient direct sum identity
  complex"`: unavailable (Internal Server Error), recorded as unavailable, no verdict.
- `msearch.py ... grep "IsUnit|unit entry|trivial complex" Algebra/Homology`: zero hits.
- `rg -n "lem-weil-pbc-free-complex-unit-entry-splits|unit.entry|add.trivial.complex|00MT"`
  in the source `WeilConjectures` and project `lean/Sheaf`: only unrelated references to
  Tag 00MT in `UnitMaximalMinorOfDepthZero.lean`; no existing splitting declaration.
- Searches for `exists_splitting_of_isUnit_entry|UnitEntrySplits` in Mathlib, source,
  project Lean, and `dag/lean_names_upstream.json`: zero hits, so the name is available.
- Additional project/source search for chain complexes and finite free complexes found only
  general homological infrastructure and bounded finite free sheaf complexes, not this lemma.

The docstring records all six proof steps from the DAG, including the triangular-basis lemma
and the free-module and direct-sum dependency IDs. Every variable and universe is explicitly
bound. No `STATEMENT-DISPUTED` issue was found.

## Second reading by C1

I independently read the sandbox node, its six proof steps, both statement-dependency
nodes, the delivered module, and the actual Mathlib declarations. No statement correction,
new definition node, or dependency module is present or needed. Verdict: the statement
renders the node and Stacks 00MT. I changed only this report; the Lean and node record are
retained.

Source: the local Stacks checkout is absent. I opened the statement and proof at
https://stacks.math.columbia.edu/tag/00MT and read the TeX at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
`lemma-add-trivial-complex`, together with the chapter conventions and the preceding
`section-complex-exact` / `situation-complex`. The chapter permits the zero ring and
requires commutative rings with identity. The preceding situation describes a bounded
complex, but 00MT independently introduces its own displayed complex and assumes no
boundedness, exactness, locality, Noetherianity, or nonzero-ring condition. The source's
numbers are chosen presentation sizes in `R^{n_j}`, which is precisely how the delivered
statement treats ranks even over the zero ring.

Object, hypothesis, and conclusion checklist (each verdict is PASS):

1. Commutative ring with identity: `{R : Type u} [CommRing R]`. No extra ring instances.
2. Integer-indexed chain complex of modules: `C : ChainComplex (ModuleCat.{max u v} R) ℤ`.
   I read `HomologicalComplex.X`, `d`, `shape`, `d_comp_d'`, and the `ChainComplex`
   abbreviation in `HomologicalComplex.lean`. Its shape permits exactly the downward
   adjacent differential; `d_comp_d` supplies the node's square-zero identities. I also
   read `ModuleCat` and `ModuleCat.Hom.hom`: the objects are modules and morphisms are
   actual linear maps, with the expected composition.
3. All terms finite free, with coordinates in finite bases: `n : ℤ → ℕ` and
   `b : ∀ j, Module.Basis (Fin (n j)) R (C.X j)`. This supplies exactly a finite basis
   at each degree. Choosing bases at unselected degrees loses no finite free complex.
   In `FreeModule/Basic.lean`, the recorded dependency `Module.Free` has field
   `exists_basis : Nonempty ((I : Type v) × Basis I R M)` and `Free.of_basis` accepts
   any basis. In `Basis/Defs.lean`, `Basis.repr : M ≃ₗ[R] (ι →₀ R)` is the unique
   finite coordinate representation. Thus this is the dependency's basis notion,
   with finite indices, rather than another freeness predicate.
4. Selected degree and invertible entry: `(i : ℤ) (p : Fin (n i))
   (q : Fin (n (i - 1)))` and
   `IsUnit ((b (i - 1)).repr ((C.d i (i - 1)).hom (b i p)) q)`.
   The expression is the target `q` coordinate of the image of the source vector `p`.
   Universal parameters with a specified unit entry give the same implication as the
   node's existential unit-entry hypothesis; no preferred entry is assumed.
5. Complement and identity summand: existential `C' T` are chain complexes over the
   same ring, in the same category and with the same integer grading.
6. Complement finite free in every degree: existential `n'` and
   `∀ j, Nonempty (Module.Basis (Fin (n' j)) R (C'.X j))`.
7. Both selected sizes decrease by exactly one: `n' i + 1 = n i` and
   `n' (i - 1) + 1 = n (i - 1)`. The entry indices force the original sizes positive;
   these equations therefore express subtraction without truncated-natural ambiguity.
8. Other sizes unchanged: `∀ j, j ≠ i → j ≠ i - 1 → n' j = n j`.
9. Summand zero elsewhere: `∀ j, j ≠ i → j ≠ i - 1 → Subsingleton (T.X j)`.
   A module is nonempty, so this is exactly a zero module, including all adjacent maps
   whose source or target lies outside the two indicated degrees.
10. Summand is `R → R` with identity differential: existential linear equivalences
    `e : T.X i ≃ₗ[R] R`, `f : T.X (i - 1) ≃ₗ[R] R`, and
    `∀ t, f ((T.d i (i - 1)).hom t) = e t`. These identify that differential with
    `LinearMap.id`; no stronger requirement on the chosen carriers is introduced.
11. Degreewise direct sums: the local `let M` selects `C'.X j` at `false` and `T.X j`
    at `true`; `(⨁ s : Bool, M j s)` is the recorded `DirectSum`. I read its
    definition `Π₀ i, β i` in `DirectSum/Basic.lean`, the componentwise module instance,
    and `lof : M i →ₗ[R] ⨁ i, M i` in `DirectSum/Module.lean`.
    The family abbreviation defines no private mathematical notion.
12. Isomorphism and every commuting square: `ψ : ∀ j, (⨁ s : Bool, M j s) ≃ₗ[R] C.X j`
    gives all linear bijections and inverses. The last equation, universally quantified
    over `j`, `x : C'.X j`, and `t : T.X j`, intertwines the original differential with
    the componentwise sum of the two differentials. Every Bool-indexed direct-sum element
    is the sum of its two inclusions, so no elements are omitted. Nonadjacent maps vanish
    by shape on both sides. Bijectivity then also gives compatibility of the inverses.
    The quantifiers choose one common splitting and all degreewise equivalences together.

Edge cases: `Fin 0` is allowed at any unselected degree. A selected empty basis cannot
supply `p` or `q`; size one leaves a size-zero complement. Over a nonzero ring the zero
complex has no unit entry. Over the zero ring a chosen positive basis size is possible,
the zero coefficient is a unit, and the splitting with sizes decreased by one is valid.
No canonical `finrank` is used. Degree zero, negative degrees, and arbitrarily unbounded
complexes are covered; `i ≠ i - 1` always holds in ℤ. Every characteristic and rings with
zero divisors are included. The universes `u v` are bound explicitly; `max u v` admits
arbitrarily large module carriers and copies of `R` (using lifts when necessary), with no
smallness hypothesis. Empty schemes are irrelevant to this purely algebraic statement.

Independent searches, using different phrasing from the worker:

- LeanFinder via `msearch.py`: `invertible coefficient differential splits contractible
  summand finite free complex` gave eight hits. These concern smooth-algebra cotangent
  retractions and Dold--Kan simplicial splittings; none states this cancellation lemma.
- Loogle via `msearch.py`: `HomologicalComplex, IsUnit` returned zero hits.
- LeanSearch via `msearch.py`: `split off a contractible rank one summand from a complex
  of free modules using an invertible differential coefficient` was unavailable with
  Internal Server Error. This is recorded as unavailable, not evidence of absence.
- Mathlib grep via `msearch.py`: `IsUnit|invertible|contractible` in `Algebra/Homology`
  found four references to contractible cones/triangles in
  `HomotopyCategory/Pretriangulated.lean`, not unit-entry cancellation.
- Direct `rg` over Mathlib homology, source `WeilConjectures`, and project `lean/Sheaf`
  for `cancel.*complex|complex.*cancel|split.*unit|unit.*split|invertible.*entry|entry.*invertible|
  00MT|lemma-add-trivial-complex` found only unrelated cancellation, cotangent/smooth
  algebra or sheaf-unit splitting, and the project's `UnitMaximalMinorOfDepthZero` source
  citations. No equivalent declaration was found. A second direct search for
  `exists_splitting_of_isUnit_entry|UnitEntrySplits` over all Mathlib, source, project Lean,
  and `dag/lean_names_upstream.json` found no existing name or statement.

H5--H9 checks: no definitions with missing data, no auxiliary proofs, and exactly one
named theorem with proof `sorry`. The module and theorem docstrings give 00MT and the
exact blueprint id. The theorem docstring covers all six node proof steps, including both
triangular basis changes, complements, incoming and outgoing differentials, and assembly
of the isomorphism. Namespaces, imports, line lengths, and explicit binders conform.
The node's `lean.statement` matches the file signature verbatim. No mismatch or disputed
statement was found, so no mathematical text was rewritten.

Validation: the supplied `scompile.py` command with the absolute sandbox module path
compiled cleanly on the server in 1.3 seconds (exit code 0), with no warnings. The first
attempt used a relative path from the read-only repository and found no file; rerunning
with the absolute sandbox path corrected the invocation, without changing any source.

## Reviewer FIX (R-fcu1041, stage 2)

The unit hypothesis is now spelled as a matrix entry, as the node's "matrix coefficient of
d_i in finite bases" and the project's matrix-entry convention ask:
`hunit : IsUnit (LinearMap.toMatrix (b i) (b (i - 1)) (C.d i (i - 1)).hom q p)`
(import `Mathlib.LinearAlgebra.Matrix.ToLin`). This is the same value as the delivered
`(b (i - 1)).repr ((C.d i (i - 1)).hom (b i p)) q` (checked: `LinearMap.toMatrix_apply`), so
the mathematics is unchanged. Checked in a scratch file: every element of the Bool-indexed
`DirectSum` is `lof false (z false) + lof true (z true)`, so the compatibility equation is the
full commuting square. All other clauses (abstract chain complex, finite bases, sizes n',
`T` zero outside i, i-1 and `R -1-> R` via `e`, `f`, linear equivalences `ψ`) were matched to the
node and kept.
