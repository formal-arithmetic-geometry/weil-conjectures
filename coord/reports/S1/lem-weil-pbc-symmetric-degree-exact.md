## Worker report

The module defines `SymmetricAlgebra.degreeMap`, the restriction of the
Mathlib symmetric-algebra map to the degree submodules from
`SymmetricAlgebra.graded_by_tensor_images`, and states
`SymmetricAlgebra.symmetric_degree_exact`. The auxiliary theorem
`degree_map_exists` supplies the degree-preservation fact used by the
restriction definition.

The ring and module hypotheses are rendered by `R : Type u`,
`M₂ M₁ M : Type v`, `[CommRing R]`, and the three pairs of
`[AddCommGroup]`/`[Module R]` instances. The maps are `a : M₂ →ₗ[R] M₁`
and `p : M₁ →ₗ[R] M`; surjectivity is `hp : Function.Surjective p`, and
exactness at `M₁` is `hker : LinearMap.range a = LinearMap.ker p`. The
positive degree is `n : ℕ` with `hn : 1 ≤ n`. The first map is represented
by the existential linear map `φ` from `M₂ ⊗[R] Sym^(n-1)(M₁)` to
`Sym^n(M₁)`, and its required formula is stated after coercion to the
ambient symmetric algebra. The second map is `degreeMap R M₁ M p n`.
Surjectivity and exactness are expressed as `Function.Surjective` and
`LinearMap.range φ = LinearMap.ker (...)`.

Dependencies used: `Sheaf.LinearAlgebra.SymmetricAlgebra.Graded`, declaration
`SymmetricAlgebra.graded_by_tensor_images`; Mathlib
`SymmetricAlgebra`, `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift`,
`SymmetricAlgebra.lift_ι_apply`, and `SymmetricAlgebra.algHom_ext` recorded
by the universal-property dependency's `mathlib_match`.

Edge cases checked: `n = 1` makes the source degree `n - 1 = 0`; `n = 0`
is excluded exactly by `hn`; zero modules are allowed; no injectivity of `a`
is assumed, matching exactness `range a = ker p`; and arbitrary universe sizes
are retained by explicit `u` and `v`.

Searches made: the node's recorded LeanSearch, Loogle, LeanFinder, and grep
searches found no exactness theorem for symmetric powers. Repository searches
(`rg` over `WeilConjectures` and `lean/Sheaf`) found no existing declaration
for this lemma. Mathlib's symmetric algebra declarations were inspected in
`Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`; only the universal
property is available.

## Earlier second reading (a previous round; superseded)

Reading the node and file together: all module, exactness, and positivity
hypotheses occur verbatim in Lean. The degree submodules are exactly the
images of powers of `TensorAlgebra.ι` under `SymmetricAlgebra.algHom`, as in
the grading dependency. The canonical algebra map is `lift ((ι R M).comp p)`;
`degreeMap` is its restriction. The existential first map has the stated
formula on pure tensors, and the final two clauses state surjectivity and
kernel=image exactness. No hypotheses or conclusion clauses were changed.

## Second reading by S1

I read the node statement against `DegreeExact.lean` and its dependency declarations. The objects are rendered by `R`, `M₂`, `M₁`, `M`, the commutative-ring and module instances, and linear maps `a` and `p`. The hypotheses `p` surjective, `range a = ker p`, and `1 ≤ n` are present exactly; no injectivity, finiteness, characteristic, Noetherian, or universe restriction is added. The degree pieces are the mapped powers of `TensorAlgebra.ι` under `SymmetricAlgebra.algHom`, matching the graded dependency. `degreeMap` is the restriction of `SymmetricAlgebra.lift ((ι R M).comp p)`, and the existential first map has the required pure-tensor formula. The conclusion gives surjectivity and `range φ = ker (degreeMap)`, and now also states uniqueness of `φ` among maps satisfying that formula, as required by the node.

The edge cases checked are `n = 1` (source degree zero), exclusion of `n = 0` by `hn`, zero modules, empty submodules, arbitrary explicit universes, and arbitrary characteristic. No mismatch remains after repair. The earlier Lean statement omitted the node's uniqueness clause; I added an explicitly typed uniqueness conjunct and updated the node's verbatim `lean.statement`. I also expanded the theorem docstring with the node proof steps. Searches recorded in the worker report and node (LeanSearch, Loogle, LeanFinder, Mathlib/project grep) found no existing exactness declaration.
