## Worker report

The module `Sheaf.RingTheory.TorsionCyclicPresentation` states
`Ideal.exists_torsion_cyclic_presentation`, with its proof `sorry`. No definitions,
new nodes, dependency modules, or statement corrections are needed.

The source was opened at https://stacks.math.columbia.edu/tag/05E8 (the local literature
checkout is absent). Its proof's first two sentences give exactly this surjection from
cyclic ideal-power quotients and its ideal-power torsion kernel. The module docstring
carries all four steps of the node's natural-language proof and their dependencies.

Hypotheses and conclusions, clause by clause:

- A commutative ring: `{R : Type u} [CommRing R]`.
- Its ideal: `(I : Ideal R)`.
- An R-module: `(Q : Type (max u v)) [AddCommGroup Q] [Module R Q]`.
- Every q is annihilated by some positive ideal power:
  `hQ : ∀ q : Q, ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • q = 0`.
  This kills q by EVERY element of that ideal power; it is not elementwise torsion
  by a single selected scalar.
- A set J: `∃ (J : Type (max u v))`. This universe permits J = Q, as in the proof;
  it does not impose a finite or countable indexing set.
- Positive integers n_j: `(n : J → ℕ), (∀ j : J, 0 < n j)`.
- P is the indicated direct sum, not an unspecified module:
  `(⨁ j : J, R ⧸ I ^ n j)` is written directly as the domain of p.
- The presentation map is R-linear: `p : (⨁ j : J, R ⧸ I ^ n j) →ₗ[R] Q`.
- Surjectivity: `Function.Surjective p`.
- K is its actual kernel: `LinearMap.ker p`; no unrelated existential submodule.
- K is ideal-power torsion:
  `∀ k : LinearMap.ker p, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ I ^ m, a • k = 0`.
  Here the scalar multiplication and zero are in the kernel submodule.
- The resulting sequence with the inclusion is short exact:
  `p.shortComplexKer.ShortExact`. Reading `LinearMap.shortComplexKer` in Mathlib confirms
  that its maps are `ModuleCat.ofHom (LinearMap.ker p).subtype` and `ModuleCat.ofHom p`.
  `ShortExact` requires exactness, a monomorphic inclusion and an epimorphic p, precisely
  the node's sequence including the zero endpoints.

Universes `u v` are explicitly bound. Q and J share `max u v`, allowing both ring
quotients and Q in the same `ModuleCat` universe. Any ring and module can be viewed in
such a common universe; there is no cardinal restriction. There are no auto-bound
variables, file-local definitions, instances or notation, or `let` binders.

Dependency declarations read and used:

- `def-weil-pbc-direct-sum-modules` is Mathlib: `DirectSum` in
  `Mathlib.Algebra.DirectSum.Basic`, and its module instance in
  `Mathlib.Algebra.DirectSum.Module`. Also read the full signatures/docstrings of
  `DirectSum.lof`, `DirectSum.component` and `DirectSum.induction_on` recorded by the node.
  The statement uses `DirectSum` and its R-module instance.
- `def-weil-pbc-quotient-module` is Mathlib: `Submodule.hasQuotient` and
  `Submodule.Quotient.module` in `Mathlib.LinearAlgebra.Quotient.Defs`.
  Also read `Submodule.mkQ`, `Submodule.mkQ_surjective` there and
  `Submodule.ker_mkQ` in `Mathlib.LinearAlgebra.Quotient.Basic`.
  `Mathlib.RingTheory.Ideal.Quotient.Defs` supplies `Ideal.instHasQuotient`, literally
  `Submodule.hasQuotient`, so R / I^n uses the recorded quotient-module notion.
- `def-weil-pbc-exact-sequence`: read the recorded
  `CategoryTheory.ComposableArrows.Exact` in `Mathlib.Algebra.Homology.ExactSequence`,
  `CategoryTheory.ShortComplex.Exact` in `Mathlib.Algebra.Homology.ShortComplex.Exact`,
  and `CategoryTheory.ShortComplex.ShortExact` in
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`.
  The applicable clause here is `ShortExact`, imported through
  `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, where the canonical kernel
  short complex is already defined. No private copy of exactness is introduced.
- `Mathlib.RingTheory.Ideal.Operations` supplies ideal powers.

Edge cases checked mathematically before writing:

- Q = 0: the empty sum and zero surjection work; its kernel is zero.
- Empty J: allowed, and a surjection then forces Q = 0.
- I = 0: n = 1 kills every module element; a direct sum of copies of R surjects onto Q.
- I = R: torsion forces Q = 0, since 1 belongs to every positive power; zero quotients
  therefore give the required zero presentation.
- The zero ring and arbitrary characteristic are permitted.
- Exponent 0 is excluded exactly as the source and node require.
- Infinite index sets are permitted; every individual sum element has finite support,
  so the kernel torsion argument does not require I to be finitely generated.

Searches made with `/home/ubuntu/weil-launcher/msearch.py`:

- Lean Finder query: `An ideal power torsion module is a quotient of a direct sum of
  cyclic quotients R/I^n with ideal power torsion kernel`. Eight hits: primary torsion
  decompositions over Dedekind domains/PIDs, torsion of quotient modules and ideal
  quotient equivalences. None states this presentation for an arbitrary commutative ring.
- Loogle query: `DirectSum, LinearMap.ker`. One hit, `DirectSum.ker_lmap`, a componentwise
  kernel formula, not this presentation.
- Mathlib grep query: `torsion.*(presentation|surject)|shortComplex.*(ker|LinearMap)|shortExact.*ker`.
  Twenty-five hits; in particular `LinearMap.shortComplexKer` and
  `LinearMap.shortExact_shortComplexKer` give the existing canonical exact sequence
  machinery, but no cyclic torsion presentation theorem.
- LeanSearch query: `Every ideal power torsion module admits a surjective linear map
  from a direct sum of R/I^n with ideal power torsion kernel`. Service unavailable:
  Internal Server Error; no verdict inferred from this failure.
- Project/source rg query: `lem-weil-pbc-torsion-cyclic-presentation|torsion.*presentation|cyclic.*presentation`
  over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the repository's
  `lean/Sheaf`: only two unrelated cotorsion bibliography references; no matching statement.
- Name collision search: `exists_torsion_cyclic_presentation` over Mathlib, the source,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py M1 lem-weil-pbc-torsion-cyclic-presentation` compiles this module
cleanly on the server (1.4 seconds). The initial compile identified a missing import for
ideal powers; adding the used `Mathlib.RingTheory.Ideal.Operations` resolved it.
No statement disputes or node faults were found. The independent second reader will
write their own reading and deliver; this worker does not push.

## Second reading by M1

I independently read the node, its three statement dependencies, the Stacks source at
More on Algebra, Lemma 15.90.2 (tag 05E8), and
`Sheaf.RingTheory.TorsionCyclicPresentation`.

The node's objects and hypotheses match the Lean as follows. The commutative ring is
`{R : Type u} [CommRing R]`; the ideal is `(I : Ideal R)`; and the module is
`(Q : Type (max u v)) [AddCommGroup Q] [Module R Q]`. The hypothesis that every
`q` is killed by a positive power of `I` is exactly
`hQ : ∀ q : Q, ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • q = 0`.
The existential index set is `J : Type (max u v)`, with exponents `n : J → ℕ`
and `∀ j, 0 < n j`. The direct sum in the node is rendered literally by
`⨁ j : J, R ⧸ I ^ n j`, using the quotient-module and direct-sum notions recorded
in the dependencies. The map is the existential R-linear map
`p : (⨁ j : J, R ⧸ I ^ n j) →ₗ[R] Q`, and its surjectivity is
`Function.Surjective p`. The kernel is exactly `LinearMap.ker p`; the kernel torsion
clause is
`∀ k : LinearMap.ker p, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ I ^ m, a • k = 0`.
Finally `p.shortComplexKer.ShortExact` is the canonical short complex consisting of
the subtype-kernel inclusion and `p`, and so expresses precisely the node's short
exact sequence with the inclusion `K → P`.

No hypothesis is added or omitted, and no conclusion is weakened or strengthened.
The shared `max u v` universe permits arbitrary modules and index sets (including
`J = Q`) without imposing finiteness or countability. Empty `J` is allowed; then a
surjection forces `Q = 0`. The zero module, zero ideal, unit ideal, zero ring,
arbitrary characteristic, and exponent-zero edge cases are covered: exponents are
explicitly required positive, while no assumption of finite generation of `I` or
`J` occurs. Infinite direct sums are allowed. The source page states the stronger
resolution lemma, but its first proof step is exactly the canonical presentation and
torsion-kernel statement isolated by this DAG node, so the node's stated source place
is appropriate.

For the one-definition check, I searched the source repository and Mathlib with
`rg` for `exists_torsion_cyclic_presentation`, `torsion.*presentation`, and
`I-power torsion`, and searched the DAG declarations. The only relevant Mathlib
notion found is the general torsion infrastructure (`Ideal.primaryComponent`), not
this presentation theorem. The canonical `LinearMap.shortComplexKer` and
`shortExact_shortComplexKer` are used directly; no private exactness definition is
introduced. The source checkout contains no declaration of this theorem. These
searches agree with the worker's LeanSearch/Loogle/LeanFinder results, which found no
matching presentation theorem.

I found no mismatch and made no changes to the module or node. The module compiles
cleanly with `scompile.py`; its only proof hole is the required theorem `sorry`.
