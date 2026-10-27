## Worker report

The module `Sheaf.Algebra.Lie.RootStringDividedAdjointTriangular` states
`LieAlgebra.root_string_divided_adjoint_triangular`, with one `sorry` and no new definitions.
The node changes only in `lean`; its natural-language statement and dependency lists are unchanged.

Hypothesis and clause correspondence:

- A finite-dimensional semisimple rational Lie algebra is `L : Type u` with `LieRing L`,
  `LieAlgebra ℚ L`, `FiniteDimensional ℚ L`, and `HasTrivialRadical ℚ L`. The last predicate
  is the exact Mathlib match of `def-wf-semisimple-lie-algebra`, not Mathlib's different
  direct-sum definition `IsSemisimple`.
- The splitting Cartan is `H : LieSubalgebra ℚ L`, `[H.IsCartanSubalgebra]`, and
  `[LieModule.IsTriangularizable ℚ H L]`. Mathlib's CartanSubalgebra docstring explicitly
  describes this pair as a splitting Cartan. No nonzero or nonempty hypothesis is added.
- The finite reduced crystallographic root system is the finite index type `I` and
  `P : RootPairing I ℚ (Module.Dual ℚ H) H` with `P.IsRootSystem`, `P.IsCrystallographic`,
  and `P.IsReduced`. `heval` makes its perfect pairing the evaluation pairing. Roots and
  coroots are `P.root` and `P.coroot`; `Δ : P.Base` provides the simple and positive roots.
- `δ : Fin r ≃ Δ.support` enumerates the simple roots. `B`, `Bh`, and `Be` say precisely
  that the simple coroots and all root vectors are the prescribed Chevalley basis of `L`.
  Together with the spanning root system, this gives the Cartan part of the basis, without
  any additional choice of a Cartan basis unrelated to those coroots.
- `he` gives the nonzero root vectors and the root-space eigenvector equation via
  `LieModule.weightSpace`. The full basis `B` also ensures that these are all root spaces:
  it decomposes `L` into the Cartan and the distinct nonzero root lines. In particular no
  independent arbitrary representation or arbitrary root system is substituted.
- `hopp` is `[e_i,e_(-i)] = h_i`, with `P.reflectionPerm i i` indexing the negative root.
  `hadd` is the sign times `chainBotCoeff + 1` formula for every root sum, and `hzero`
  is exactly the absent, nonzero root-sum clause. These are the recorded PBW conventions.
- The arbitrary total order on the positive roots is represented by an arbitrary
  `β : Fin N ≃ {i : I // Δ.IsPos i}`. On a finite set, every total order admits exactly
  this form of increasing enumeration. There is no compatibility restriction on `β`.
- `a b`, `ha hb`, `hab`, and `hbottom` are respectively the two roots, their positivity,
  rational linear independence, and absence of `b-a`. `k`, `hk`, `γ`, and `hγ` give
  `k ≥ 1` and the specified root `γ = b + k a`.
- `UniversalEnvelopingAlgebra ℚ L` is Mathlib's actual tensor-algebra quotient by the
  Lie relations. All occurrences of `e` in it use its canonical generator map `ι`.
  `Algebra.rationalDividedPower` is the dependency's existing `x^m/m!` construction.
- The single existential integer `ε` has `ε = 1 ∨ ε = -1`, followed by the divided
  adjoint identity in `L`. `ad ℚ L` is the recorded adjoint representation. Its canonical
  enveloping image is the same identity in `U`.
- This sign is chosen BEFORE `∀ n`, so the same sign works for every `n ≥ 1`.
- The alternating sum is over `Finset.range (k*n+1)`, hence precisely `j = 0,...,kn`.
  `(-1 : ℤ)^j` acts by integer scalar multiplication. The three factors retain their
  stated order, and `k*n-j` is natural subtraction only on this bounded range.
  The leading term subtracted is `ε^n • rationalDividedPower (ι ℚ (e γ)) n`.
- `t`, `c : Fin t → ℤ`, and `d : Fin t → Fin N → ℕ` give a finite integer linear
  combination of ordered monomials. `List.ofFn` followed by `.prod` multiplies their
  divided powers in exactly the order `β`; all positive roots, including exponent-zero
  factors, are represented.
- `∀ j, d i j < n` is the required strict individual bound. The exponents are natural,
  so nonnegativity is built in. The root-weight equation is
  `∑ j, d i j • P.root (β j).val = n • P.root γ`.
- For every nonzero exponent, `∃ u v : ℕ, 1 ≤ v ∧ root = u • a + v • b` gives exactly
  the required cone with nonnegative integral `u` and positive integral `v`. The fact that
  the root belongs to `R` and is positive is already built into `β`.
- Bounds, weight, and cone are required for each listed summand. This is equivalent to
  the node's conditions on nonzero coefficients: zero-coefficient summands can be deleted.
  Repetitions in a finite linear combination are permitted and can be combined.
- `t = 0` permits precisely the empty correction combination, without a nonempty binder.

Dependency declarations read and used:

- `def-wf-lie-algebra`: Mathlib `LieRing`, `LieAlgebra`, `LieSubalgebra`, and `LieAlgebra.ad`;
  source signatures/docstrings read in `Mathlib.Algebra.Lie.Basic`, `.Subalgebra`, and
  `.OfAssociative`. The statement uses the existing Lie-algebra and adjoint constructions.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` and
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`, read in
  `Mathlib.Algebra.Lie.Semisimple.Defs` and `.Basic`.
- `lem-sfb-kostant-integral-pbw`: the complete signature and proof docstring of
  `LieAlgebra.exists_kostant_integral_pbw_basis` were read in
  `Sheaf.Algebra.Lie.KostantIntegralPBW`, which is publicly imported. Its public dependency
  `Sheaf.Algebra.Lie.KostantIntegralForm` supplies `Algebra.rationalDividedPower`,
  `LieAlgebra.kostantIntegralForm`, and `LieAlgebra.kostantPBWMonomial`; their full definitions
  were read. The theorem uses the same explicit root-pairing and basis conventions.
- Proof dependency `lem-sfb-root-string-integer-interval` is Mathlib's
  `RootPairing.root_add_zsmul_mem_range_iff`, read together with its endpoint definitions
  in `Mathlib.LinearAlgebra.RootSystem.Chain`, imported privately for the proof plan.
- Proof dependency `lem-sfb-rational-pbw` has no recorded Lean statement in the read clone;
  there is consequently no recorded module to import for it. Its proof use remains
  documented in the theorem's six-step proof plan. No duplicate statement was supplied.

Edge cases checked before writing:

- `n = 1`: all exponents are zero, and weight `γ ≠ 0` excludes the resulting unit
  monomial, so choose the permitted empty correction. The conclusion reduces to the
  divided iterated-adjoint identity, with the same sign.
- `k = 1`: the sum runs from `0` to `n`, with no truncated endpoint or factorial shift.
- Zero Lie algebra, rank zero, or empty positive roots: none can supply independent
  positive roots `a,b`. They are not excluded globally by any nontriviality hypothesis.
- Independent positive roots with no root `b+ka` cannot supply `γ,hγ`; there is no
  conclusion asserted for a nonexistent root. No assumption that `k` is the string top
  or that `a` is simple was added.
- The zero correction and either sign are supported. The natural exponents include zero,
  and zeroth divided powers use the actual dependency's value `1`.
- Arbitrary enumeration and arbitrary universes `u,v` remain allowed; no fixed rank, type,
  Chevalley sign convention beyond the stated one, or root-system classification is imposed.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `Divided iterated adjoint of a Chevalley root vector at the bottom of a root string has a triangular integer PBW expansion`:
   eight hits, including `LieModule.chainBotCoeff`, `RootPairing.GeckConstruction.f_lie_v_ne`,
   and root-string endpoint lemmas. None states the integer triangular correction identity.
2. `msearch.py ... loogle 'UniversalEnvelopingAlgebra, LieAlgebra.ad'`: successful search,
   zero hits.
3. `msearch.py ... grep 'divided|PBW|Kostant' Algebra/Lie`: one hit, the PBW TODO in
   `Mathlib/Algebra/Lie/Free.lean`; no matching theorem.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for divided-adjoint, node id, and
   triangular/PBW patterns: existing Kostant constructions and the distinct central-parity,
   Weyl-sign, and rank-two-commutator results. Their modules were opened; none has this
   statement. The proposed declaration name is absent from the upstream name index.
5. Read the normalization directly from the local Milne PDF with `pdftotext -layout`:
   Theorem 23.71 gives `N_(α,β) = ±(p+1)`, with `p` the greatest backward root index.
   The source and report explicitly distinguish this from the agent-written coefficient
   lemma, which is not attributed to Milne as an existing theorem.

No statement fault or statement correction was needed. The module compiled cleanly using
`scompile.py NA lem-sfb-root-string-divided-adjoint-triangular <module>` on 2026-10-24.

## Second reading by NA

This is the author's second pass over the node and completed file, not an independent-agent
review: the dispatcher's explicit instruction forbids starting other agents. The maintainer's
independent review remains the independent reading of this delivery.

Rechecked the first-line hypotheses against the full binder list: rational finite-dimensional
semisimple algebra, splitting Cartan, finite reduced crystallographic root pairing evaluated
on that Cartan, positive system, Chevalley eigenvectors and full basis, all three bracket
normalizations. Rechecked the local root assumptions against `ha`, `hb`, `hab`, `hbottom`,
`hk`, `hγ`; neither simple-root nor string-top assumptions appear. Rechecked the sign scope
outside `∀ n`, the inclusive upper summation endpoint, multiplication order, subtraction of
`ε^n e_γ^(n)`, strict exponent bounds for every positive root, exact total root weight,
positive `b`-coordinate of every occurring root, and the empty finite sum. All correspond to
the node. The implementation uses a finite indexed list of integer coefficients rather than
a finitely supported map; both encode the same finite linear combinations. No changes were
needed on this pass.

Delivery validation: `deliver2.py NA lem-sfb-root-string-divided-adjoint-triangular --no-push`
reported `OK (dry run)` at commit `7e1c4909186`: preflight and per-file server compilation pass.
