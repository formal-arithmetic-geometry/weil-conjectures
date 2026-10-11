## Worker report

The module `Sheaf.RingTheory.SplitInjectionAfterCompletion` states
`LinearMap.exists_leftInverse_of_split_mod_pow`, with its sole proof `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- The commutative Noetherian ring A is `{A : Type u} [CommRing A]
  [IsNoetherianRing A]`, using the recorded dependency
  `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`. Its full source signature and docstring were read;
  it means all ideals are finitely generated.
- The ideal J is `(J : Ideal A)`. Its containment in the intersection of
  maximal ideals is `hJ : J ≤ (⊥ : Ideal A).jacobson`;
  `Ideal.jacobson` is precisely the infimum of maximal ideals containing
  the specified ideal, here the zero ideal.
- Finite A-modules N and M use independent explicitly declared universes
  v and w, `[AddCommGroup N] [Module A N] [Module.Finite A N]` and the
  corresponding instances for M. `Module.Finite` means finite generation,
  not finite underlying cardinality.
- The module homomorphism is `(u : N →ₗ[A] M)`.
- Arbitrarily large exponents are `∀ b : ℕ, ∃ k : ℕ, b ≤ k ∧ ...`.
  This is unboundedness, without requiring every exponent to split or
  imposing any compatibility between different retractions.
- The quotient modules are `N ⧸ (J ^ k • (⊤ : Submodule A N))` and
  `M ⧸ (J ^ k • (⊤ : Submodule A M))`, the standard Mathlib quotients
  by J^kN and J^kM. The existential `vk` is an A-linear map from the
  latter to the former.
- The equation `vk.comp (((J ^ k • (⊤ : Submodule A M)).mkQ).comp u) =
  (J ^ k • (⊤ : Submodule A N)).mkQ` says vk qM u = qN.
  It is exactly equivalent to vk u_k = id: linearity gives an induced
  quotient map u_k because u(J^kN) is contained in J^kM; the equality
  u_k qN = qM u is Mathlib's `Submodule.mapQ_mkQ`. Since qN is
  surjective, vk u_k qN = qN holds exactly when vk u_k = id. Thus this
  formulation omits neither a hypothesis nor any splitting data; it
  avoids introducing a second definition of the induced quotient map.
- The conclusion `∃ v : M →ₗ[A] N, v.comp u = LinearMap.id` is exactly
  the asserted A-linear retraction. Injectivity follows from this equation
  and need not be an extra conjunct.

Source checked: the repository does not contain the cited algebra.tex
on this machine, so I read the full statement and proof at
[Stacks Tag 02HO](https://stacks.math.columbia.edu/tag/02HO).
It matches the node. The declaration docstring carries all five steps
of the node's proof, with the non-elementary proof dependencies named.

Edge cases checked before writing: J = 0 makes the hypothesis a splitting
of u itself at every positive exponent. At k = 0 both quotients are zero,
so that exponent alone conveys no information; unboundedness correctly
excludes relying on it alone. N = 0, M = 0, and the zero ring are allowed:
if M = 0 the hypothesis forces N = 0 by Krull intersection, so the
conclusion remains correct. Nilpotent J reduces at large exponents to
splitting u directly. No locality, freeness, nonzero-ring, completeness,
or compatible-retractions hypothesis was added. No statement dispute found.

Searches for an existing statement:
- `msearch.py ... leanfinder`: “A map of finite modules over a Noetherian
  ring split injective modulo arbitrarily high powers of an ideal in the
  Jacobson radical is split injective”. Eight hits, including
  `IsHausdorff.of_le_jacobson`, `AdicCompletion.map_injective`, and
  Nakayama quotient-generator results; none states splitting of u.
- `msearch.py ... loogle`: `Submodule.mapQ, LinearMap.id, Ideal.jacobson`.
  Zero hits for the combined query.
- `msearch.py ... grep`: `split.*(completion|jacobson)|split_injection_after|
  split_injective` in RingTheory. Three hits, on the local-ring
  residue-field criterion and its smoothness application. This requires
  different hypotheses and is not the node's statement.
- `rg -n` of the same completion/Jacobson splitting patterns and the node
  id in `WeilConjectures` and `lean/Sheaf` found only mentions in other
  proofs, no declaration of this statement.
- `rg -n exists_leftInverse_of_split_mod_pow` in Mathlib, the source
  project, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no name
  collision. Direct source reads checked `Submodule.mapQ`,
  `Submodule.mapQ_mkQ`, `Ideal.jacobson`, `Module.Finite`, and
  `IsNoetherianRing` with their docstrings and signatures.

Validation: `scompile.py P1 lem-weil-pbc-split-injection-after-completion`
compiled the module on the server in 1.3 seconds, exit code 0, with no
warnings. Every variable and universe is explicitly bound.

## Second reading by P1

Statement checklist against the DAG node and Stacks Algebra Tag 02HO,
Lemma 10.74.1 (line 18142):

- The ambient ring is `A : Type u` with `[CommRing A] [IsNoetherianRing A]`.
  This is Mathlib's `IsNoetherianRing`, which means every ideal is finitely
  generated, exactly the dependency node `def-weil-pbc-noetherian-ring`.
- The ideal is `J : Ideal A`, with `hJ : J ≤ (⊥ : Ideal A).jacobson`, i.e.
  containment in the intersection of maximal ideals.
- The modules are `N : Type v` and `M : Type w`, each with additive
  commutative group, `A`-module, and `Module.Finite` instances; these are
  finitely generated modules as in the source, with independent universes.
- The map is `u : N →ₗ[A] M`.
- The hypothesis is `∀ b : ℕ, ∃ k : ℕ, b ≤ k` and an `A`-linear `vk` from
  `M ⧸ (J ^ k • (⊤ : Submodule A M))` to
  `N ⧸ (J ^ k • (⊤ : Submodule A N))`, satisfying
  `vk.comp (((J ^ k • ⊤).mkQ).comp u) = (J ^ k • ⊤).mkQ`.
  This is precisely a left inverse of the induced quotient map, expressed
  through the two quotient projections, and has the source's arbitrarily
  large exponents with no compatibility assumption.
- The conclusion is `∃ v : M →ₗ[A] N, v.comp u = LinearMap.id`, exactly the
  asserted split injection and with no extra injectivity clause.

Edge cases checked: `k = 0` gives zero quotients but is insufficient by itself
because the hypothesis is unbounded; `J = 0`, zero modules, the zero ring,
nilpotent ideals, and empty/independent universes are all permitted. No
locality, freeness, nonzero-ring, completion, or compatible-retraction
hypothesis was added.

Searches were repeated with `msearch.py` (LeanFinder, Loogle, and grep) for
the concept and declaration name in Mathlib, `WeilConjectures`, and
`lean/Sheaf`; only unrelated Nakayama, local-ring, and completion lemmas were
found. The dependency declaration and its docstring were read directly.

No mismatch was found and no repair was required. The sandbox module compiles
cleanly with `scompile.py`; its statement is verbatim equal to the node's
recorded `lean.statement`, and all variables and universes are bound.
