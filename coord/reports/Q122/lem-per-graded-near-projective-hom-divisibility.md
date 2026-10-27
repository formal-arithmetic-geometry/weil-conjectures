## Worker report

The module `Sheaf.RingTheory.GradedNearProjectiveHomDivisibility` states
`Ideal.exists_graded_nearProjective_hom_divisibility`, with its sole theorem proof
postponed by `sorry`. It also constructs the two canonical quotient maps used in
that statement, `Ideal.homDivisibilityQuotientMap` and
`Ideal.homDivisibilityQuotientMul`. These are helpers of this node's own notion,
listed in `lean.declarations`, with source and blueprint docstrings; their data
are actual `Submodule.mapQ` maps, extended to quotient scalars by Mathlib's
`LinearMap.extendScalarsOfSurjective`. There are no new nodes, dependency repairs,
statement changes, or mathematical disputes. Only the item's `lean` field changes.

The source was read in `literature/stacks-project/local-cohomology.tex`,
section-uniform (0GA6) and lemma-factor-hom (0GAC), and
`literature/stacks-project/more-algebra.tex`, lemma-near-projective (0G92) and
definition-near-projective (0G93). The current blueprint ancestor proof was read
under `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/`:
`sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md`.
As the accepted split records, its current Step 3 concerns Verdier exchange;
the algebraization branch here is inherited, rather than asserted by that step.

Hypotheses and clauses, matched individually:

- The fixed Noetherian commutative ring and ideal are `R₀ : Type u`,
  `[CommRing R₀]`, `[IsNoetherianRing R₀]`, and `K₀ : Ideal R₀`.
- The nonnegative constants are `∃ D q : ℕ`, placed before every comparison ring,
  ideal, graded isomorphism, exponent, module, and homomorphism. Thus one pair of
  constants works throughout the graded isomorphism class, independently of all
  those choices; no completeness assumption occurs.
- An arbitrary comparison ring and ideal are `∀ (R : Type v) [CommRing R]
  [IsNoetherianRing R] (K : Ideal R)`. The universes of the fixed ring, comparison
  ring, and module are independently declared `u v z`.
- The unital ring isomorphism is `e : K.associatedGraded ≃+* K₀.associatedGraded`.
  Preservation of each degree is the following hypothesis for every `j : ℕ`:
  the range of `x ↦ e (DirectSum.of _ j x)` equals the range of
  `DirectSum.of (fun k => K₀.associatedGradedPiece k) j`. This says exactly that
  `e` maps the degree-j subgroup onto the degree-j subgroup. Since `e` is a ring
  equivalence, it includes the inverse degree condition and preserves the unit.
  It imposes no extraneous identification of the two base rings.
- `n c : ℕ` and `hcn : c ≤ n` render `n ≥ c ≥ 0`.
  `hb : max (q + (D + 1) * c) ((D + 2) * c) ≤ n` is the first numerical bound;
  `hzero : D = 0 → q + 2 * c ≤ n` retains the extra conditional bound verbatim.
- `A` is written directly as `R ⧸ K ^ n`, with no opaque let binder.
  `M : Type z`, `[AddCommGroup M]`, `[Module (R ⧸ K ^ n) M]`, and
  `[Module.Finite (R ⧸ K ^ n) M]` render the finite A-module.
- For every `a : (K ^ c : Ideal R)`, the factorization hypothesis supplies
  `r : ℕ`, `f : M →ₗ[A] (Fin r → A)` and `g : (Fin r → A) →ₗ[A] M`, with
  `∀ x, g (f x) = Ideal.Quotient.mk (K ^ n) a.1 • x`.
  The finite function module is finite free of rank r, including rank zero.
  The pointwise equality is precisely `g ∘ f = ā id`, with the canonical image
  of the ideal element in the quotient ring, not a separately chosen scalar.
- The quotient `K^r/K^(n+r)` is rendered by
  `(K ^ r : Ideal R) ⧸ (K ^ n • ⊤ : Submodule R (K ^ r : Ideal R))`.
  This is literally the quotient of the ideal module K^r by K^n times that
  module. Its image under the ideal subtype is `K^n K^r = K^(n+r)`.
  `Submodule.mem_smul_top_iff` and `pow_add` give the representative membership
  identification. Mathlib's instance from `Module.Torsion.Basic` gives its
  canonical `R/K^n` action, induced by multiplication in R.
- Consequently `u` has exactly the node's type `M →ₗ[A] K^n/K^(2n)`:
  the numerator exponent is n and denominator exponent is `n+n = 2n`.
- `t = n-(D+1)c` and `w = n-(D+2)c` appear explicitly, using natural
  subtraction. The hypotheses ensure both are nonnegative and subtraction
  agrees with the integer formulas; the inline arithmetic proof establishes
  exactly `t = c+w`, without a new assumption.
- The finite indexing set is `Fin m` for the existential `m : ℕ`.
  Every finite set admits such an enumeration; conversely `Fin m` is finite.
  `a : Fin m → (K ^ c : Ideal R)` supplies all required coefficients, and
  `ψ : Fin m → M →ₗ[A] K^w/K^(n+w)` supplies exactly the required linear maps.
- `homDivisibilityQuotientMap K n n t (Nat.sub_le _ _)` is p: the underlying
  linear map is `Submodule.inclusion (Ideal.pow_le_pow_right ...)`, so a
  representative x stays x and the denominator becomes K^(n+t). The inequality
  `t ≤ n` is automatic; hence this helper adds no hypothesis to the theorem.
- `homDivisibilityQuotientMul K n c w t ... (a j)` is μ_(a_j): the underlying
  linear map is multiplication `b ↦ (a j).1 * b.1`, restricted to K^w and
  corestricted to K^t using `t = c+w`. Its quotient takes K^n K^w into K^n K^t,
  so it sends `[b]` to `[a_j b]` modulo the exact required denominator.
- The final equality is `p.comp u = ∑ j : Fin m, (μ_(a j)).comp (ψ j)` in the
  space of A-linear maps to K^t/K^(n+t), so it asserts the node's equality
  for every element of M with the correct common codomain.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, together with its signature/docstring and
  `isNoetherianRing_iff_ideal_fg`. It is the specified finite-generation condition.
- `def-weil-pbc-associated-graded-ring`:
  `WeilConjectures.RingTheory.AssociatedGradedRing`, `Ideal.associatedGraded`
  and `Ideal.associatedGradedPiece`, with its `associatedGradedCommRing`
  instance. Read the full source: each piece is K^j/K^(j+1), multiplication
  is induced by product of representatives, and the degree-zero class of one
  is the unit. The direct sum inclusions are Mathlib's `DirectSum.of`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite`, whose signature/docstring says the top submodule is FG.
- Additional implementation APIs are `Module`'s ideal-smul quotient action
  from `Mathlib.Algebra.Module.Torsion.Basic`,
  `LinearMap.extendScalarsOfSurjective` from `Mathlib.Algebra.Algebra.Basic`,
  and the imported quotient, ideal, and direct-sum APIs.
- The three proof dependencies, `lem-per-blowup-uniform-tensor-section-bound`,
  `lem-per-near-projective-dual-comparison`, and
  `lem-per-line-twist-double-annihilator-reverse`, currently have no recorded
  Lean declarations or Mathlib matches. Their statements were read, their
  exact roles are retained in the theorem's four-step natural-language proof,
  and there is no module to import for them yet. They are proof prerequisites,
  not missing notions needed to state this theorem.

Edge cases checked before writing:

- `n = 0` forces `c = 0`; A is the zero ring, hence M is zero. All displayed
  quotient modules are zero and `m = 0` supplies the empty sum.
- `c = 0` gives `t = w = n`; the scalar 1 has a finite-free factorization,
  the transition is the identity, and the asserted divisibility is consistent.
- `D = 0` is allowed and retains the separate bound `n ≥ q+2c`.
- At the boundary `n = (D+2)c`, w is zero and t is c. The source for ψ is the
  full ideal `K^0 = R` modulo K^n, which the quotient presentation includes.
- Zero module, rank-zero factorization, and an empty summation set are allowed.
- `K = ⊤` gives zero quotient modules; no proper-ideal assumption was added.
- For `K = ⊥`, a suitable invariant q can be at least 1, avoiding a spurious
  small-exponent assertion. The theorem requires existence of constants and
  does not prescribe q=0. Nilpotent ideals and the zero ring are included.
- `t ≤ n` always holds, and `t = c+w` follows from the numerical bound;
  these verify both canonical maps on all allowed boundary cases.

Searches for existing statements and notions (2026-10-24):

- `msearch.py ... leanfinder`, query: "Uniform divisibility of Hom from finite
  near projective modules modulo ideal powers with constants determined by
  the associated graded ring". Eight results concerned completion transition
  maps, adic congruence lifting, and `Submodule.factorPowSucc`; no matching
  uniform near-projective Hom statement.
- `msearch.py ... loogle`, query: `Ideal.associatedGraded, LinearMap`.
  Zero results; Loogle's Mathlib index does not know the project declaration
  `Ideal.associatedGraded`.
- `msearch.py ... grep`, query:
  `near.?projective|hom.*divisib|divisib.*hom`, subdirectory `RingTheory`.
  One unrelated hit in `HahnSeries/HahnEmbedding.lean` on `DivisibleHull`.
- `msearch.py ... leansearch`, query: "Every linear map from a finite near
  projective module over R modulo K^n into K^n modulo K^(2n) becomes a finite
  sum of K^c multiples after a uniform loss depending only on the associated
  graded ring". Eight results: `LinearMap.reduceModIdeal` and its representative
  formula, finiteness of linear-map modules, finite module presentations, and
  finite projective splitting. None is this statement. The general quotient
  map construction in `reduceModIdeal` uses the same Mathlib `Submodule.mapQ`
  and extension-of-scalars APIs used here for the specified canonical maps.
- `rg` for `near.?[Pp]rojective|[Hh]om.*[Dd]ivisib|[Dd]ivisib.*[Hh]om`
  in `lean/WeilConjectures` and `lean/Sheaf`: only unrelated group-divisibility,
  Kummer, and categorical orthogonality references. The prescribed `grep -rn`
  for this node ID in `lean/WeilConjectures` returned no hits.
- Declaration-name collision search in `dag/lean_names_upstream.json`,
  Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` returned no hits for
  `homDivisibilityQuotientMap`, `homDivisibilityQuotientMul`, or
  `exists_graded_nearProjective_hom_divisibility`.
- Further source searches found Mathlib's canonical module structure on
  `N/(I • ⊤)` and `LinearMap.extendScalarsOfSurjective`, which were used rather
  than inventing a quotient action. `Submodule.mem_smul_top_iff` identifies
  the denominators with the exact ideal powers in the node.

Validation: the prescribed `scompile.py Q122
lem-per-graded-near-projective-hom-divisibility <module>` compiled both the
sandbox probe and the actual library module cleanly (2.1 s and 2.3 s).
The file explicitly disables autoImplicit, binds every universe and variable,
and has no diagnostics or probe commands. The only postponed theorem is the
main declaration, whose docstring includes all four accepted proof steps.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
