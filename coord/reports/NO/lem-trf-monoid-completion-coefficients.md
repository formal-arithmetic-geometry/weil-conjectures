## Worker report

The module `Sheaf.RingTheory.MonoidCompletionCoefficients` states
`AddMonoidAlgebra.monoidCompletion_coefficients`, with exactly one postponed theorem
and no definitions or proofs. The DAG statement is unchanged; only its `lean` record
is set. No new nodes or dependency repairs are needed.

Source read: ILO, Travaux de Gabber, Exposé VI §1.6(i)–(ii), printed p. 70
(the equal- and mixed-characteristic formal monoid models); Stacks Project,
`algebra.tex`, `lemma-hathat-finitely-generated`, Tag 05GG, including both numbered
parts and the final quotient statement. As the DAG source says, the general
coefficient refinement is agent-supplied, not asserted to occur verbatim in ILO.
The module docstring records that attribution; the theorem docstring gives all six
proof steps, including the finite-pattern partition.

Hypotheses and objects, clause by clause:

- The commutative coefficient ring is `(A : Type u) [CommRing A]`.
  `[IsNoetherianRing A]` is exactly the Noetherian hypothesis, and
  `[IsLocalRing A]` supplies its unique maximal ideal `IsLocalRing.maximalIdeal A`.
- Completeness and separatedness for that maximal ideal are the single standard
  hypothesis `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`. Its source signature
  extends both `IsHausdorff` and `IsPrecomplete`.
- The commutative additive monoid is `(P : Type v) [AddCommMonoid P]`;
  `[AddMonoid.FG P]` means its top additive submonoid is finitely generated.
- The ambient group is `(G : Type w) [AddCommGroup G]`. `ι : P →+ G` with
  `hι : Function.Injective ι` gives the specified embedding. The hypothesis
  `hfree : ∃ r : ℕ, Nonempty (G ≃+ (Fin r → ℤ))` says precisely that the ambient
  abelian group is free of finite rank, including rank zero.
- `wgt : G →+ ℤ` is the weight homomorphism; `hpos` requires strict positivity on
  every nonzero element of `P`, evaluated through `ι`.
- `AddMonoidAlgebra A P` is the existing finite-support monoid algebra, whose
  `single p a` is the monomial `a z^p`. Its multiplication adds exponents.
- The existential `b` is pinned by an equality, not left arbitrary: it is the sum
  of the mapped maximal ideal and the span of `single p 1` for `p ≠ 0`.
- `AdicCompletion b (AddMonoidAlgebra A P)` is literally the specified inverse
  limit. No replacement completion is introduced.

Conclusions, clause by clause:

- `∃ ν : P → ℕ` with `ν 0 = 0` and `IsGreatest` of the set of lengths of nonzero
  decompositions defines the order function exactly. A decomposition of length
  `q` is `p₁ : Fin q → P` with every `p₁ i ≠ 0` and `∑ i, p₁ i = p`.
  `IsGreatest` asserts both attainment and that every possible length is at most
  the finite natural number `ν p`; no maximum is assumed as an extra hypothesis.
- The literal type of all families is `P → A`. A commutative ring structure
  `ring` and an algebra structure `alg` are quantified in the conclusion with
  their exact operation formulas, and `c` is an `A`-algebra equivalence from
  the completion to that very type. This is a statement of the claimed ring
  structure and isomorphism, not a definition choosing data from an existence
  theorem. There is no restriction on supports.
- `@Add.add ... ring.toAdd` is prescribed to be componentwise addition, and
  `@Mul.mul ... ring.toMul` is prescribed to be convolution. Explicit structure
  arguments are essential: an inspection of an earlier elaboration showed that
  unqualified multiplication would select Mathlib's ordinary pointwise function
  multiplication. The delivered signature explicitly uses `ring` in the target
  semiring of `AlgEquiv`, the `Algebra` structure, and both operation formulas.
- The convolution uses `∑ᶠ` over the subtype of pairs `(u,v)` whose sum is `p`.
  The separate `Set.Finite {q : P × P | q.1 + q.2 = p}` clause guarantees that
  this is the intended finite sum even for arbitrary coefficient families.
- The monomial clause sends `AdicCompletion.of ... (single p a)` to the function
  whose value at `q` is `if q = p then a else 0`. In particular, at `p = 0`
  it normalizes the algebra map on coefficients, and at `a = 1` it normalizes
  each monomial. The algebra equivalence is therefore not an arbitrary map.
- For every `n : ℕ` with `1 ≤ n`, `AdicCompletion.evalₐ b n` is the canonical
  projection to the quotient by `b ^ n`, and it is asserted surjective.
- Its `RingHom.ker` is `Ideal.map (algebraMap A[P] B) (b ^ n)`, which is exactly
  the extended ideal `b^n B`, rather than an ideal independently specified on `B`.
- Membership in that kernel is equivalent to
  `∀ p, c x p ∈ maximalIdeal A ^ (n - ν p)`. Natural subtraction is truncated,
  so this is exactly the node's exponent `max(n - ν(p), 0)`.
- `Set.Finite {p : P | ν p < n}` asserts finitely many summands. The final
  `Nonempty (... ≃ₗ[A] ⨁ p : {p // ν p < n}, A ⧸ m^(n - ν p.1))`
  is precisely the asserted module isomorphism from `B / b^n B` to the indicated
  direct sum of coefficient quotients. It is not an algebra isomorphism or a
  product substituted for the direct sum.

The normalization is also enough to specify the natural coefficient map, rather
than merely some abstract isomorphism. It is additive and agrees with all finite
monomial sums. The kernel condition makes it continuous for the displayed
filtrations. For a representative `F` of `x` at level `n`, applying the condition
to `x - of F` gives `c(x)_p - F_p ∈ m^(n - ν(p))`. Taking `n ≥ k + ν(p)` pins its
residue modulo every `m^k`; separatedness gives uniqueness. Thus the existential
presentation does not lose the naturality requested by the node.

Dependency declarations used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`; the abbreviation and its docstring were read.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `Mathlib.RingTheory.AdicCompletion.Basic`; the complete class signature and its
  two parent definitions were read.
- `def-weil-pbc-adic-completion`: `AdicCompletion` and `AdicCompletion.of` from
  `Mathlib.RingTheory.AdicCompletion.Basic`, with the ring/algebra structures and
  canonical `evalₐ` from `Mathlib.RingTheory.AdicCompletion.Algebra`.
  Their full source signatures and docstrings were read. Importing `Algebra`
  publicly also imports the recorded `Basic` module.
- Other standard objects: `AddMonoidAlgebra`/`single` from
  `Mathlib.Algebra.MonoidAlgebra.Basic`, `AddMonoid.FG` from
  `Mathlib.GroupTheory.Finiteness`, `IsLocalRing.maximalIdeal` from
  `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`, `finsum` from
  `Mathlib.Algebra.BigOperators.Finprod`, and the direct sum from
  `Mathlib.Algebra.DirectSum.Basic`.
- Proof dependency `lem-trf-finite-pattern-factorization` was read in full.
  It currently has no recorded Lean declaration, so there is no module to import.
  The theorem docstring gives its required partition argument. It is not needed
  to type this statement; it remains a proof dependency for stage 3.

Edge cases checked before drafting:

- If `P = {0}`, only the empty decomposition occurs, `ν(0)=0`, the monomial part
  of `b` is zero, and completeness identifies the completion with `A`. The quotient
  sum has its sole summand `A/m^n`. Rank zero and no monoid generators are allowed.
- For `P = ℕ`, `ν(p)=p` and convolution is the usual finite Cauchy sum. More generally
  relations in `P` are retained; no free-monoid assumption was introduced.
- At `n = 1`, `ν(p) < 1` singles out zero and the quotient is `A/m`. At `ν(p) ≥ n`,
  natural subtraction is zero and the condition is membership in `m^0 = ⊤`, as needed.
- If `A` is a field, `m=0`; the same formulas yield the usual monomial filtration.
  No regularity, field, characteristic, domain, or reducedness hypothesis is added.
- Coefficients, the monoid, and the ambient group have independent explicitly bound
  universes `u v w`. The completion and all families live in their natural maximum
  universe. The function type imposes no countability or finite-support assumption.

Searches for an existing declaration (all performed in this session):

- `msearch.py` LeanFinder: “Completion of a positive affine monoid algebra over a
  complete local ring has arbitrary coefficient families with finite convolution”.
  Eight Laurent-series/adically completed rational-function declarations; none is
  the affine-monoid mixed-ideal coefficient theorem.
- `msearch.py` Loogle: `"AdicCompletion", "AddMonoidAlgebra"`: zero hits.
- `msearch.py` Mathlib grep:
  `AdicCompletion.*(MonoidAlgebra|MvPowerSeries)|(MonoidAlgebra|MvPowerSeries).*AdicCompletion`:
  four hits, all in `Mathlib/RingTheory/MvPowerSeries/Equiv.lean`.
  Read lines 275–355: `MvPowerSeries.toAdicCompletionAlgEquiv` completes the free
  monoid polynomial algebra at its variable ideal. It does not handle the mixed
  maximal coefficient ideal, monoid relations, or the order `ν` here.
- `msearch.py` LeanSearch: “Formal monoid series coefficients of the completion of
  a positive monoid algebra at its mixed maximal ideal”. Eight HahnSeries,
  PowerSeries and MvPowerSeries coefficient declarations. None is this statement.
- `rg` in Mathlib, `WeilConjectures`, and `lean/Sheaf` for the planned name
  `monoidCompletion_coefficients` / `monoid_completion_coefficients`: no existing
  declaration. Searches for monoid completion, formal monoid, coefficient and
  finite-pattern terms find the downstream FormalMonoidRingDimension and
  CompleteToricFacetValuations uses, not this coefficient interface.
- Searched `dag/lean_names_upstream.json` and the source tree for the item id;
  no upstream attachment. Read the three dependency node records and the example
  `CompactObject.lean` with its node record. No repair note exists for this item.

Validation: the full module compiles without errors or warnings through the
prescribed `scompile.py` wrapper, both as a sandbox file and as its intended module.
No `#check` or `#print` commands remain. The only proof is the required `sorry`.
All Lean lines are at most 100 characters. No statement correction, new definition
node, dependency module, or disputed statement is present.

## Second reading by NO

Author's clause-by-clause second pass, not an independent review. This dispatcher
brief prohibits starting other agents; the maintainer provides the independent
review. I reread the item beside the final signature and checked each hypothesis
and each conclusion listed above. In particular I checked that the existential
function ring's explicit structure, rather than ordinary pointwise multiplication,
is passed to `AlgEquiv` and used in the convolution formula; all families are
included; `ν` is an attained maximum; the extended ideal is the image of the actual
`b^n`; `n - ν(p)` is truncated; and the quotient is the specified finite direct sum.
The final module has no auxiliary data choices, additional mathematical hypotheses,
unnamed postponed lemmas, or changes to other nodes. The correction made during this
pass was to make the function-ring structure arguments explicit, avoiding the
pointwise instance. The mathematical DAG statement required no change.
