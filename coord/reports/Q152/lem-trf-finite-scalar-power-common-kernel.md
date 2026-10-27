## Worker report

The module `Sheaf.RingTheory.FiniteScalarPowerCommonKernel` states
`Module.finite_scalar_power_common_kernel`, with its proof postponed by `sorry`.
The node is unchanged except for its new `lean` record. No new notions, dependency
repairs, statement corrections, or disputed statements are needed.

Clause-by-clause translation:

- A commutative ring is `(A : Type u) [CommRing A]`.
- Its module is `(M : Type v) [AddCommGroup M] [Module A M]`.
  These standard structures express all the additive-group and scalar-action laws
  listed in the node, without requiring faithfulness, finite generation or a domain.
- The nonnegative integer n is `(n : ℕ)`; the n scalars are `(f : Fin n → A)`.
- The finite direct sum of n copies of M is the domain of
  `DirectSum.linearEquivFunOnFintype A (Fin n) (fun _ ↦ M)`.
  This is precisely Mathlib's `DirectSum (Fin n) (fun _ ↦ M)`.
- The displayed scalar-coordinate map is
  `fun m : M ↦ (DirectSum.linearEquivFunOnFintype A (Fin n) (fun _ ↦ M)).symm
    (fun i ↦ f i • m)`.
  The inverse equivalence sends an ordinary tuple to its finitely supported tuple
  with the same entries. It is linear, and the scalar-coordinate map is linear
  because A is commutative. No arbitrary map is substituted for the displayed map.
- Its injectivity is exactly the binder `hinj : Function.Injective (...)`.
  The node's equivalent common-kernel reformulation follows by subtracting two
  elements and testing the coordinates, using the additive-module laws.
- The tuple of positive integers is `(e : Fin n → ℕ) (he : ∀ i, 1 ≤ e i)`.
  Positive integers are represented by their nonnegative natural values, with
  the explicit lower bound one; all the node's possible exponents are included.
- The arbitrary element is `(m : M)`, its power-annihilation equations are
  `(hm : ∀ i, f i ^ e i • m = 0)`, and the conclusion is `m = 0`.

Dependency declaration read and used: `def-weil-pbc-direct-sum-modules` is a Mathlib
leaf. Its `mathlib_match` names `DirectSum`, its module instance, `DirectSum.lof`,
`DirectSum.component`, and `DirectSum.induction_on`, in
`Mathlib.Algebra.DirectSum.Basic` and `Mathlib.Algebra.DirectSum.Module`.
I read the direct sum's finitely supported-function definition, its group/module
instances, inclusion and component signatures and induction principle. The module
publicly imports `Mathlib.Algebra.DirectSum.Module` and uses its canonical
`DirectSum.linearEquivFunOnFintype`, whose full signature and docstring identify
it with the linear equivalence from that same direct sum to all tuples on a finite
index type. The only proof dependency is this same direct-sum node, already imported.

Source checked: `literature/stacks-project/algebra.tex`, label
`lemma-when-injective-covering` (Tag 0565), especially its converse proof: induction
on the sum of the exponents, first applying induction to `f_i m`, then replacing
that exponent by one. The theorem docstring includes all four proof steps of the
node, using the equivalent excess-exponent sum in its recorded proof.

Edge cases checked before drafting:

- n = 0 is admitted by `Fin 0`, with no Nonempty assumption. The direct sum is the
  singleton of empty tuples, so `hinj` forces every element of M to be zero.
- The zero module, and the trivial ring with its necessarily zero unital module,
  are admitted. No `Nontrivial` assumption was introduced.
- For n = 1 this is the familiar preservation of injectivity by positive powers.
- All exponents one reproduce the original common-kernel implication.
- Some scalars may be zero or zero divisors. In particular the two complementary
  idempotents of a product ring have a jointly injective scalar-coordinate map
  although neither scalar acts injectively alone; the hypothesis permits this.
- The ring and module universes u and v are independent and explicitly declared.
  `set_option autoImplicit false` checks that every parameter is bound.

Searches for an existing statement (through the prescribed `msearch.py`):

- LeanFinder: "A finite family of scalars on a module with zero common kernel
  still has zero common kernel after taking arbitrary positive powers". Eight
  results, including `Finsupp.iInf_ker_lapply_le_bot`, `IsSMulRegular.pow`,
  `IsSMulRegular.pow_iff`, and kernel stabilization results. None states joint
  injectivity for a general commutative-ring module.
- Loogle: `IsSMulRegular.pow`. One result, whose signature requires injectivity
  of a single scalar, a hypothesis not available here.
- LeanSearch: "For finitely many scalars f_i acting on a module, a zero common
  kernel implies that arbitrary positive powers f_i also have zero common kernel".
  Eight results: endomorphism power annihilation, dual linear-functional results,
  and kernel stabilization; none matches the statement.
- Mathlib grep: `annihilator.*pow|pow.*annihilator|iInf.*ker|ker.*iInf`, restricted
  to `RingTheory`. Fifteen results. I read `Ideal.iInf_ker_le` (localization at
  primes) and the Artinian Fitting-decomposition signatures, which respectively
  concern different kernels and require stronger module hypotheses.
- Read `IsSMulRegular.pow` and `IsSMulRegular.pow_iff` in
  `Mathlib/Algebra/Regular/SMul.lean`: neither covers joint scalar injectivity.
- Project rg over `lean/WeilConjectures` and `lean/Sheaf`:
  `finite.*scalar.*power|common.kernel|lem-trf-finite-scalar-power-common-kernel`.
  Hits concern unrelated common kernels and scalar constructions; no exact theorem.
- Upstream node-id search: `grep -rn lem-trf-finite-scalar-power-common-kernel
  lean/WeilConjectures` returned no hits. Exact proposed declaration-name search
  over both project trees, Mathlib and `dag/lean_names_upstream.json` returned no hits.

Validation: prescribed `scompile.py` compiled the delivered file in sandbox and
library module modes, both cleanly (4.7 s and 0.9 s). There are no definitions with
postponed data and exactly one theorem, whose entire proof is `sorry`.

## Second reading by Q152

I reopened the node and delivered file for a separate clause audit in this worker;
no second agent was started, as the assignment prohibits that. Independent delivery
review remains with the maintainer. The audit checks the original injectivity
hypothesis directly, rather than assuming injectivity of every scalar. The inverse
finite-tuple equivalence really lands in the dependency's finite direct sum, and
has exactly the specified coordinates. `Fin n` admits the empty family; the
positivity binder is pointwise, and the conclusion quantifies over every module
element and every permitted exponent tuple. All scalar powers and zeros have the
original ring and module types. There are no extra algebraic assumptions and no
missing conclusion clauses. No mismatch or change was found during this rereading.
