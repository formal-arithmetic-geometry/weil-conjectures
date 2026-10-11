## Worker report

Item: lem-weil-pbc-kernel-cokernel-annihilated-mod-ideal.
Module: `Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal`.
Declarations: `LinearMap.ker_coker_annihilated_mod_ideal` (clauses a–d), and
`LinearMap.ker_coker_annihilated_iff_exists_exact_sequence` (the parenthetical equivalence).
Both are statements with `sorry`; there are no new definitions, proofs, or additional nodes.
The node copy changes only `lean`.

Source checked: Stacks Project, Cohomology of Schemes, Remark 0888,
https://stacks.math.columbia.edu/tag/0888, the commutative algebra paragraph and
following limit paragraph. The repository's `literature/stacks-project/coherent.tex`
is absent on this machine; I read the official online tag instead. The source's
algebra fact is stated for arbitrary modules over a commutative ring, so no
Noetherian, finiteness or completeness hypothesis belongs in this lemma.
Naturality and the converse are the node's explicit expansions of the limit argument.

Hypotheses and conventions:

- A commutative ring: `{A : Type u} [CommRing A]`.
- A-modules M and N: `{M N : Type v}` with `AddCommGroup` and `Module A` instances.
  A common arbitrary universe accommodates both carriers; the naturality modules and
  the converse modules have independent arbitrary universes `w` and `z`.
- Ideal K: `(K : Ideal A)`; integer t ≥ 1: `(t : ℕ) (ht : 1 ≤ t)`.
  Positive integers are represented exactly by these natural numbers.
- The A-linear map: `(u : M →ₗ[A] N)`.
- Kernel annihilation: `hker : K ^ t ≤ Module.annihilator A (ker u)`.
- Cokernel annihilation: `hcoker : K ^ t ≤ Module.annihilator A (N ⧸ range u)`.
  This quotient is precisely the node's cokernel N/u(M), not an abstract replacement.
- The parenthetical equivalence is the separate iff theorem, with precisely the same
  two annihilator conditions on the left. The right existentially quantifies bundled
  A-modules T,Q and maps i,p and asserts
  `(ComposableArrows.mk₅ 0 i (ModuleCat.ofHom u) p 0).Exact`, with the endpoints explicitly
  Mathlib's zero object. This is the whole sequence 0 → T → M → N → Q → 0;
  both annihilator conditions on T,Q follow in the conjunction. The iff is also valid
  at t=0, so this explanatory equivalence does not need the positivity restriction.

Clause correspondence:

- (a) The first conjunction quantifies every `f g : A` with memberships in `K ^ t`.
  `∀ y : N, ∃ x : M, u x = f • y` is existence of a lift.
  The next clause quantifies y,x,x' and both lifting equalities and concludes
  `g • x = g • x'`, explicitly giving independence of the chosen lift.
  `∃ h : N →ₗ[A] M` gives A-linearity. Its first property is
  `∀ y x, u x = f • y → h y = g • x`, the defining formula of the canonical map.
  Its next two properties are `h.comp u = (f * g) • LinearMap.id` and
  `u.comp h = (f * g) • LinearMap.id`, on the correct respective modules.
  Existence of a lift and the formula uniquely characterize h, without a private
  definition or a choice of underlying data based on `sorry`.
- (b) The last property of h quantifies M',N', their module structures, u', both
  annihilator hypotheses for u', maps a,b,h', and the commuting-square equation
  `u'.comp a = b.comp u`. It assumes the lifting formula for h', so h' is exactly
  the canonical map of (a), and concludes `a.comp h = h'.comp b`.
  Existence of this canonical h' is clause (a) applied to u'; the universal property
  makes the naturality equation hold for every representative satisfying that formula.
  Requiring merely the two composite identities would not characterize the canonical
  map, which is why its full lifting formula is used here.
- (c) The second outer conjunction quantifies `∀ J : Ideal A`.
  `ū := (u.reduceModIdeal J).restrictScalars A` is the actual induced A-linear map
  M/JM → N/JN, using Mathlib's existing reduction, with its A/J scalars restricted
  to A. Here JM is `(J • ⊤ : Submodule A M)`, and likewise for N.
  Both `K ^ (2 * t) ≤ Module.annihilator A (ker ū)` and the analogous condition on
  `(N ⧸ (J • ⊤ : Submodule A N)) ⧸ range ū` are stated.
- (d) The third outer conjunction quantifies arbitrary A-modules P,R and
  `v : P →ₗ[A] R`. Its premise quantifies every f,g in K^t, with an existential
  `k : R →ₗ[A] P` having exactly both composite identities in the node.
  The conclusion states annihilation by K^(2*t) of `ker v` and `R ⧸ range v`.
  There is no additional hypothesis on v or on the modules P,R.

Dependency used:

- `def-weil-pbc-exact-sequence`: recorded module
  `Mathlib.Algebra.Homology.ExactSequence`, declaration
  `CategoryTheory.ComposableArrows.Exact`. Its signature and docstring were read,
  along with the recorded `ShortComplex.Exact` and `ShortComplex.ShortExact`.
  The finite sequence of the parenthetical is rendered using ComposableArrows.Exact
  directly; this record was usable and needs no dependency module.
- Existing Mathlib operations: `LinearMap.ker`, `LinearMap.range`, module quotients,
  `Module.annihilator`, ideal powers, `LinearMap.reduceModIdeal` from
  `Mathlib.RingTheory.AdicCompletion.Functoriality` (full definition and apply theorem
  read), and `ModuleCat` from `Mathlib.Algebra.Category.ModuleCat.Abelian`.
  These supply all notions; no missing notion needs a new node.

Edge cases checked before writing:

- K=0 and t≥1: f=g=0, h=0, and the annihilation assertions are vacuous as expected.
- K=⊤: annihilation forces kernel and cokernel zero; the map is an isomorphism,
  with the stated scalar inverse and quotient isomorphisms.
- J=0 retains u; the claimed K^(2*t) bound follows from the K^t bound.
- J=⊤ makes both quotient modules zero; their kernels and cokernels are zero.
- Zero modules, the zero ring, and nilpotent K are allowed; no nontriviality or
  domain assumptions occur. The case t=1 is included; t=0 is excluded in the main
  theorem exactly as in the node. Arbitrary non-finite modules and infinitely
  generated ideals are included; ideal multiplication uses finite sums of products.
- The naturality equation follows by applying a to a lift x; a(x) lifts f*b(y),
  including when a or b is zero. Formula uniqueness handles every possible lift.

Searches (actual queries recorded in sandbox `searches.jsonl` by msearch.py):

- LeanSearch: `linear map with kernel and cokernel killed by ideal power has canonical
  scalar quasi inverse and reduction has kernel cokernel killed by square power`.
  Service unavailable (Internal Server Error), not evidence of absence.
- LeanFinder: `linear map with kernel and cokernel annihilated by ideal power, scalar
  quasi inverse naturality and reduction modulo an ideal`.
  Eight results: factorPowSucc, factorPow, adic-completion lift/transition results,
  regular-sequence quotient naturality and a ramification quotient map. These are
  quotient-map operations or different hypotheses/conclusions; none matches this node.
- Loogle: `Module.annihilator, LinearMap.ker`.
  Only `Module.exists_ker_toSpanSingleton_eq_annihilator`, a PID result identifying
  a kernel with a module annihilator; not this statement.
- Mathlib grep: `annihilator.*(ker|coker)|(ker|coker).*annihilator|reduceModIdeal`.
  Returned dual annihilator results and unrelated character/polynomial statements.
  Focused reading of Functoriality.lean found reduceModIdeal and its apply theorem,
  but no scalar quasi-inverse or annihilation theorem.
- Project grep: `annihilat|reduceModIdeal` in the source and landed RingTheory modules;
  annihilator/associated-prime statements only. Follow-up full-tree search for
  `ker_coker_annihilated_mod_ideal|ker_coker_annihilated_iff_exists_exact_sequence|
  canonical.*fg|reduceModIdeal` in WeilConjectures/, lean/Sheaf/ and the upstream name
  index found only the different adic-limit theorem using reduceModIdeal.
  Searching the item's blueprint id in WeilConjectures/ returned no match.

No statement correction or dispute. Server compile via scompile.py succeeded
without errors or warnings (1.9 seconds); every theorem remains `sorry` as required.

## Second reading by J1

I reread the node statement, its Stacks source (Remark 0888, lines 29--34 on the
online tag), the dependency node `def-weil-pbc-exact-sequence`, and the complete
Lean module. The objects and hypotheses render as follows: `A` is `{A : Type u}`
with `[CommRing A]`; `M,N` are `{M N : Type v}` with additive-group and module
instances; `K : Ideal A`, `t : ℕ`, `ht : 1 ≤ t`, and `u : M →ₗ[A] N`; and the two
annihilator inclusions are exactly `hker` for `ker u` and `hcoker` for
`N ⧸ range u`. Clause (a) is the outer `∀ f g` conjunction, including lifts,
choice independence, the linear map `h`, both scalar composite identities, and
its lifting formula. Clause (b) is the quantified `M' N' u' a b h'` continuation
of that conjunction, with both annihilator hypotheses, the commuting square, and
the lifting formula for `h'`. Clause (c) is the `∀ J` let-bound
`(u.reduceModIdeal J).restrictScalars A`, with both kernel and quotient-cokernel
bounds by `K ^ (2 * t)`. Clause (d) is the independent-universe `P,R,v`
converse and its two annihilator conclusions. The parenthetical exact-sequence
form is rendered by the separate theorem
`LinearMap.ker_coker_annihilated_iff_exists_exact_sequence`, using the recorded
`CategoryTheory.ComposableArrows.Exact` declaration.

The edge cases remain covered: zero and unit ideals, zero modules and zero ring,
nilpotent ideals, `t = 1`, arbitrary modules and ideal sizes, every `J` including
zero and top, and arbitrary universes for the naturality and converse modules.
The positivity hypothesis is present exactly for the main statement; the
parenthetical equivalence intentionally has no positivity premise. I searched
Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and the upstream-name index for the
two theorem names and for annihilator/kernel/cokernel variants; only unrelated
adic and PID results were found. The dependency's Mathlib exact-sequence
notion is the one used by the module.

No mismatch was found and no source, statement, dependency, or Lean declaration
was changed. `scompile.py` compiles the module with only the permitted `sorry`
proofs.
