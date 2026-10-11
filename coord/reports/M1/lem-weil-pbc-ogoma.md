## Worker report

The module `Sheaf.AlgebraicGeometry.Ogoma` states `ogoma_lemma`. It uses
`IsNoetherianRing A` for the Noetherian-ring hypothesis,
`Module.Finite A M` for finitely generated, and `LocalizedModule S M` for
$S^{-1}M$. The hypothesis `h` is equality of the two sets of localized
vectors killed by multiplication by `π` and by `π` twice. The conclusion is an
`s : S` and, for every natural number `n` with `0 < n`, equality of the sets
of `m : M` killed by `((s : A)^n * π)` and by its square. Scalar multiplication
renders multiplication by each displayed ring element; set equality renders
equality of kernels. The proof is `sorry` as required at stage 2.

Dependency declarations used:

- `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs.Module.Finite`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic.LocalizedModule`.

Edge cases checked: `S` is an arbitrary submonoid (including the trivial one),
`M` may be zero, and `n` is explicitly restricted to positive naturals so the
statement does not impose an unmentioned zero-power case. Universes `u` and
`v` are explicit and independent, as required for a ring and module.

Searches for an existing statement or definition: `msearch.py leanfinder` with
“Ogoma lemma kernel of s^n pi equals kernel of (s^n pi)^2 for some s in
multiplicative set” returned no match; `msearch.py loogle` with
“LinearMap.eventually_iSup_ker_pow_eq, Module.End.eventually_disjoint_ker_pow_range_pow,
Ideal.exists_pow_inf_eq_pow_smul” returned only unrelated kernel-stabilization
lemmas; `msearch.py grep` for `Ogoma|ker.*\^ 2.*IsLocalization|annihilator.*pow 2`
returned none. `rg` over `WeilConjectures/` and `lean/Sheaf/` found no Ogoma
statement. The dependency notions were matched directly to the recorded
Mathlib declarations above.

## Earlier second reading (a previous round; superseded)

The node's hypotheses are rendered one-for-one: commutative ring and
Noetherian instance on `A`, finitely generated `A`-module `M`, multiplicative
subset `S`, and element `π`. The displayed localized kernel equality is the
node's `Ker(π)=Ker(π^2)` hypothesis, expressed as set equality on
`LocalizedModule S M`; the conclusion has exactly one `s ∈ S` and exactly the
same kernel equality for every positive natural exponent. No hypothesis or
clause was added or omitted.

## Second reading by M1

I read the node statement and Stacks Smoothing Ring Maps, Lemma 07FC (tag
07FC, `lemma-ogoma`, lines 2287--2303) against the module.

- The source's Noetherian commutative ring (A) is rendered by `{A : Type u}
  [CommRing A] [IsNoetherianRing A]`; the latter is the recorded Mathlib
  meaning of every ideal finitely generated.
- The source's finite (A)-module (M) is rendered by `{M : Type v}
  [AddCommGroup M] [Module A M] [Module.Finite A M]`.
- The multiplicative subset (Ssubset A) is the explicit `(S : Submonoid A)`;
  `Submonoid` supplies (1in S) and closure under multiplication.
- The element π is the explicit `(π : A)`.
- The hypothesis
  `Ker(π : S⁻¹M → S⁻¹M) = Ker(π² : S⁻¹M → S⁻¹M)` is rendered exactly as
  `h : {x : LocalizedModule S M | π • x = 0} =
  {x : LocalizedModule S M | π • (π • x) = 0}`. `LocalizedModule S M`
  is the dependency's localization object, and the ambient scalar action is
  the canonical (A)-action.
- The conclusion's existential (s\in S) is `∃ s : S`; its universal positive
  integer is `∀ n : ℕ, 0 < n →`; and its two kernel clauses are exactly the
  set equalities
  `((s : A)^n * π) • m = 0` and
  `(((s : A)^n * π)^2) • m = 0` for `m : M`.

No hypothesis, object, quantifier, or conclusion clause is added, omitted,
strengthened, or weakened. The declaration has no unbound variables or extra
universe restrictions, and its proof is only `sorry` as required for stage 2.

Edge cases checked: `S` may be the trivial submonoid or any nonempty
multiplicative subset; `M = 0` is admitted; `π = 0` is admitted; positive
`n` includes `n = 1` and deliberately excludes `n = 0`, exactly as in the
source; and independent universes `u` and `v` allow all source cases without
an artificial universe equality. The source and Lean both use commutative
rings, so no noncommutative case is introduced.

Searches were repeated with `msearch.py` LeanFinder and Loogle queries for the
Ogoma kernel statement, `rg` over Mathlib and `WeilConjectures/`, and `rg` over
this repository's `lean/Sheaf`; these found only unrelated kernel-stabilization
lemmas and no existing Ogoma declaration. The three dependency declarations
were opened and match their nodes: `IsNoetherianRing`, `Module.Finite`, and
`LocalizedModule`.

Mismatch review: none found, so no Lean, node, or dependency record was
changed. The module compiled cleanly with `scompile.py` (the sole diagnostic
is the permitted `sorry` declaration warning).
