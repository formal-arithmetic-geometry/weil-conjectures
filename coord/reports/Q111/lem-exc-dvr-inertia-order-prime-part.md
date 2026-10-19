## Worker report

The module `lean/Sheaf/FieldTheory/FiniteDVRInertiaOrderPrimePart.lean` states
`IsDiscreteValuationRing.inertia_order_prime_part`, with proof `sorry` as required for
stage 2. It uses Mathlib's `integralClosure`, `Localization.AtPrime`, and
`Ideal.inertia` to render the integral closure, localization, and inertia subgroup in
the node statement. The theorem binds universes `u`, `v`, and `w` explicitly and uses
`set_option autoImplicit false`.

The hypotheses are rendered as follows. `A` is a commutative domain with the
`IsDiscreteValuationRing A` class; `K` is a field with `Algebra A K` and
`IsFractionRing A K`; `L` is a field with `Algebra K L`, `Algebra A L`, the scalar-tower
instance, finite dimensionality, and `IsGalois K L`. The residue characteristic is
rendered by `(p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]`. The integral
closure and maximal ideal are `(𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal]`.
The localized ring is assumed to be a DVR via `[hC : IsDiscreteValuationRing
(Localization.AtPrime 𝔫)]`, and the structural map is local via `[hlocal : IsLocalHom
(algebraMap A (Localization.AtPrime 𝔫))]`.

The chosen uniformizers are `πA : A` with
`hπA : IsLocalRing.maximalIdeal A = Ideal.span {πA}` and `t :
Localization.AtPrime 𝔫` with `ht : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫) =
Ideal.span {t}`. The positive integer in the node is `(e : ℕ)` with `he : 0 < e`, a
unit `u : (Localization.AtPrime 𝔫)ˣ`, and
`hπ : algebraMap A (Localization.AtPrime 𝔫) πA = (u : Localization.AtPrime 𝔫) * t ^ e`.
The largest divisor prime to `p` is rendered by `n : ℕ` together with
`hn_dvd : n ∣ e`, `hn_coprime : Nat.Coprime n p`, and
`hn_max : ∀ d : ℕ, d ∣ e → Nat.Coprime d p → d ≤ n`.
Finally, the decomposition group is `MulAction.stabilizer Gal(L / K) 𝔫` and the
inertia subgroup is `𝔫.inertia (MulAction.stabilizer Gal(L / K) 𝔫)`. The conclusion is
`Finite` for this subgroup and `∃ b : ℕ, Nat.card ... = n * p ^ b`.

The dependency declarations used are the recorded Mathlib declarations:
`Mathlib.RingTheory.DiscreteValuationRing.Basic.IsDiscreteValuationRing`,
`Mathlib.Algebra.Algebra.Defs.Algebra`,
`Mathlib.FieldTheory.Separable.Algebra.IsSeparable`,
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic.integralClosure`,
`Mathlib.RingTheory.Localization.AtPrime.Basic.Localization.AtPrime`,
`Ideal.ResidueField`, and `Ideal.Fiber` (the latter two are in the recorded
localization dependency interface). The subgroup operation is Mathlib's
`Ideal.inertia` from `Mathlib.RingTheory.Ideal.Defs`.

Edge cases checked were the trivial extension `L = K` (then the inertia subgroup can
be trivial and `n = 1`), `e = 1` (the prime-to-`p` part is one), and inseparable residue
extensions (the statement has no residue separability assumption and retains the
possible `p`-power factor). The quantifier for `n` permits `n = 1`; `b = 0` covers a
trivial `p`-part.

Searches for an existing declaration were made with:

- `msearch.py ... leanfinder` for the complete inertia-order statement: returned
  `Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.inertiaDeg_le_finrank`, and related
  ramification declarations, but all exact-order candidates require perfect/separable
  residue hypotheses and do not match this statement.
- `msearch.py ... loogle 'Ideal.card_inertia_eq_ramificationIdxIn, Ideal.inertia'`:
  returned `Ideal.card_inertia_eq_ramificationIdxIn`; its signature requires an
  `Algebra.HasSeparableDegree`/perfect-residue setting and is not an exact match.
- `msearch.py ... grep 'card_inertia|prime.*inertia|def inertia' RingTheory`:
  returned Mathlib's `Ideal.inertia` and the ramification/inertia degree files, with no
  complete arbitrary-residue prime-part theorem.
- Repository `rg`/`grep` searches for `inertia-order-prime-part`, `inertia`, and
  `DiscreteValuation` found no existing project declaration with this statement.

The node statement is unchanged; no statement correction, new node, dependency module,
or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q111

I read the node statement, its source place (Stacks Project `more-algebra.tex`, Tag
09EE, `lemma-galois-inertia`, first proof paragraph), the Lean module, and every
recorded statement dependency.

The node's objects and hypotheses match the Lean as follows. The DVR `A` with fraction
field `K` is `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`
and `(K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]`. The finite normal
separable extension `L/K` is `(L : Type w) [Field L] [Algebra K L] [Algebra A L]`
with `[IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]`; `IsGalois`
supplies normality and separability, while finite dimensionality supplies finiteness.
The residue characteristic `p > 0` is `(p : ℕ) [Fact p.Prime]` and
`[CharP (IsLocalRing.ResidueField A) p]`, which is equivalent to the source's
positive prime characteristic. The integral closure `B` is the Mathlib subalgebra
`integralClosure A L`, and the maximal ideal `𝔫` is
`(𝔫 : Ideal (integralClosure A L)) [𝔫.IsMaximal]`. The localization `C = B_𝔫`
is `Localization.AtPrime 𝔫`, with `[hC : IsDiscreteValuationRing ...]` and the
local structural map `[hlocal : IsLocalHom (algebraMap A ...)]`.

The uniformizers are `πA : A` and `t : Localization.AtPrime 𝔫`, rendered by
`hπA : maximalIdeal A = Ideal.span {πA}` and
`ht : maximalIdeal (Localization.AtPrime 𝔫) = Ideal.span {t}`. The positive
ramification exponent is `(e : ℕ) (he : 0 < e)`, with unit `u` and equation
`hπ : algebraMap A ... πA = (u : ...) * t ^ e`. The largest divisor prime to `p`
is rendered by `n`, `hn_dvd`, `hn_coprime`, and
`hn_max : ∀ d, d ∣ e → Nat.Coprime d p → d ≤ n`; these clauses jointly express
exactly the source's maximality condition, including `n = 1`.

The decomposition group `D` is expanded as
`MulAction.stabilizer Gal(L / K) 𝔫`, and the inertia group `I` is expanded as
`𝔫.inertia (MulAction.stabilizer Gal(L / K) 𝔫)`. Mathlib's `Ideal.inertia` is
the subgroup whose elements act trivially modulo `𝔫`, so it is the source's
restriction-to-`B/𝔫` kernel. The conclusion has both source clauses: `Finite I`
and `∃ b : ℕ, Nat.card I = n * p ^ b`. No hypothesis is added or dropped, and
the residue extension remains unrestricted (it need not be separable).

The five proof clauses in the node are rendered in the theorem docstring: finite
Galois group and degree data; orbit/stabilizer coset counting; normal residue action
and inertia kernel; the normal-field degree factorization; and the kernel-fibre count
followed by prime factorization. The named proof dependencies are retained in that
docstring (`lem-weil-pbc-finite-galois-fixed-field`,
`lem-exc-dvr-galois-degree-data`, `lem-exc-dvr-residue-normal-action`, and
`lem-exc-normal-field-degree-factors`).

Edge cases checked: the trivial extension `L = K` gives trivial inertia and permits
`n = 1`, `b = 0`; `e = 1` likewise gives prime-to-`p` part one; `n = 1` is allowed
by the divisor clauses; arbitrary and inseparable residue extensions are allowed;
and the characteristic hypothesis forces a genuine prime `p`, with no zero or
negative characteristic case silently included. Universes `u`, `v`, and `w` are
explicit and the index-free statement excludes no source case.

I repeated the existing-declaration searches with `msearch.py` (LeanFinder and
Loogle), direct grep through Mathlib and `WeilConjectures/`, and grep through
`lean/Sheaf`. The searches found Mathlib's general `Ideal.inertia` and related
ramification formulas, but no theorem asserting this arbitrary-residue
prime-to-characteristic order formula. No project or upstream declaration matches
the complete statement, so the module is required.

The only mismatch found was documentary: the worker docstring summarized the proof
instead of carrying the node's five proof steps and dependency names. I replaced it
with the step-by-step proof documentation above. The Lean signature itself required
no change, and compilation with `scompile.py` is clean.

## Earlier second reading (a previous round; superseded)

Read the target node and module independently. The theorem has exactly the target's
DVR, fraction-field, finite normal separable extension, integral-closure maximal ideal,
localization, local-map, uniformizer, ramification exponent, prime-to-`p` divisor, and
inertia-order clauses. `Ideal.inertia` is the Mathlib subgroup of automorphisms acting
trivially modulo the maximal ideal, matching the node's restriction-to-`B/𝔫` definition.
No mismatch was found and no change was required.
