## Worker report

The module `Sheaf.NumberTheory.FrobeniusRootsOfUnityPower` states all three clauses of
`lem-pur-frobenius-roots-of-unity-power` in the single theorem
`WeilConjectures.FiniteFieldDatum.frobenius_rootsOfUnity_power`. Its proof is `sorry`.
No definitions, instances, other nodes, or statement corrections are introduced.
The declaration docstring supplies a complete natural-language proof. The node's own
`proof` and `proof_deps` arrays are empty and are preserved.

Hypothesis and clause correspondence:

- `D : WeilConjectures.FiniteFieldDatum.{u}` is the recorded global tuple. Its fields
  `p`, `prime`, `a`, `exponent_pos`, `q`, `cardinality_eq`, `k₀`, `field_base`,
  `finite_base`, and `card_base` give a finite field with `q = p ^ a` elements and
  `p` prime, `a ≥ 1`. Its `k`, `field_closure`, `algebra_closure`, and `isAlgClosure`
  give the fixed algebraic closure with its base embedding. No characteristic,
  splitting, or root-existence assumption is added.
- Arithmetic Frobenius is the dependency's exact
  `FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k`. The signature supplies its
  finite enumeration explicitly with `Fintype.ofFinite D.k₀` using `@`; this is
  constructed from `D.finite_base`, not an extra binder or assumption.
  `.symm` is the geometric Frobenius, precisely its inverse as required.
- `(N : ℕ) (hN : 1 ≤ N) (hNp : N.Coprime D.p)` expresses the positive integer
  prime to `p`. Natural numbers represent exactly the allowed positive integers.
  `rootsOfUnity N D.k` is Mathlib's subgroup of units whose `N`-th power is one.
- Clause 1 is the first conjunct: `IsCyclic (rootsOfUnity N D.k)`,
  `Nat.card (rootsOfUnity N D.k) = N`, and, for every
  `σ : D.k ≃+* D.k`, `Set.BijOn (Units.map σ.toRingHom.toMonoidHom)` of this
  subgroup onto itself. These are all field automorphisms, without a requirement
  to fix `D.k₀`. Bijectivity on the invariant set is equivalent to the source's
  stability under every automorphism: applying stability to `σ.symm` gives
  surjectivity, and field automorphisms are injective.
- Clause 2 is the second conjunct. For every `ζ : rootsOfUnity N D.k`, evaluation
  of the arithmetic Frobenius in the field equals `ζ ^ D.q`. The casts from the
  root subgroup through units to the field preserve the same element.
  `∃ q' : ℤ, Int.ModEq (N : ℤ) ((D.q : ℤ) * q') 1` states the asserted existence
  of an inverse exponent. The subsequent `∀ q' : ℤ` with that congruence
  states the geometric formula for *any* such integer and every root. The formula
  is an equality in `D.kˣ`, so `^ q'` is integer exponentiation and includes
  negative exponents without imposing a nonnegativity hypothesis.
- Clause 3 universally quantifies `(ℓ : ℕ) [Fact ℓ.Prime]` and assumes
  `ℓ ≠ D.p`. Its module is `AddCommGroup.tateModule ℓ (Additive D.kˣ)`, exactly
  the defining expression of the upstream `cyclotomicTateModule D.k ℓ`.
  Its elements are systems `t : ℕ → Additive D.kˣ` satisfying
  `(ℓ : ℤ) ^ r • t r = 0` and `(ℓ : ℤ) • t (r + 1) = t r`. These are
  precisely the required inverse limit of `μ_(ℓ^r)` with power-`ℓ` transitions.
  Its existing `AddCommGroup.tateModule.instModule` is the canonical p-adic
  scalar structure, acting at level `r` by reduction modulo `ℓ ^ r`.
  `Nonempty (... ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ])` expresses free of rank one, without
  selecting a generator. `∃ u : ℤ_[ℓ]ˣ, (u : ℤ_[ℓ]) = (D.q : ℤ_[ℓ])`
  asserts exactly that the scalar `q` is a unit. The two equations for every
  `t` identify the arithmetic and geometric actions with `(u : ℤ_[ℓ]) • t`
  and `(↑(u⁻¹) : ℤ_[ℓ]) • t`. The units are determined by their value `q`;
  this existential does not replace Frobenius by an arbitrary action.
  Both actions are the canonical `AddCommGroup.tateModule.map` applied to
  `Units.map` of the given field automorphism, with `.toAdditive`. Its defining
  function is coordinatewise application of that automorphism, so the required
  componentwise action is specified in the statement itself.

Dependencies read and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum`, including its full structure fields,
  docstring, and published field/algebra/closure instances.
- `def-weil-frobenius-substitution` is a Mathlib leaf; its `mathlib_match` names
  `FiniteField.frobeniusAlgEquivOfAlgebraic` in
  `Mathlib.FieldTheory.Finite.Basic`. Its full signature, docstring and
  `FiniteField.coe_frobeniusAlgEquivOfAlgebraic` were read. The latter identifies
  evaluation with raising to the cardinality. Geometric Frobenius is `.symm`.
- `def-weil-l-adic-numbers` is a Mathlib leaf. Read `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers` and `PadicInt` in
  `Mathlib.NumberTheory.Padics.PadicIntegers`, with their full definitions and
  docstrings. `ℤ_[ℓ]` is `PadicInt ℓ`, the valuation ring, not `ℚ_[ℓ]`.
  The p-adic imports are public through `WeilConjectures.GroupTheory.TateModule`.
- Other existing notions used: `rootsOfUnity` and its cyclic group interface
  in `Mathlib.RingTheory.RootsOfUnity.Basic`; `AddCommGroup.tateModule`,
  `AddCommGroup.tateModule.instModule`, `AddCommGroup.tateModule.map`, and
  `AddCommGroup.tateModule.coe_map_apply` in
  `WeilConjectures.GroupTheory.TateModule`. Read their full definitions and
  docstrings. Also read the definition/docstring of `cyclotomicTateModule` in
  `WeilConjectures.NumberTheory.TateModule`. Its defining expression is used
  directly because instance search does not unfold this ordinary definition
  when seeking its canonical p-adic module. This is the existing construction,
  with no replacement definition or instance.

Source validation: read the actual local PDFs, Deligne Weil I (2.2) on printed
pp. 280--281 (PDF pp. 9--10), defining the projective system and its transitions,
and giving arithmetic Frobenius scalar `q`; Weil II (1.1.7), printed
pp. 150--151 (PDF pp. 15--16), fixes arithmetic and geometric conventions.
Also read the current main-20261015 blueprint's
`sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md`:
its geometric action `q⁻¹` agrees with the statement.

Edge cases checked before writing:

- `N = 1`: the root subgroup is trivial, cyclic of cardinality one. Congruence
  modulo one holds for every integer, including zero and negative integers;
  every displayed power formula remains true.
- `N = 0` is excluded by the source's positivity, exactly `hN`.
- Negative inverse exponents are included using powers of units.
- `p = 2`, `ℓ = 2` when `p ≠ 2`, and `a = 1` are included. The coefficient prime
  equals the characteristic only in the explicitly excluded case `ℓ = D.p`.
- Level `r = 0` is present in the upstream Tate module and is `μ_1 = {1}`;
  adjoining this uniquely determined coordinate does not restrict the limit.
- The arbitrary universe `u` of the recorded global datum is retained. No
  independently small index or test-object universe, chosen closure model,
  Fintype assumption, or preferred primitive root is imposed.

Searches made (2026-10-16):

- `msearch.py ... leansearch "Arithmetic Frobenius on roots of unity and cyclotomic
  Tate module over algebraic closure of finite field"`: eight hits, including
  `FiniteField.frobeniusAlgEquivOfAlgebraic`, its evaluation lemmas, and
  `cyclotomicCharacter.spec`; no declaration states all three clauses.
- `msearch.py ... leanfinder "Arithmetic Frobenius acts on roots of unity by power q
  and on cyclotomic Tate module by scalar q"`: eight hits, including
  `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`, modular cyclotomic-character
  specifications, and `cyclotomicCharacter`; these do not give the whole result.
- `msearch.py ... loogle "rootsOfUnity, cyclotomicCharacter,
  frobeniusAlgEquivOfAlgebraic"`: zero hits, diagnostic unknown identifier
  `frobeniusAlgEquivOfAlgebraic`.
- `msearch.py ... grep "frobenius.*(rootsOfUnity|cyclotomic)|cyclotomic.*frobenius"`:
  zero Mathlib hits.
- Direct `rg` searches for `frobenius`, `TateModule`, `tateModule`, and
  `rootsOfUnity` in the project and upstream found the existing Tate module,
  `WeilConjectures.Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter`, and
  `WeilConjectures.WeilSheaf.TateTwist`. Read these relevant declarations.
  `cyclotomicCharacter_frobeniusEquiv_pow` and its inverse formula concern
  the character of an iterated characteristic Frobenius, not the full finite-level
  and module-rank statement. `cyclotomicUnit_eq` concerns a scalar in the
  algebraic closure of `ℚ_[ℓ]`, not the integral Tate module.
- Direct upstream search for `lem-pur-frobenius-roots-of-unity-power`, and searches
  in `dag/lean_names_upstream.json`, the upstream project and `lean/Sheaf` for
  `frobenius_rootsOfUnity_power` found no existing aggregate declaration.

The first `scompile.py` run diagnosed the module-instance unfolding issue above.
Using the upstream defining expression repaired it. The final file passed both
sandbox and module-path compilation through `scompile.py`, with no warnings or
errors. The required delivery dry-run command is
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q51
lem-pur-frobenius-roots-of-unity-power --no-push`; it is currently running through
the shared delivery queue. The independent second reader supplies their own
reading and performs the actual delivery.

## Second reading by Q51

I independently opened the node copy and `Sheaf/NumberTheory/FrobeniusRootsOfUnityPower.lean`,
then checked the source conventions in Deligne Weil I (2.2), Weil II (1.1.7), the current
cyclotomic blueprint section `sk-d-ab-cyclotomic`, and the Stacks Project definitions of roots
of unity (`fields.tex`, Section `section-roots-of-1`) and arithmetic/geometric Frobenius
(`trace.tex`, definitions `definition-arithmetic-frobenius` and
`definition-geometric-frobenius-on-stalk`). The item-by-item comparison is:

1. The Lean binder `D : FiniteFieldDatum.{u}` renders the fixed tuple
   `(p,a,q,k₀,k)` and its field, finite-cardinality, algebra-closure, and
   `q = p^a` data. The binders `N`, `hN : 1 ≤ N`, and `hNp : N.Coprime D.p` render
   `N ≥ 1` prime to the characteristic. The first conjunct renders that
   `rootsOfUnity N D.k` is cyclic, has cardinality `N`, and is carried bijectively
   to itself by every field automorphism `σ : D.k ≃+* D.k`. `rootsOfUnity` is the
   units realization of `μ_N(k)`; `Set.BijOn` is equivalent here to preservation of
   the subgroup because `σ` and `σ⁻¹` are field automorphisms. Verdict: exact.
2. The first part of the second conjunct applies the recorded
   `FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k`, whose evaluation is the
   `q`-power, to every root. The existential integer and the following universal
   inverse-congruence binder render existence and arbitrariness of
   `q'` with `q q' ≡ 1 (mod N)`. The inverse Frobenius is `.symm`, and the unit
   equality uses integer powers, so negative exponents are included. Verdict: exact.
3. The final conjunct binds every prime `ℓ` with `ℓ ≠ D.p`. It uses the existing
   `AddCommGroup.tateModule ℓ (Additive D.kˣ)`, whose coordinates and transition
   equation are exactly the inverse system of `ℓ^r`-th roots with
   `ζ ↦ ζ^ℓ` (the coordinate `r = 0` is the canonical trivial level). The
   `Nonempty` linear equivalence is freeness of rank one over `ℤ_[ℓ]`; the unit
   `u` is fixed by `(u : ℤ_[ℓ]) = D.q`; and the two coordinatewise
   `AddCommGroup.tateModule.map` equations give arithmetic scalar `q` and
   geometric scalar `q⁻¹`. Verdict: exact.

The empty-index case does not occur: `N = 0` is excluded by `hN`, while `N = 1`
is included and gives the trivial cyclic subgroup and valid congruences. The zero
Tate-module coordinate at level `r = 0`, negative inverse exponents, `p = 2`,
`ℓ = 2` when allowed, and `a = 1` are all covered. No independent universe,
Noetherian/finiteness hypothesis, chosen primitive root, or extra characteristic
assumption is introduced; the only finiteness is the recorded finite base field.

I repeated the three required existing-declaration searches: `msearch.py` LeanFinder
for Frobenius on roots and the Tate module, Loogle for `rootsOfUnity`/cyclotomic
Frobenius, and direct `rg` over Mathlib, `WeilConjectures/`, and `lean/Sheaf`.
They returned only the component declarations (`frobeniusAlgEquivOfAlgebraic`,
`rootsOfUnity`, `tateModule`, and cyclotomic-character infrastructure), never this
three-clause statement. The recorded dependency declarations were opened and used;
there is no duplicate definition or dependency interface repair.

No mismatch was found, so no Lean or node statement was changed. The module compiled
through the prescribed `scompile.py` wrapper for both sandbox and library paths, with
no errors or warnings. The only postponed proof remains the named theorem
`frobenius_rootsOfUnity_power`, with the source and blueprint proof steps in its
docstring.
