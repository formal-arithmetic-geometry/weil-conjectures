## Worker report

The module `Sheaf.RingTheory.ArtinReesPrincipalColengthDifference` states
`IsLocalRing.exists_artinRees_principal_colength_difference`, with one postponed proof
(`sorry`), no new definitions, and no changes to the informal statement or dependencies.
It states the Artin--Rees intersection inclusion, the finite middle colength, the
scalar-restriction length equalities, and the length difference equality and bound.

Source read: `literature/stacks-project/algebra.tex`, lemma-Artin-Rees (Tag 00IN,
lines 12186–12218), lemma-length-independent (Tag 00IX, lines 12444–12458),
lemma-hilbert-ses (Tag 00K6, lines 14087–14130), and proposition-dimension (Tag 00KQ,
lines 14520–14600). The last argument uses the injective multiplication-by-x sequence
in the domain obtained by quotienting a prime. The item's six-step proof specializes
this argument to the indicated local domain. The declaration docstring reproduces
all six steps, including the quotient maps, cancellation, and finiteness argument.

Hypotheses and clauses, matched individually:

- A nonzero commutative Noetherian local integral domain is `(A : Type u)` with
  `[CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]`.
  Both `IsDomain` and `IsLocalRing` include nontriviality; no redundant nonzero binder
  is needed. The universe `u` is explicit and unrestricted.
- The element is `(x : A)`, with `(hx : x ≠ 0)` and
  `(hxm : x ∈ maximalIdeal A)`. This excludes units, zero, and the field case for A.
- B is literally `A ⧸ Ideal.span {x}`; `Ideal.span {x}` is the principal ideal xA.
  The ideal b is literally `(maximalIdeal A).map (Ideal.Quotient.mk (Ideal.span {x}))`.
  Thus the ring and quotient map are canonical, without an arbitrary algebra or map.
  The first conclusion is `IsLocalRing B` (including nonzeroness), and the second is
  `b.IsMaximal`. They render the node's assertion that B is nonzero local with maximal
  ideal b = aB. The properness follows from x ∈ a and is not an extra hypothesis.
- H_A(n) is `Module.length A (A ⧸ maximalIdeal A ^ n)`.
  H_B(n) is `Module.length B (B ⧸ b ^ n)`. Neither function is separately redefined.
  `hA` and `hB` state that each is `< ⊤` for every natural n with `1 ≤ n`, exactly
  the assumed finiteness range in the node.
- `∃ c : ℕ, 1 ≤ c ∧ ∀ n : ℕ, c < n → ...` gives one integer c ≥ 1 and every
  integer n > c. Natural indexing is equivalent to integer indexing on this positive
  range. In particular n-c ≥ 1, so both finiteness hypotheses cover the lengths used.
- `Ideal.span {x} ⊓ maximalIdeal A ^ n ≤
  maximalIdeal A ^ (n-c) * Ideal.span {x}` renders the first displayed inclusion.
  Ideal multiplication is the ideal a^(n-c)xA, and infimum is intersection.
- The middle quotient is `xA ⧸ Submodule.comap (Submodule.subtype xA) (a ^ n)`:
  the preimage consists exactly of those elements of xA that also belong to a^n,
  hence this is xA/(xA ∩ a^n), not A/(xA ∩ a^n). Explicit `Submodule` operations
  distinguish the inclusion of modules from ideal ring-hom operations. Its
  `Module.length A ... < ⊤` is the middle-quotient finiteness clause.
- The next two equalities assert `length_A(B/b^n) = length_B(B/b^n)` and
  `length_A(A/(xA + a^n)) = length_B(B/b^n)`. The sum ideal is written `⊔`.
  These record precisely the final scalar-restriction/quotient-identification clause.
- The next equality is `H_B(n) = H_A(n) - length_A(xA/(xA ∩ a^n))`.
- The last inequality is `H_B(n) ≤ H_A(n) - H_A(n-c)`.
  All lengths use `Module.length : ℕ∞`. Their finiteness makes subtraction the
  ordinary truncated subtraction of finite integers; exactness gives that the
  subtracted middle length is at most H_A(n). No conversion at infinity occurs.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, and the characterization `isNoetherianRing_iff_ideal_fg`.
  The recorded definition says every ideal is finitely generated, exactly the node.
- `def-weil-pbc-module-length`: its Mathlib match `Mathlib.RingTheory.Length`,
  `Module.length` (lines 30–36), and `Module.length_ne_top_iff` (line 94).
  Length is the dimension of the submodule lattice, equivalent to the node's
  supremum of strict-chain lengths. A missing lean record is not a missing definition.
- Proof dependency `lem-weil-pbc-artin-rees`: Mathlib match
  `Ideal.exists_pow_inf_eq_pow_smul`, `Mathlib.RingTheory.Filtration`, lines 388–392.
  This module is imported without `public` for the future proof.
- Proof dependency `lem-weil-pbc-length-additive-short-exact`: Mathlib match
  `Module.length_eq_add_of_exact`, `Mathlib.RingTheory.Length`, lines 164–172.
  The declaration takes injectivity, surjectivity, and exactness of the two linear maps.
  `Module.length_eq_of_surjective` (same module, lines 137–143) also supplies the
  scalar-restriction clause in step 2. All recorded dependency interfaces are usable.

Edge cases checked before writing:

- A field has maximal ideal zero and admits no x satisfying both element hypotheses.
  The zero ring is excluded by the node and by the typeclasses.
- A DVR A = k[[t]], x = t^e, e ≥ 1, has H_A(n) = n and H_B(n) = min(e,n).
  Take c=e. For n>e the intersection is (t^n), the middle quotient has length n-e,
  and both difference formulas give e. The e=1 case explicitly allows B to be a field
  with b=0; it is not excluded.
- A = k[[s,t]], x = s has H_A(n)=n(n+1)/2 and H_B(n)=n. Taking c=1 makes the
  difference bound an equality. This rules out an accidental dimension-one restriction.
- n=0 and n=c are outside the asserted conclusion, as in the node; n=c+1 uses
  the defined finite length H_A(1), so no undefined or negative exponent is introduced.

Searches run using `batch2/msearch.py`, plus direct project searches:

- LeanFinder: `Artin Rees principal ideal colength difference bounds length of local
  domain quotient by nonzero x`. Eight hits, including
  `isFiniteLength_quotient_span_singleton` and regular-element Krull dimension lemmas.
  They are stronger-hypothesis finite-length or dimension statements, not this estimate.
- Loogle: `"length", "pow", "quotient"`. One hit:
  `IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`, the DVR specialization,
  not the present arbitrary local-domain result.
- Mathlib grep (RingTheory): `length.*sub|sub.*length|exists_pow_inf_eq_pow_smul`.
  Twenty-five displayed hits, including module length, length additivity, restriction
  of scalars, and Artin--Rees. These supply ingredients, not the whole statement.
- LeanSearch: `Artin Rees principal quotient length difference bound maximal ideal
  powers local domain`. Eight hits, including `Ideal.exists_pow_inf_eq_pow_smul` and
  dimension bounds. No exact declaration or one-line specialization.
- `rg -n 'colength|principal_colength|length.*sub|artin.rees'` in both project roots
  `lean/WeilConjectures` and `lean/Sheaf` found supporting length material and the
  HilbertSamuelGrowthDimension proof plan, but no theorem stating this result.
  `grep -rn 'lem-trf-artin-rees-principal-colength-difference' lean/WeilConjectures`
  found no owning declaration. No private copy of a notion was introduced.

Validation: all compilation uses the prescribed `scompile.py`. The explicit
`Submodule.comap`/`Submodule.subtype` names repair Lean's resolution of ideal
operations. `set_option autoImplicit false` enforces explicit binding of all variables.
The final server compile and delivery preflight results are recorded by the delivery
wrapper. No node correction, dependency repair, new node, or disputed statement.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
