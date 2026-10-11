## Worker report

The module `Sheaf.RingTheory.CmModuleGoodElementNonzerodivisor` states
`Module.cm_module_good_element_nonzerodivisor`, with its sole proof `sorry`.
The source is [Stacks Tag 00N5](https://stacks.math.columbia.edu/tag/00N5),
Lemma 10.103.3, and the Cohen–Macaulay equality in Tag 00N3. The local literature
copy is absent on this machine, so the source lemma and its proof were read online.
No node correction or new notion is needed: the node itself defines
Cohen–Macaulay by an equality, which is rendered inline rather than duplicated.

Hypotheses and clauses, in order:

- A commutative Noetherian local ring `(R,m)` is `{R : Type u} [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`; `m` is `IsLocalRing.maximalIdeal R`.
- The finite module is `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. Nonzero is `[Nontrivial M]`.
- Support of any module is `Module.support R M`. Its defining nonzero
  localization is exactly `Nontrivial (LocalizedModule p.asIdeal.primeCompl M)`.
- Dimension of support is `Module.supportDim R M`, which unfolds to
  `Order.krullDim (Module.support R M)`. This is the supremum of finite strict
  prime-chain lengths, with bottom for an empty support.
- Cohen–Macaulay is `hCM : (IsLocalRing.depth (R := R) M : WithBot ℕ∞) =
  supportDim R M`. The coercion embeds natural-number-or-infinity depth into
  natural-number-or-infinity dimension with an additional bottom element.
- The element is `(g : R)` with `hg : g ∈ IsLocalRing.maximalIdeal R`.
  `V(g)` is `PrimeSpectrum.zeroLocus ({g} : Set R)`.
- The dimension-drop hypothesis is `hdim : Order.krullDim (support R M ∩
  PrimeSpectrum.zeroLocus ({g} : Set R)) + 1 = supportDim R M`.
  Under the ring/module hypotheses all these dimensions are finite; the maximal
  ideal lies in this intersection, so the dimension is nonnegative. Thus this
  successor equality is exactly the stated integer drop by one. It correctly
  rules out dimension zero, unlike subtraction on natural numbers.
- Clause (a) is `Function.Injective (fun m : M => g • m)`.
- In clause (b), `QuotSMulTop g M` is the actual module `M/gM`, not an arbitrary
  quotient or extra parameter. Its Cohen–Macaulay property is the same coerced
  depth/support-dimension equality. Its depth drop is
  `IsLocalRing.depth (R := R) (QuotSMulTop g M) + 1 =
  IsLocalRing.depth (R := R) M`. Finite depths and positive original dimension
  make this equivalent to the stated subtraction by one.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`: every ideal finitely
  generated, the record of def-weil-pbc-noetherian-ring.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule` and
  `LocalizedModule.mkLinearMap`: the mathlib_match of
  def-weil-pbc-module-localization, used through `Module.support`'s definition.
- `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`: the mathlib_match of
  def-weil-finitely-generated-module. Its defining condition is `(⊤ : Submodule
  R M).FG`. Quotient finiteness is supplied by Mathlib.
- `Sheaf.RingTheory.Depth`, `Ideal.depth` and `IsLocalRing.depth`: the landed
  declaration of def-weil-pbc-depth. Read the full definitions: supremum of
  regular-sequence lengths, infinity when `I • ⊤ = ⊤`, and local specialization.

No private definitions, additional hypotheses, or omitted clauses. Universes `u`
and `v` are explicit and independent. The docstring follows all nine proof steps
of the node and names their DAG dependencies; no proofs were attempted.

Edge cases checked: the zero module is explicitly excluded; the zero ring cannot
have a nonzero module. Dimension zero is impossible since the maximal ideal lies
in Supp(M) ∩ V(g), so its dimension plus one cannot be zero. For `g = 0` on a
nonzero finite module, the support is unchanged and the drop hypothesis fails.
Units are excluded by maximal-ideal membership. The depth-zero quotient in
original dimension one is allowed. There is no field-characteristic restriction
and no universe identification. The extended dimension type retains bottom for
empty sets and infinity for general sets; neither leads to extra cases under the
Noetherian local finite-module hypotheses.

Searches performed with msearch.py (group J1, this item):

- LeanFinder: "Cohen Macaulay finite module local ring element cuts support
  dimension by one is injective quotient depth drops one". Eight hits: regular
  elements imply dimension drops and minimal-prime avoidance implies a drop;
  none gives the Cohen–Macaulay converse or the quotient depth assertion.
- Loogle: "Module.supportDim, RingTheory.Sequence.IsRegular". One hit,
  `Module.supportDim_add_length_eq_supportDim_of_isRegular`, the regular-sequence
  dimension formula; not this theorem.
- Mathlib grep: "CohenMacaulay|Cohen.Macaulay|supportDim_quotSMulTop" in RingTheory.
  Five hits, all dimension-drop results in KrullDimension/Regular; no CM theorem.
- LeanSearch: "Cohen Macaulay module element dimension support drops one
  nonzerodivisor". Unavailable (Internal Server Error); no absence inferred.
- rg in WeilConjectures and lean/Sheaf: "supportDim|CohenMacaulay|
  IsCohenMacaulay|def depth", then "Cohen|supportDim|depth". Only Depth,
  SerreConditions, and unrelated source comments; no matching theorem or CM def.
- rg in WeilConjectures and dag/lean_names_upstream.json for the item id,
  `cm_module_good_element`, and `CohenMacaulay`: no matching declaration.
  The selected declaration name is absent from those sources and Mathlib.

Validation: server single-file compile and deliver2.py --no-push are run for this
sandbox. The independent second reader supplies their own section after handoff.

## Second reading by J1

I independently opened the node and `Sheaf/RingTheory/CmModuleGoodElementNonzerodivisor.lean` and matched the signature clause by clause. The introduced objects and verdicts are:

- The commutative Noetherian local ring `(R, m)` is rendered by `{R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]`; the maximal ideal is the canonical `IsLocalRing.maximalIdeal R`, with no extra ring hypothesis.
- The finite nonzero module `M` is rendered by `(M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]`. The two universes are independent, so no case is excluded.
- Cohen–Macaulayness is exactly the node's equality `depth(M) = dim Supp(M)`, rendered as `(IsLocalRing.depth (R := R) M : WithBot ℕ∞) = supportDim R M`.
- The element and membership hypothesis are exactly `(g : R)` and `hg : g ∈ IsLocalRing.maximalIdeal R`.
- The support intersection with `V(g)` is rendered by `support R M ∩ PrimeSpectrum.zeroLocus ({g} : Set R)`, and the dimension-drop hypothesis is the node's successor equality `Order.krullDim (...) + 1 = supportDim R M`; this preserves the empty-support/bottom convention and avoids truncated subtraction.
- Clause (a), injectivity of multiplication by `g`, is exactly `Function.Injective (fun m : M => g • m)`.
- Clause (b)'s quotient is the actual `QuotSMulTop g M` (the module `M/gM`), and its two clauses are rendered exactly by the coerced Cohen–Macaulay equality and `depth (M/gM) + 1 = depth M`.

No hypothesis, object, quantifier, or conclusion clause was added, dropped, strengthened, or weakened. The signature compiled unchanged with `scompile.py`; no repair was needed. I checked the source place (Stacks Tag 00N5, with Tag 00N3) and the recorded dependency declarations, including `Module.support`, `Module.supportDim`, `LocalizedModule`, `Module.Finite`, and `IsLocalRing.depth`. The dependency records provide the notions used; no private duplicate or new node is needed.

Edge cases were checked explicitly: `Nontrivial M` excludes the zero module as required; a zero ring cannot supply such a module; `g = 0` fails the dimension-drop hypothesis for a nonzero module; units are excluded by maximal-ideal membership; dimension zero is excluded by the successor equality and the maximal ideal in the intersection; depth-zero quotients in original dimension one remain allowed; empty supports retain `WithBot` bottom; and no characteristic or universe identification is imposed.

I repeated the existing-definition searches (LeanFinder, Loogle, LeanSearch, grep of pinned Mathlib, grep of `WeilConjectures`, and grep of `lean/Sheaf`). They found only the regular-sequence/support-dimension lemmas and the project's `Depth` declaration, with no Cohen–Macaulay good-element theorem or duplicate declaration. Therefore the module and node declaration are new and correctly recorded.
