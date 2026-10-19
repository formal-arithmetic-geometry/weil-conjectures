## Worker report

Item: `lem-trf-ordered-group-prime-ideal-convex-correspondence` (Q27, stage 2).

The module `lean/Sheaf/GroupTheory/OrderedGroupPrimeIdealConvex.lean` states
`AddSubgroup.orderedGroup_primePositiveConeIdeal_orderDualEquiv_convexAddSubgroup`.
Its sole proof is `sorry`, as required in stage 2. It introduces no definitions,
instances, helper theorems, axioms, or file-local notation. The families are written as
explicit subtypes, so the notions introduced inline in the node remain inline in Lean.
Only the item's `lean` field changes; its signature is copied verbatim from the module.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Any totally ordered abelian group Γ | `{Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]`, with `universe u` explicitly declared. |
| A subset of the nonnegative cone | `I : Set Γ` with `∀ ⦃x : Γ⦄, x ∈ I → 0 ≤ x`. Representing a subset of the cone as an ambient set contained in it changes neither objects nor inclusion. |
| Upward closed in the cone | `∀ ⦃x y : Γ⦄, x ∈ I → x ≤ y → y ∈ I`. Since membership implies `0 ≤ x`, the bound on `y` follows by transitivity. There is no additional closure condition on negative elements. |
| Zero is not in a prime ideal | `0 ∉ I`. |
| Primality for nonnegative summands | `∀ ⦃x y : Γ⦄, 0 ≤ x → 0 ≤ y → x + y ∈ I → x ∈ I ∨ y ∈ I`. |
| Subgroups of Γ | Mathlib's `AddSubgroup Γ`, including exactly zero, addition, and negation closure. |
| Convexity between subgroup elements | `∀ ⦃h₁ h₂ x : Γ⦄, h₁ ∈ H → h₂ ∈ H → h₁ ≤ x → x ≤ h₂ → x ∈ H`. |
| Both families ordered by inclusion | Inherited subtype orders from `Set Γ` and `AddSubgroup Γ`; Mathlib defines both orders by inclusion. |
| Canonical order anti-isomorphism | `∃ e : (prime-ideal subtype)ᵒᵈ ≃o (convex-subgroup subtype)`. The order dual reverses ideal inclusion; the `OrderIso` includes inverse identities and order preservation/reflection. |
| Ideal I maps to `H_I = {γ : abs γ ∉ I}` | `∀ I γ, γ ∈ (e (OrderDual.toDual I)).1 ↔ abs γ ∉ I.1`, written using `|γ|` in the file. This quantifies over every group element, including negative ones. |
| Subgroup H maps to `I_H = {γ ≥ 0 : γ ∉ H}` | `∀ H γ, γ ∈ (e.symm H).1 ↔ 0 ≤ γ ∧ γ ∉ H.1`. Both the nonnegativity and complement conditions are explicit. |
| Absolute value is the larger of γ and -γ | Mathlib `abs` on a linearly ordered additive group, with no normed-space or scalar structure. |

Both formulas constrain the same `e` and its actual inverse. They determine the maps
pointwise, so the existential does not assert an arbitrary unspecified bijection.
No nontriviality, Archimedean, divisibility, discreteness, or inhabited-ideal assumption
is imposed.

Dependency and source inspection:

- Read the entire item, its seven proof steps, and its only statement/proof dependency
  `def-trf-totally-ordered-abelian-group`, including the `mathlib_match` record.
- Read `Mathlib/Algebra/Order/Group/Defs.lean`. The former class name
  `LinearOrderedAddCommGroup` is now a namespace; the node's recorded combination
  `AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid` is exactly the intended structure.
  The module explicitly imports this dependency source.
- Read `Mathlib/Algebra/Group/Subgroup/Defs.lean`, including the `AddSubgroup` signature,
  its docstring, and the induced set-like partial order. Also use
  `Mathlib.Algebra.Order.Group.Abs` for `abs` (its module docstring and the imported
  `abs_eq_max_neg` declaration identify this with `max γ (-γ)`) and `Mathlib.Order.Hom.Basic` for `≃o`.
- Opened `literature/stacks-project/algebra.tex` at `definition-value-group` and the
  preceding valuation-group lemma. These supply the conventions and explicitly allow
  the zero group. The node correctly says that the correspondence itself is the
  elementary argument supplied in its proof, rather than a theorem quoted from 00IE.
- The declaration docstring carries the source, blueprint id, and complete proof:
  absolute-value inequalities, the subgroup-to-ideal construction, downward/additive
  closure of the complement, subgroup and convexity checks, inverse formulas, and
  reversal of inclusions.

Edge cases checked mathematically before finalizing the signature:

- Γ = {0}: the unique prime cone ideal is empty and the unique subgroup is Γ; both
  formulas hold. Neither `Nontrivial Γ` nor nonempty ideals may be assumed.
- I empty corresponds to the full subgroup; H full corresponds to the empty ideal.
- H = {0} corresponds to the strictly positive cone, whose complement under absolute
  value is precisely {0}. This also covers the trivial group.
- Γ = ℤ and Γ = ℚ with their usual orders have the two endpoint subgroups and their
  corresponding ideals. The proof uses no discrete or Archimedean property.
- In lexicographically ordered ℤ × ℤ, the nontrivial proper convex subgroup
  {0} × ℤ corresponds to nonnegative elements with positive first coordinate. This
  tests inclusion reversal beyond the two endpoint cases.
- For negative γ, `H_I` uses its absolute value; `I_H` explicitly excludes γ by
  nonnegativity. Boundary γ = 0 is retained in every subgroup and excluded from ideals.

Searches for an existing declaration (all run through the prescribed wrapper unless noted):

1. `leanfinder`, query `prime positive cone ideal convex subgroup order anti-isomorphism`:
   eight hits, including `ValuationSubring.primeSpectrumOrderEquiv_apply_coe_carrier`
   and `Order.Ideal.PrimePair`; none is the ordered-group correspondence. The former
   compares prime spectra and valuation overrings, not convex subgroups of an arbitrary
   ordered group.
2. `loogle`, query `OrderIso OrderDual AddSubgroup abs`: malformed application reported;
   not evidence of absence. Repeated with valid query `AddSubgroup, OrderIso`: twelve
   hits on additive/multiplicative subgroup conversion and closure; none matches.
3. `leansearch`, query `prime ideals of the nonnegative cone of an ordered abelian group
   correspond to convex subgroups`: eight hits, including `AddGroupCone.nonneg` and
   `RingPreordering.instIsPrimeSupport`; none states the correspondence.
4. `grep`, query `ConvexSubgroup|prime.*positive.*cone` in `Algebra/Order`: zero hits.
5. `grep`, query
   `ConvexSubgroup|ConvexAddSubgroup|OrdConnected.*[Ss]ubgroup|[Ss]ubgroup.*OrdConnected|prime.*[Cc]one|[Cc]one.*prime`
   over Mathlib: zero hits.
6. Direct `rg` in the source project's `WeilConjectures/` and side project's
   `lean/Sheaf/` for prime ideals, convex subgroups, positive cones, the proposed
   declaration name, and `ConvexAddSubgroup`: no matching notion or theorem.
   The prescribed `grep -rn` of this node id in upstream returned no hit.
   The declaration-name search in `dag/lean_names_upstream.json` returned no hit.
7. Searched `dag/nodes` for positive-cone/prime/convex terminology. The hits are the
   item, its valuation-ring parent, and related rank/valuation nodes, not an existing
   definition or declaration of this correspondence.
8. Read `Order.Ideal` and `Order.Ideal.IsPrime` signatures and docstrings. They concern
   nonempty downward-closed directed order ideals and complement filters, not the
   upward-closed cone subsets with additive primality here. Reusing them would change
   the node (and discard its empty prime ideal).

No statement correction, disputed statement, dependency repair, or new node is needed.
`scompile.py Q27 lem-trf-ordered-group-prime-ideal-convex-correspondence` passed
for the delivered module, both as a sandbox file and at its library path, with
exit code 0 and no errors or warnings. Compilation and delivery gates use only
`scompile.py` and `deliver2.py`; no library or global build was run.

## Second reading by Q27

This is the worker's self-check, not an independent maintainer review. Re-read the
node and final Lean signature side by side. The group structure uses exactly the
recorded Mathlib interface; the nonnegative-subset condition is not a nonemptiness
condition; upward closure has no extra membership premise; primality has both
nonnegative hypotheses; the subgroup convexity has both endpoint memberships and
both inequalities. Re-read both displayed maps and checked their directions: `e`
takes a dual ideal to its absolute-value complement subgroup, whereas `e.symm`
takes a subgroup to its nonnegative complement ideal. These are precisely the
node's formulas, for all γ. The `OrderIso` supplies both inverse identities and
inclusion reversal through the dual domain. Corrected the initial draft's swapped
map directions and accidental redundant membership premise before compilation.
No item statement or dependency metadata changed. All binders and the universe
are explicit. There is one theorem with one `sorry`, a complete proof docstring,
no definitions containing postponed data, and every line is at most 100 characters.
The report records the failed Loogle query separately from the valid replacement.
The node's `lean.statement` is extracted verbatim through the text before `:=`.
