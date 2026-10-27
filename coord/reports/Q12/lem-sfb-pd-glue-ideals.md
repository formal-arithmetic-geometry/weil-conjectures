## Worker report

The module `Sheaf.RingTheory.DividedPowersGlueIdeals` states
`DividedPowers.coincide_mul_and_existsUnique_sup`, with its whole proof `sorry`.
The source is Stacks Project, dpa.tex, Tag 07GQ (lemma-two-ideals), both assertions
and the convolution displayed in its proof. I read that source in full, the
item's seven proof steps, and the statement dependency's definition and Mathlib
record. No definition, new node, or statement correction is needed.

Hypothesis and conclusion correspondence:

- The commutative ring is `{A : Type u} [CommRing A]`, with `universe u` explicitly
  bound; `U V : Ideal A` are arbitrary ideals.
- The ordinary divided powers are `ρ : DividedPowers U` and
  `σ : DividedPowers V`. This is exactly the recorded Mathlib match of
  `def-sfb-ordinary-divided-power-structure`, not a duplicate notion.
- The first conjunct quantifies `w ∈ U * V` and `n : ℕ` with `1 ≤ n`, concluding
  `ρ.dpow n w = σ.dpow n w`. Ideal multiplication is the product ideal UV.
- The second conjunct is an implication. Its antecedent is precisely agreement
  for every `w ∈ U ⊓ V` in every positive degree; no compatibility is assumed
  for the unconditional product-agreement conclusion.
- Its consequent uses `∃! τ : DividedPowers (U ⊔ V)`, the ideal sum U+V.
  The first two conjuncts of its predicate express restriction to ρ on U and
  σ on V, in every positive degree, respectively.
- The last conjunct quantifies every `a ∈ U`, `b ∈ V`, and every `n : ℕ` and
  gives `τ.dpow n (a+b) = ∑ i ∈ Finset.range (n+1),
  ρ.dpow i a * σ.dpow (n-i) b`. The range is exactly 0 through n.
  Including the formula in the uniqueness predicate does not restrict uniqueness
  to a smaller class of extensions: every divided-power extension obeys that
  formula by `DividedPowers.dpow_add` and its restrictions (degree zero is fixed).
- The zeroth-operation convention is supplied by `DividedPowers.dpow_zero` on
  each ideal. Mathlib's total maps are zero off their ideal, as the dependency
  node expressly permits. We never impose equality off U or V when restricting.
  Equality of structures in `∃!` is therefore equivalent to equality of the
  operations on the sum, by the fixed off-ideal extension and proof irrelevance.

Dependency declarations: `Mathlib.RingTheory.DividedPowers.Basic`, declaration
`DividedPowers` (read its full structure signature and module documentation,
including `dpow_null`, `dpow_zero`, `dpow_mem`, `dpow_add`, and `dpow_comp`).
`Nat.uniformBell` is the integral iteration coefficient of the dependency;
Bell.lean documents its factorial identity, so no division in A is introduced.
The same module already provides `DividedPowers.coincide_on_smul`, which covers
only the first clause. The theorem docstring contains the complete seven-step
proof plan. The proof-only node `lem-sfb-pd-check-generators` has no Lean record
or Mathlib match at reading time, so there is no module to import for it; it
remains explicitly cited in the proof plan. It is not needed to type this
statement. There are no other stated proof-only dependencies to import.

Edge cases checked before writing: U=0 or V=0 gives restriction of the other
structure, with positive operations at zero vanishing; U=V forces the two
structures to agree under the compatibility premise; U=V=0 and the zero ring
are admitted. No torsion-free, factorial-invertibility, domain or proper-ideal
hypothesis is imposed. For n=0 the convolution has one term, 1*1=1; n=1 gives
a+b. The product-agreement and compatibility quantifiers cover exactly positive
degrees, and formula indices n-i are natural subtraction only for i≤n. All ring
universes are allowed, and no new universe constraint occurs.

Searches for an existing full statement:

- `msearch.py leanfinder`, query “Divided powers on ideals agree on the product
  and glue uniquely on their sum when equal on intersection”: eight hits,
  including `DividedPowers.coincide_on_smul`, `DividedPowers.ext`,
  `DividedPowers.dpEqualizer`, `DividedPowers.dpow_eq_from_gens`, and quotient
  uniqueness. None constructs the extension to the sum from two structures.
- `msearch.py loogle`, query `"DividedPowers", "sup"`: six hits. In particular
  `DividedPowers.isSubDPIdeal_sup` assumes a common ambient divided-power
  structure; it is not the required gluing theorem.
- `msearch.py grep`, query `glue|coincide|sup`, subdirectory
  `RingTheory/DividedPowers`: ten hits, only the same product-agreement theorem
  and sub-divided-power ideal supremum machinery relevant. I read Basic.lean's
  definition and the complete signature/proof of `coincide_on_smul`.
- `rg -n 'DividedPowers|divided.power|pdGlue|glue_ideals'` in the project's
  `lean/WeilConjectures` and `lean/Sheaf`: unrelated graded/Lie-theoretic and Tor
  mentions; no ordinary ideal gluing statement. Searching the item's ID in
  `lean/WeilConjectures` found no occurrence. The requested old compact-object
  example is withdrawn; its node now records the upstream module, which I read
  for the public module/header conventions.

Validation: `scompile.py Q12 lem-sfb-pd-glue-ideals` compiled the delivered file
as both sandbox and library module, cleanly (2.5 s and 1.9 s). No diagnostic
commands remain. Every binder is explicit and every Lean line is at most
100 characters. Only the item's `lean` field changes. No statement is disputed.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
