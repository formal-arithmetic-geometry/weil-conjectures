## Worker report

Stage 2: the new module `Sheaf.RingTheory.DividedPowersFactorialCriterion` states
`DividedPowers.exists_unique_of_factorial_divisibility_on_generators` with one whole-proof
`sorry`. It defines no new notion and proves nothing. The accepted stage-1 split and all node
fields except `lean` are preserved. The inherited stage-1 BLOCKED message is resolved by the
stage-handoff paragraph in coord/brief-stage2.md §0: an accepted split is the input to this
stage, not a prohibition against writing its Lean statement. No repair note exists for this item.

Source read: literature/stacks-project/dpa.tex, definition-divided-powers (Tag 07GL),
lemma-silly (Tag 07GM), all four parts and the full proof. The item is the forward generator
criterion of (4), together with the conclusions of (1)-(3); the source and node agree.

Hypotheses and clauses, matched individually:

- The commutative ring A is `(A : Type u) [CommRing A]`. There is no nontriviality or
  characteristic-zero assumption excluding the zero ring.
- Additive torsion-freeness is `hT : ∀ (m : ℕ) (a : A), 0 < m → m • a = 0 → a = 0`.
  Positive natural integers are precisely the positive integer multipliers of the node.
- The ideal, family index, and generators are `(J : Ideal A) (S : Type v) (u : S → A)`.
  The unrelated index universe v permits every family size.
- Generation is `hgen : Ideal.span (Set.range u) = J`; in particular every `u s` lies in J.
- For each generator and each n ≥ 1, factorial divisibility with quotient in J is
  `hdiv : ∀ (s : S) (n : ℕ), 1 ≤ n → ∃ w ∈ J, u s ^ n = (n.factorial : A) * w`.
  The quotients are existential, as in the node, so no additional chosen family is assumed.
- Existence of an ordinary structure is `∃ θ : DividedPowers J`. Its membership, zeroth,
  first, scalar, addition, product and iteration axioms are exactly the recorded Mathlib
  dependency. Operations off J are canonically zero, as expressly allowed in that node.
- Uniqueness of the structure is `∀ η : DividedPowers J, η = θ`, with no additional
  condition imposed on the competing structure.
- For every x in J and every n ≥ 1, `(n.factorial : A) * θ.dpow n x = x ^ n` is the
  required equation. The positive value belongs to J by the structure's `dpow_mem` field.
- Uniqueness of its quotient in J is
  `∀ (y : A), y ∈ J → (n.factorial : A) * y = x ^ n → y = θ.dpow n x`.
- The final conjunct quantifies over every s, positive n, and w in J satisfying the
  generator equation and gives `θ.dpow n (u s) = w`. This is precisely the node's
  `θ_n(u_s) = v_(n,s)`, without choosing the existential witnesses outside the statement.

Dependency declarations read and used:

- Statement dependency def-sfb-ordinary-divided-power-structure is the Mathlib leaf
  `DividedPowers`, Mathlib.RingTheory.DividedPowers.Basic (full structure and docstring read).
  The node's mathlib_match is usable; it has no lean record and needs no repair.
- Proof dependency lem-pur-commutative-ring-binomial-expansion is `add_pow`, imported
  privately from Mathlib.Data.Nat.Choose.Sum.
- Proof dependency lem-weil-pbc-algebra-tensor-pushout-universal-property is the Mathlib
  tensor ring/maps API: Algebra.TensorProduct.instCommRing, tmul_mul_tmul, includeLeft,
  includeRight, productMap, productMap_apply_tmul, ext. Private import
  Mathlib.RingTheory.TensorProduct.Maps exposes the recorded Basic/Maps declarations.
- Proof dependency lem-trf-torsionfree-rationalization-injective is
  `AddCommGroup.rationalizationMap_injective` in
  Sheaf.GroupTheory.TorsionfreeRationalizationInjective. Its full statement, proof docstring,
  and actual proof were read. It takes positive integer torsion-freeness and uses ℚ ⊗[ℤ] A;
  tensor symmetry relates it to the node's A ⊗[ℤ] ℚ. The mathematical torsion condition
  is equivalent to the natural-multiplier hypothesis of this item.
- Proof dependency lem-sfb-rational-ideal-divided-powers is the Mathlib leaf
  `DividedPowers.RatAlgebra.dividedPowers`, with dpow_apply, from
  Mathlib.RingTheory.DividedPowers.RatAlgebra. Its full construction and signatures were read.
  This is a proof-only private import; a rational-algebra hypothesis is not imposed on A.

Edge cases checked against the source and Mathlib encoding:

- Empty S: generation forces J = ⊥. The hdiv hypothesis is vacuous, and the zero ideal
  has its unique structure. No Nonempty S or nonzero ideal is assumed.
- Zero ring: hT holds and the unique ideal/structure has all values zero; one also equals
  zero, so the zeroth axiom is consistent. No IsDomain or CharZero binder was introduced.
- n = 1: the equation is 1*w = x and the first operation is x. No extra divisibility is needed.
- n = 0: excluded only from the positive-quotient conclusion and the divisibility hypothesis,
  exactly as in the node. The zeroth operation on J is already one in DividedPowers.
- x = 0 and zero generators: torsion-freeness gives zero as the unique positive quotient.
- Arbitrary S, including infinite families and distinct universe levels, is allowed by span.
- Nonzero positive characteristic rings fail hT, as intended, rather than being discarded by
  a separate hypothesis. The zero ring remains included.

Searches made (2026-10-24):

- msearch.py leanfinder: "An ideal in a torsion free commutative ring has unique divided
  powers if powers of all generators are divisible by factorials in the ideal". Eight hits:
  RatAlgebra.dividedPowers_unique requires a rational algebra; dpow_eq_from_gens and ext
  compare pre-existing structures; OfInvertibleFactorial.dividedPowers requires invertible
  factorials and nilpotence; DividedPowers is the definition. No matching existence criterion.
- msearch.py loogle: `"DividedPowers", "factorial"`. Twelve hits, notably
  factorial_mul_dpow_eq_pow (presupposes a structure), and OfInvertibleFactorial declarations
  (invertibility/nilpotence). None has the torsion-free generator criterion.
- msearch.py grep: `torsion|factorial|ofInjective`, RingTheory/DividedPowers: fifteen hits.
  Read Basic, RatAlgebra and ofInjective's context. Existing constructions need a rational
  algebra, invertible factorials/nilpotence, or an ambient structure and lifting witnesses
  on every ideal element; none is this statement.
- rg over lean/WeilConjectures and lean/Sheaf for DividedPowers and torsionfree_factorial:
  only GradedDividedPowers imports/extends the ordinary structure. No duplicate theorem.
  Search for the item ID in lean/WeilConjectures has no hits.
- rg over dag/lean_names_upstream.json, the divided-power Mathlib directory, lean/Sheaf,
  and lean/WeilConjectures for torsionfree_factorial, existsUnique_of_factorial,
  exists_of_factorial, and factorial.*generat: no hits.

No statement correction, new node, dependency module, or mathematical dispute is needed.

## Second reading by Q75

Author's final self-check, not an independent reading: reopened the node, its Mathlib
DividedPowers dependency, Tag 07GM and the delivered signature. The torsion condition,
span equality, per-generator existential divisibility, unrestricted uniqueness of the whole
structure, quotient equation, quotient uniqueness, and generator-value consequence each
match the clauses listed above. Checked that quotient membership follows from dpow_mem,
that competing structures have no extra hypothesis, and that positive degrees alone occur
in the quotient claims. No mismatch was found and no accepted split field was changed.
The maintainer's independent review is the separate review required by the dispatch brief.

## Validation

scompile.py compiled the sandbox and library module cleanly (5.2 s and 4.6 s).
The prescribed deliver2.py --no-push completed successfully: preflight and per-file
compilation passed; dry-run commit cc4422a095f. No changes were required after validation.
