## Worker report

The module `Sheaf.RingTheory.DividedPowersGeneratorCriterion` states
`DividedPowers.generator_criterion`, with its sole proof `sorry`. Source read:
`literature/stacks-project/dpa.tex`, Tag 07GP (`lemma-check-on-generators`),
statement and proof, together with Tag 07GL (`definition-divided-powers`).
No mathematical node fields change; the item gains only its `lean` record.

Hypothesis-by-hypothesis correspondence:

- A commutative ring C is `{C : Type u} [CommRing C]`, with arbitrary explicit `u`.
- Its ideal J is `(J : Ideal C)`.
- A subset S of J is `(S : Set J)`. The subtype expresses S ⊆ J without adding a
  separate membership assumption; `hS : Ideal.span (Subtype.val '' S) = J`
  expresses generation as an ideal, not generation of the underlying abelian group.
- The given positive operations J → J are represented by `δ : ℕ → J → C`
  and `hmem : ∀ n, 0 < n → ∀ z : J, δ n z ∈ J`. This is exactly their
  specified codomain. Degree zero is the ambient-ring-valued operation fixed by
  `hzero : ∀ z : J, δ 0 z = 1`. In particular the zeroth value need not lie in J.
- The identity axiom is `hone : ∀ z : J, δ 1 z = (z : C)`.
- The scalar axiom is `hscalar`, with positive n, arbitrary c : C and z : J;
  the ideal scalar action `c • z` represents multiplication cz.
- The addition axiom is `hadd`, for arbitrary z,w : J and positive n. The finite
  sum over `Finset.range (n + 1)` includes both endpoints and is precisely
  Σ(i=0,…,n) δ_i(z) δ_(n-i)(w).
- The multiplication identity on each generator is `hmul`, quantified over
  `s ∈ S` and arbitrary positive n,m. Its coefficient is `Nat.choose (n + m) n`
  cast to C.
- The iteration identity on each generator is `hcomp`. The inner value is the
  ideal element `⟨δ m s, hmem m hm s⟩`, so no unrelated operation or lift is used.
  The coefficient `(n*m).factorial / (n.factorial * m.factorial ^ n)` is natural
  number division, cast to C; it is not division in C.

Clause-by-clause conclusion:

- The first conjunct is the same multiplication equality for every `z : J`
  and all positive n,m.
- The second conjunct is the same iteration equality for every `z : J`
  and all positive n,m, with the same ideal-valued inner operation.
- The third conjunct `∃ γ : DividedPowers J, ∀ n z, γ.dpow n z = δ n z`
  says these very maps, in every degree, form the ordinary divided-power structure.
  It does not merely assert existence of an unrelated divided-power structure.
  `DividedPowers` automatically extends all operations by zero off J, as the
  definition node permits; the input is stated directly on J, so it carries no
  off-ideal conditions.
- Integrality is expressed by the natural-number coefficient. Mathlib's
  `Nat.uniformBell_eq_div` in `Combinatorics/Enumerative/Bell.lean` (lines 191ff)
  identifies the coefficient in the `DividedPowers.dpow_comp` axiom with this exact
  quotient when m > 0, after commuting the two denominator factors. Thus its
  use agrees with the recorded definition's `uniformBell` coefficient in every
  characteristic.

Dependency declarations used: `def-sfb-ordinary-divided-power-structure` has
status `mathlib`, with its `mathlib_match` naming `DividedPowers` in
`Mathlib.RingTheory.DividedPowers.Basic`. I read the module documentation and
full structure signature (lines 78–92), including `dpow_null`, `dpow_zero`,
`dpow_one`, `dpow_mem`, `dpow_add`, `dpow_mul`, `mul_dpow`, and `dpow_comp`.
The module publicly imports that declaration. The proof dependency
`lem-sfb-pd-check-generators` currently has neither `lean` nor `mathlib_match`;
it is named in the natural-language proof plan and has no module to import.
It is not a statement dependency or a missing notion. Its accepted stage-1
statement is the same generator criterion (without separately spelling out the
consequent identities). It does not depend back on this item. A future statement
of that proof dependency can be attached here by the maintainer under the shared
proof-import rule; this delivery does not create a second definition.

Edge cases checked against the source and the Lean signature:

- Empty S is admitted: no Nonempty or finite-set hypothesis occurs. The span
  equality then makes J the zero ideal. Applying homogeneity at c=0 gives the
  positive operations at zero equal to zero, so the conclusion is consistent.
- Infinite S is admitted, since S is a `Set J` and ideal span uses finite linear
  expressions without assuming the whole generating set finite.
- The zero ring, the zero ideal, and the unit ideal are not excluded by binders.
  The latter can only carry inputs satisfying the displayed axioms; no further
  restriction is imposed by the theorem.
- n=1 or m=1 is included in both generator and global identities. Degree zero
  is present in the addition endpoints and in agreement with the resulting γ;
  the two requested identities have the positive index restrictions of the node.
- Rings of positive characteristic are included. Both coefficients are natural
  number casts, and no torsion-free, field, characteristic, or invertibility
  assumption is introduced. The denominator factorials are positive integers.

Searches actually run, all on 2026-10-24:

1. `msearch.py ... leanfinder` with query
   "Maps on an ideal satisfying addition and scalar homogeneity give divided
   powers if multiplication and iteration hold on ideal generators": 8 hits,
   including `DividedPowers`, `SubDPIdeal`, `IsSubDPIdeal`,
   `DPMorphism.fromGens`, `dpow_eq_from_gens`, and `dpow_comp_from_gens`.
2. `msearch.py ... loogle` with query `DividedPowers, "gens"`: 4 hits,
   `dpow_eq_from_gens`, `DPMorphism.fromGens`, its coercion lemma, and
   `dpow_comp_from_gens`.
3. `msearch.py ... grep` with regex `generat|from_gens|fromGens` in
   `RingTheory/DividedPowers`: 10 hits, all concerning sub-PD-ideals or morphisms
   between existing full divided-power structures.
4. Direct `rg` in Mathlib `RingTheory/DividedPowers` for generators/fromGens;
   I opened the full signatures and docstrings in `DPMorphism.lean` at 164ff
   and 237–250. These require existing full structures and do not state this
   criterion from partial axioms. `DividedPowers.mk` requires all axioms globally.
5. Direct `rg` in both project `lean/WeilConjectures` and `lean/Sheaf` for the
   item ID, the duplicate ID, 07GP, and divided-power/generator patterns, plus
   `dag/lean_names_upstream.json`: no recorded theorem for this criterion.
   Hits in `DividedPowersFlatExtension` and `DividedPowersGlueIdeals` are
   natural-language proof references only. `ColourProfileCoefficients` is an
   arithmetic supporting statement, not the criterion.

No statement correction, new node, dependency repair, or disputed statement.

## Second reading by Q42

Author's second pass, not an independent-agent review: the dispatcher brief
forbids starting other agents and assigns independent review to the maintainer.
I compared the node and Tag 07GP with the final signature again. Each of the
three global axioms and both generator axioms has precisely the specified
quantifiers. S is a subset of the ideal via its subtype, and generation is ideal
span. Membership of positive values and the zeroth convention encode the given
maps without a stronger algebraic assumption. The conclusion gives both global
identities and agreement of all supplied maps with an actual `DividedPowers J`.
The coefficient quotient is taken in ℕ and agrees with Mathlib's `uniformBell`.
No mismatch requiring a node correction was found. The sole theorem proof is
`sorry`; all variables and universes are explicit, with `autoImplicit false`.
