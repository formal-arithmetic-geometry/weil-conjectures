## Worker report

The module `Sheaf.GroupTheory.FiniteAbelianCharacterPrimeBound` states
`CommGroup.finite_monoidHom_units_and_card_le_ordCompl`, with its only proof `sorry`.
It introduces no definition. The existing node's statement and dependency lists are unchanged.

Hypothesis-by-hypothesis and clause-by-clause comparison:

| Node text | Lean rendering |
| --- | --- |
| A finite abelian group, multiplicative | `(A : Type u) [CommGroup A] [Finite A]` |
| Its order n ≥ 1 | `Nat.card A`; a group is inhabited by its identity, so its finite cardinal is positive. The name n is substituted by its defining expression throughout. |
| k is a field | `(k : Type v) [Field k]`, the recorded Mathlib match of `def-weil-field` |
| p = char(k) | `ringChar k`, the unique characteristic of the field |
| n' is the largest divisor of n prime to positive p | `ordCompl[ringChar k] (Nat.card A)`, Mathlib's existing complementary prime-power part |
| If p = 0, n' = n | The same expression is n: factorization at the nonprime 0 is zero, and `0 ^ 0 = 1`. |
| X = Hom(A,k×) | `A →* kˣ`; a monoid homomorphism between groups is a group homomorphism |
| Pointwise multiplication on X | The existing `MonoidHom.instCommGroup` on this exact type; its multiplication is pointwise. No new character type is introduced. |
| X is finite | First conjunct `Finite (A →* kˣ)` |
| Its order is at most n' | Second conjunct `Nat.card (A →* kˣ) ≤ ordCompl[ringChar k] (Nat.card A)` |
| No primitive-roots assumption | The complete binders contain only the finite commutative group and arbitrary field; no `HasEnoughRootsOfUnity` or field finiteness instance occurs. |

The universes `u` and `v` are explicitly declared and independent. All term variables are explicitly
bound. The header uses module mode and exposes the statement dependencies publicly.

Dependency declarations read and used:

- Statement dependency `def-weil-field`: `Field`, in `Mathlib.Algebra.Field.Defs`. Its extension of
  `CommRing` and `DivisionRing` supplies nontriviality and inverses for nonzero elements, exactly
  the node's field notion. This Mathlib leaf has no `lean` record and needs none.
- Proof dependency `lem-trf-finite-abelian-cyclic-product`:
  `CommGroup.equiv_prod_multiplicative_zmod_of_finite`, in
  `Mathlib.GroupTheory.FiniteAbelian.Basic`; read the full statement and structure-theorem docstring.
  It gives a finite index type, orders greater than one, and the multiplicative equivalence.
- Proof dependency `lem-trf-roots-of-unity-remove-characteristic-power`:
  `mem_rootsOfUnity_prime_pow_mul_iff`, in `Mathlib.RingTheory.RootsOfUnity.Basic`.
  Its full signature assumes a reduced commutative ring with `ExpChar`; the node's field is the
  stated specialization. Its primed power variant was read too.
- Proof dependency `lem-exc-field-roots-cyclic-bound`: the finite instance,
  `rootsOfUnity.isCyclic`, and `card_rootsOfUnity`, in
  `Mathlib.RingTheory.RootsOfUnity.Basic`. Read their signatures in the `IsDomain` section;
  nonzero order provides their `NeZero` parameter. The same module supplies the existing instance
  `Finite (A →* kˣ)`. It is imported as a proof dependency, not as a new assumption.

The theorem docstring records all four proof steps of the DAG, including the empty-product case.
The two proof modules are plain imports. Other public imports provide `ringChar`, `ordCompl`,
`Nat.card`, and the existing pointwise group on homomorphisms.

Encoding check for n': `Mathlib.Data.Nat.Factorization.Defs` defines `ordCompl[p] n` as
`n / p ^ n.factorization p`. Read its documentation, and in `Factorization.Basic` read
`ordCompl_of_not_prime`, `ordCompl_dvd`, `coprime_ordCompl`, and
`dvd_ordCompl_of_dvd_not_dvd`. They verify both the characteristic-zero convention and the
largest-coprime-divisor characterization for nonzero n and prime p. No new definition node is needed.

Edge cases checked mathematically before writing:

- The trivial group has n = n' = 1 and precisely one character. No nontriviality assumption on A
  occurs; its cyclic decomposition may use the empty index type.
- A p-group in characteristic p has n' = 1 and only the trivial character, since roots of unity
  of p-power order in a field of characteristic p are trivial.
- For A = Z/6 and k = F3, there are two characters and n' = 2.
- For A = Z/3 and k = Q, there is one character and n' = 3. Thus absent primitive roots do not
  cause an equality claim or an excluded case.
- For A = (Z/2)^2 and k = Q, four sign characters attain the bound four.
- Characteristic zero and infinite fields are included; the order-zero case for A cannot occur
  because a group contains its identity. No field with 0 = 1 is included by `Field`.

Searches made using `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- `leanfinder`: "The number of homomorphisms from a finite abelian group to the units of an
  arbitrary field is bounded by the prime to characteristic part of the group order".
  Returned `AddChar.card_addChar_le`, `MulChar.finite`, and duality results requiring enough roots.
  The additive bound assumes `RCLike`; none states this arbitrary-field prime-part bound.
- `loogle`: `MonoidHom, Nat.card`. Twelve hits, including subgroup image/range cardinality facts;
  none gives the item.
- `leansearch`: "Finite abelian group homomorphisms to field units cardinality bounded by prime
  to characteristic part". Eight hits include `MulChar.finite`, cyclic power-map counts, and
  enough-roots duality; none matches the statement.
- `grep`: `card_monoidHom|finite.*[Mm]onoidHom|ordCompl`, in `GroupTheory/FiniteAbelian`.
  It found `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`; read its full signature and
  surrounding binders in `Duality.lean`. The extra enough-roots hypothesis rules out an exact match.
- Direct `rg` in Mathlib found `ordCompl` and its arithmetic characterization; read the notation
  in `Factorization.Defs` and the relevant lemmas in `Factorization.Basic`.
- Direct `rg` for finite abelian characters, character prime parts, and homomorphism cardinality
  in `lean/WeilConjectures` and `lean/Sheaf` found unrelated Kummer, cyclotomic-character, and
  fundamental-group results. `grep -rn` for the item id in `lean/WeilConjectures` found no match.
  A final direct `rg` over both project trees and Mathlib found no declaration of the proposed name
  or an existing homomorphism-cardinality bound using `ordCompl`.

No statement fault, missing dependency interface, new node, or disputed assertion was found.
The Gabber--Ramero archival copy remains WANTED as the base node says. The proof is already marked
agent-written in the node; local Stacks `fields.tex`, section `section-roots-of-1` (Tag 09HW),
was read and gives the root-counting argument actually used.

## Second reading by NS

The dispatcher explicitly requires a single worker and prohibits starting another agent. This is a
separate line-by-line rereading by that worker; independent review is left to the maintainer, as the
assignment specifies. I reopened the node and module and checked the comparison table above against
the complete theorem signature. The two conjuncts retain finiteness and the inequality, the finite
commutative group permits the trivial group, and the field binder has no roots-of-unity hypothesis.
Replacing the names n, p, n' and X by their defining expressions changes no hypothesis or clause.
The standard `ordCompl` handles both characteristics, and no new data or axiom was introduced.
No mismatch or further change was needed during this rereading.
