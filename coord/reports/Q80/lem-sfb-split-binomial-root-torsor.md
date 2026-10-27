## Worker report

The module `Sheaf.FieldTheory.SplitBinomialRootTorsor` states
`Polynomial.split_binomial_root_torsor`. Its single theorem has proof `sorry`;
there are no definitions, helper theorems, new nodes, or dependency repairs.
The node is unchanged except for its `lean` record.

The source was read at `literature/stacks-project/fields.tex`,
`section-Kummer`, opening paragraph (Tag 09I6). The node extracts the elementary
root-scaling input, rather than asserting the later irreducible Kummer equivalence.
Its five proof steps are reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- The field F is `(F : Type u) [Field F]`.
- The positive integer n is `(n : ℕ) [NeZero n]`. For natural numbers this is
  exactly n ≥ 1, not a restriction to n ≥ 2.
- Invertibility of n in F is `(hn : IsUnit (n : F))`.
- Splitting over F is `(hsplit : (X ^ n - 1 : F[X]).Splits)`.
- The fixed algebraic closure is `(Ω : Type v) [Field Ω] [Algebra F Ω]
  [IsAlgClosure F Ω]`. The two universes are independently bound; no choice of a
  particular closure or equality of universes is imposed. All inclusions of F
  into Ω are the recorded `algebraMap F Ω`.
- The group μ_n(F) is exactly Mathlib's `rootsOfUnity n F`, the subgroup of Fˣ
  cut out by ζ^n = 1 with inherited multiplication. Its `Finite` instance is
  already supplied by Mathlib for nonzero n over a domain. Its cardinality is
  the conclusion `Nat.card (rootsOfUnity n F) = n`. Thus finiteness is available
  as a structure instance, and the theorem asserts the required exact count.
- Every nonzero a is quantified as `∀ a : Fˣ`. Monicity and separability are the
  two conclusions `(X ^ n - C (a : F)).Monic` and
  `(X ^ n - C (a : F)).Separable`, over F itself.
- A chosen root α in Ω and its root equation are `∀ α : Ω,
  α ^ n = algebraMap F Ω (a : F) → ...`.
- Its nonvanishing is the conclusion `α ≠ 0`.
- The claimed bijection is an existential equivalence
  `e : rootsOfUnity n F ≃ {β : Ω // β ^ n = algebraMap F Ω (a : F)}`.
  Its value is fixed for EVERY ζ by
  `(e ζ : Ω) = α * algebraMap F Ω ((ζ : Fˣ) : F)`.
  This states the actual scalar map, rather than an unspecified bijection.
- The factorization is an equality in Ω[X] between
  `X ^ n - C (algebraMap F Ω (a : F))` and the finite product of
  `X - C (α * algebraMap F Ω ((ζ : Fˣ) : F))` over ALL ζ in μ_n(F).
  `@Finset.univ (rootsOfUnity n F) (Fintype.ofFinite _)` makes the finite
  enumeration explicit without adding an enumeration or finiteness hypothesis.
- The final conjunct explicitly records the special case a = 1, α = 1:
  `(X ^ n - 1 : Ω[X])` equals the product of
  `X - C (algebraMap F Ω ((ζ : Fˣ) : F))` over that same full finite group.
- There is no irreducibility hypothesis.

Dependency interfaces read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (reexported through the
  public imports). Read its full class declaration and documentation.
- `def-weil-algebraic-closure`: the recorded Mathlib match explicitly includes
  `IsAlgClosure F Ω`, Mathlib.FieldTheory.IsAlgClosed.Basic. Read the full
  `IsAlgClosed` and `IsAlgClosure` class declarations and documentation.
- `def-weil-polynomial-ring`: `Polynomial`, Mathlib.Algebra.Polynomial.Basic,
  reexported by the public imports. Read its full structure and documentation.
- `def-pc-separable-polynomial`: `Polynomial.Separable`,
  Mathlib.FieldTheory.Separable, literally coprimality with the formal derivative.
- Proof dependency `lem-pc-separable-polynomial-distinct-roots-alg-closed`:
  the recorded `Polynomial.card_rootSet_eq_natDegree` is in the publicly imported
  Mathlib.FieldTheory.Separable; its companion clauses use
  `Polynomial.nodup_roots` in that module and
  `Polynomial.Splits.eq_prod_roots_of_monic` in Mathlib.Algebra.Polynomial.Splits
  (reexported by it), with `IsAlgClosed.splits` from the other public import.
  The signatures and the factorization statement were read. No dependency module
  needs to be supplied or repaired.
- Existing notion used directly: `rootsOfUnity`,
  Mathlib.RingTheory.RootsOfUnity.Basic. Read its subgroup definition, membership
  formulas, `rootsOfUnityEquivNthRoots`, and its `Finite` instance.

Edge cases checked before writing: n = 1 gives the trivial root group, one root a,
and the single linear factor; a = 1 and α = 1 give the explicitly recorded final
conjunct. If a is already an nth power, reducibility causes no problem: α remains
nonzero and division by α gives the inverse root parametrization. In positive
characteristic, only characteristic dividing n is excluded, exactly by `hn`;
no characteristic-zero assumption is added. The excluded a = 0 and n = 0 are
excluded by precisely the hypotheses in the node. F need not be algebraically
closed; splitting of X^n - 1 is the base-root descent assumption. Arbitrary
algebraic closures and independent field universes are retained.
No statement dispute or correction was found.

Existing-declaration searches (2026-10-24, using msearch.py):

- LeanFinder: “Over a field with n invertible and X^n-1 split, multiplication by a
  root alpha bijects the nth roots of unity with roots of X^n-a and gives the
  product factorization”. Eight hits: Kummer automorphism equivalences requiring
  irreducibility, `X_pow_sub_C_eq_prod`, and `IsPrimitiveRoot.nthRoots_eq`.
  None gives the full statement with the base root group and no primitive-root
  choice or irreducibility hypothesis.
- Loogle: `Polynomial.Separable, Polynomial.X`. Twelve hits, including
  `Polynomial.separable_X_pow_sub_C_unit`, `Polynomial.separable_X_pow_sub_C`,
  and separability of products. These give individual clauses, not the combined
  root-torsor and factorization conclusion.
- Mathlib grep: `rootsOfUnityEquivNthRoots|X_pow_sub_C_eq_prod|
  separable_X_pow_sub_C|card_rootsOfUnity`. Twenty-five hits, including the
  preceding factorization and separability lemmas, cardinality lemmas, and the
  existing root-group notion. None states the whole item.
- LeanSearch: “The roots of a separable split binomial are scalar multiples of
  one root by all nth roots of unity”. Eight hits, including
  `Polynomial.card_rootSet_eq_natDegree`, `Polynomial.Splits.scaleRoots`, and
  `X_pow_sub_C_splits_of_isPrimitiveRoot`. No exact combined statement.
- Direct rg of lean/WeilConjectures and lean/Sheaf for `rootsOfUnity`,
  `split_binomial`, `binomial.*torsor`, and the node id found root-group usages
  but no root-torsor statement or existing module for this item. A final exact
  declaration-name search in Mathlib and both project roots found no collision.
  The prescribed semantic-search transcripts are in the sandbox searches.jsonl.

Validation: the prescribed scompile.py compiled this file in both sandbox and
library module positions, against the live server build, with exit status zero
and no errors or unexpected warnings (1.5 s and 1.7 s reported). The module
sets `autoImplicit false`; every variable and universe is explicitly bound.

## Second reading by Q80

A second pass by the same worker reread the node and the finished module; no
separate agent was started because the dispatcher's explicit instruction forbids
it. The maintainer performs the independent review. The pass checked the
conjunction grouping: the root equation guards nonvanishing, the equivalence
with its pointwise formula, and the general product; monicity and separability
are asserted for every unit before any root is chosen; the special a = 1 product
is outside the universal a/α clause. It checked that `NeZero n` is equivalent
to n ≥ 1 and that `IsUnit (n : F)` is the node's invertibility assumption, that
all coefficients cross into Ω through the algebra structure, and that the
product ranges over the entire subgroup using its existing finiteness instance.
All four statement dependencies and the proof-dependency leaf are supplied by
the public Mathlib imports. No clause, hypothesis, or object mismatch was found;
no change was required after this rereading.
