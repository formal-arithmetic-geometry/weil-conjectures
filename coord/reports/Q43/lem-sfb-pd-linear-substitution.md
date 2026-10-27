## Worker report

The module `Sheaf.RingTheory.DividedPowerLinearSubstitution` states
`DividedPowers.dpow_multinomial_linear_substitution`, with `sorry` as its only proof.
It introduces no definitions and changes only the item's `lean` record.
Source read: `literature/stacks-project/dpa.tex`, definition-divided-powers
(Tag 07GL), and lemma-gamma-extends (Tag 07H1), especially the matrix-substitution
paragraph before the common-refinement argument. Although the surrounding
existence proof assumes flatness, the matrix identity itself uses only the
source divided-power axioms, as the node's finite-convolution proof explains.

Hypothesis and clause correspondence:

- Commutative rings A and B: `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`.
  Universes are independent and explicitly declared; neither ring is required
  to be nontrivial.
- Unital map f: `(f : A →+* B)`. No algebra structure, flatness, injectivity,
  surjectivity, or target divided-power structure is assumed.
- Ideal I with its ordinary divided powers: `(I : Ideal A) (γ : DividedPowers I)`.
  This is exactly the Mathlib match recorded by
  `def-sfb-ordinary-divided-power-structure`, including the total extension
  outside the ideal and `γ.dpow 0 z = 1` for z in the ideal.
- Finite tuple x in I: `(r s : ℕ) (x : Fin r → A)` with
  `(hx : ∀ i : Fin r, x i ∈ I)`. Using ambient elements with a membership
  hypothesis supplies exactly the same data as a tuple in the ideal.
- Arbitrary matrix entries and coefficients: `(a : Fin r → Fin s → A)` and
  `(c : Fin s → B)`. The coefficient tuple b of the displayed identity is
  replaced directly by `∑ j : Fin s, f (a i j) * c j`.
- The tuple y is replaced directly by `∑ i : Fin r, a i j * x i`. Every entry
  lies in I by closure under A-multiplication and finite sums; no additional
  membership hypothesis is imposed.
- Degree n ≥ 0: `(n : ℕ)`, with no positivity restriction.
- P_n's indexing condition `∑ i, e_i = n` is rendered by
  `e ∈ (Finset.univ : Finset (Fin r)).sym n`. An element of this finset is an
  unordered tuple/multiset of exactly n indices. Its exponent at i is
  `Multiset.count i e`. Counting multiplicities is a bijection with natural
  exponent tuples of total degree n. Each exponent tuple is counted once,
  with no multinomial coefficient. The right side uses the same convention
  for `Fin s`. This is also Mathlib's convention in `DividedPowers.dpow_sum`.
- Each product factor is exactly `b i ^ e_i * f (γ.dpow e_i (x i))` on the
  left and `c j ^ d_j * f (γ.dpow d_j (y j))` on the right. Consequently the
  asserted equality is exactly P_n(x;b) = P_n(y;c); the local P notation is
  expanded directly and is not replaced by a new object.

Dependency declarations read and used:

- Statement dependency `def-sfb-ordinary-divided-power-structure` has no `lean`
  record because it is a Mathlib leaf. Its `mathlib_match` is `DividedPowers`
  in `Mathlib.RingTheory.DividedPowers.Basic`. Read the full structure,
  fields, and module documentation; imported publicly and used directly.
- Proof dependency `lem-pur-commutative-ring-binomial-expansion` has Mathlib
  match `add_pow` in `Mathlib.Data.Nat.Choose.Sum`. Read its full signature
  and binomial-theorem docstring; imported as a proof dependency without
  `public`. Its use in the future proof is described in step 3 of the
  theorem's docstring.

Edge cases checked before writing:

- n = 0: `Finset.sym_zero` gives one empty multiset; all counts are zero,
  every divided-power factor on an ideal element is one, so both sides are
  one, including empty index sets.
- r = 0 and n > 0: `Finset.sym_empty` makes the left sum zero. Every y_j is
  zero, and some exponent is positive in every right-side term, so that
  term vanishes by the divided-power scalar-zero axiom.
- s = 0 and n > 0: the right sum is zero; every b_i is zero, and every
  left-side term has a positive exponent, hence vanishes. The simultaneous
  empty case also has empty positive-degree sums on both sides.
- n = 1 reduces to the same double sum after applying the ring-map laws.
- Zero coefficients, x_i = 0, and I = 0 obey the same zero-factor argument;
  0^0 = 1 retains the degree-zero and zero-exponent factors correctly.
- Zero rings and rings in arbitrary characteristic are allowed; no division
  by factorials or characteristic assumption appears.

Searches made using the prescribed `msearch.py Q43 lem-sfb-pd-linear-substitution`:

- LeanFinder: "Divided power multinomial sums are invariant under linear
  substitution through a ring homomorphism without divided powers on the
  target ring". Eight hits, including `DividedPowers.dpow_sum'`, `prod_dpow`,
  `dpow_sum`, `dpow_comp_from_gens`, and `IsDPMorphism.map_dpow`. None states
  the arbitrary-target matrix identity: the sum lemmas evaluate source
  divided powers, and morphism lemmas require a target divided-power ideal.
- Loogle: `DividedPowers.dpow_linearCombination`. One hit. Read its full
  signature in Basic.lean: it requires `hJ : DividedPowers J` in the target
  algebra S, so it cannot represent this statement.
- Mathlib grep: `dpow_sum|dpow_linearCombination|prod_dpow|linear.*substit`
  in `RingTheory/DividedPowers`. Five hits in Basic.lean, including
  supporting multinomial expansions; no matrix-substitution theorem.
- LeanSearch: "Divided power multinomial expressions under matrix
  substitution and arbitrary target ring homomorphism". Eight hits,
  including `MvPolynomial.bind₁`, `DividedPowers.prod_dpow`, `dpow_sum'`, and
  power-series substitution lemmas; none is this statement.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf`:
  `linearSubstitution|linear_substitution|pd-linear-substitution|dpow_linearCombination|multinomial`.
  Only supporting docstrings and unrelated multinomial comments appeared;
  notably DividedPowersFlatExtension references this node as an input but
  does not state its identity. No existing matching declaration.
- Direct rg for `dpow_multinomial_linear_substitution|multinomial_linear_substitution`
  in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf:
  no hits; the declaration name is unused.
- Read `Finset.sym`, `mem_sym_iff`, `sym_zero`, `sym_empty`, and `sym_univ`
  in Mathlib/Data/Finset/Sym.lean to check the finite indexing and empty cases.

No statement correction, missing dependency, new node, or statement dispute.
The source identity and the node agree. The theorem docstring contains the
complete five-step finite-convolution proof from the node, with the endpoint
and empty-product cases included.

Validation: prescribed `scompile.py` compiled both sandbox and final library
module paths successfully (6.1 s and 10.8 s); no errors or warnings printed.

## Second reading by Q43

I reread the node and the completed module side by side after the first compile.
This is a second pass by the assigned worker, not an independent worker review:
the dispatcher brief explicitly prohibits starting another agent; the maintainer
performs the independent review of this delivery.

The ring, unital map, ideal, divided-power structure and ideal-membership
hypotheses match literally through the binders above. The tuple lengths are
unrestricted naturals; Fin 0 is permitted. The substitutions for b and y use
the same matrix orientation a i j as the node. On the right the sum is over
i for fixed j, while the outer product is over j, as required. Both sides
apply f to the source divided power after forming its source argument; the
target has no divided-power structure. The multiset multiplicity encoding
counts every exponent tuple once and introduces no factorial coefficient.
Degree zero uses membership of x and of the source column sums, so the
Mathlib extension-by-zero convention off the ideal changes nothing. The
empty index, zero ideal, and zero coefficient cases remain included. The
only postponed theorem is the item's theorem, and its proof is exactly
`sorry`. No mismatch was found and no statement change was needed.
