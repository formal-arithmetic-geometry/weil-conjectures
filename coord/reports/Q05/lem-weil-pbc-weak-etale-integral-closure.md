## Worker report

The node is already stated by the source-library theorem
`Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct` in
`WeilConjectures.RingTheory.ProEtale.WeakDimension`; no new module is needed.  The
node's `lean` record therefore uses `existing: true` and records that declaration.
The theorem has no `sorry` and its source docstring identifies Stacks Tag 092W.

The declaration signature is:

```lean
theorem Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct
    (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] [Field L] [Algebra A L] [FaithfulSMul A L]
    [Algebra.IsAlgebraic A L] [IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn B (B ⊗[A] L) :=
```

The correspondence with the node is clause by clause.  `A : Type*`,
`[CommRing A]`, and `[IsDomain A]` render the commutative integral domain A.
`L : Type*`, `[Field L]`, and `[Algebra A L]` render the fraction-field
realization K and its A-algebra structure.  For a fraction field of a domain,
`Algebra.IsAlgebraic A L` is the standard fact that every fraction satisfies a
linear polynomial over A; the node's “A integrally closed” hypothesis is rendered
by `[IsIntegrallyClosedIn A L]`.  `B : Type*`, `[CommRing B]`, and `[Algebra A B]`
render the A-algebra B, while `[Algebra.WeaklyEtale A B]` is exactly the weakly
étale hypothesis from `def-weil-pbc-ind-etale-algebra`.  Finally,
`IsIntegrallyClosedIn B (B ⊗[A] L)` is precisely the conclusion that B is
integrally closed in the tensor product.

The dependency declaration used is the recorded source declaration
`Algebra.WeaklyEtale` from `WeilConjectures.RingTheory.ProEtale.WeaklyEtale`,
which is the weakly-etale algebra notion supplied by
`def-weil-pbc-ind-etale-algebra`.  The source theorem itself is in
`WeilConjectures.RingTheory.ProEtale.WeakDimension`.

I checked the edge cases mentioned by the source: when A is already a field (so
K is A), the tensor product reduces to B and the assertion is immediate; the
zero and empty-product cases occur only in the proof's valuation construction
and do not alter the theorem's quantified statement.  Universes are fully
polymorphic (`Type*`) as in the source declaration.

Searches made:

- `msearch.py Q05 lem-weil-pbc-weak-etale-integral-closure leanfinder "integrally closed in tensor product weakly etale"` returned general tensor-product/integral-closure declarations but no competing statement; the source theorem was then confirmed directly.
- `msearch.py ... loogle "Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct"` returned no Mathlib match.
- `msearch.py ... grep "isIntegrallyClosedIn_tensorProduct" WeilConjectures` found the exact source declaration in `WeilConjectures/RingTheory/ProEtale/WeakDimension.lean`.
- `rg` over `lean/Sheaf` found no duplicate project declaration.
- `scompile.py` compiled a probe importing `WeilConjectures.RingTheory.ProEtale.WeakDimension` and checking the recorded declaration successfully, with no warnings.

No statement correction, dependency module, new node, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by Q05

I independently opened the node, its blueprint source (order 1218), the full
source theorem in `WeilConjectures/RingTheory/ProEtale/WeakDimension.lean`, and
Stacks `more-algebra.tex`, labels `lemma-normality-goes-up` (092W) and
`lemma-weak-dimension-at-most-1-integrally-closed` (092V), using the tag table.
Tag 092W assumes exactly a normal domain A with fraction field K and a weakly
etale A-algebra B. The surrounding section supplies no Noetherian, finite-type,
characteristic, or nontrivial-B assumption. Tag 092V is the flat injective
ring-epimorphism lemma used in its proof, not an additional hypothesis on B.

The node's objects, hypotheses, and conclusion, matched individually:

1. A commutative domain A: `(A : Type*) [CommRing A] [IsDomain A]`.
   Verdict: exact, with no Noetherian or finiteness assumption.
2. A is integrally closed: `[IsIntegrallyClosedIn A L]`, together with the
   fraction-field characterization in item 3 below, is equivalent to
   `[IsIntegrallyClosed A]` by
   `isIntegrallyClosed_iff_isIntegrallyClosedIn L`. Verdict: exact.
3. K is the fraction field of A: the source calls it L and uses
   `[Field L] [Algebra A L] [FaithfulSMul A L]
   [Algebra.IsAlgebraic A L] [IsIntegrallyClosedIn A L]`.
   These are equivalent to the node's hypotheses, not a larger-field variant.
   In the forward direction, `[IsFractionRing A L]` supplies injectivity and
   hence faithful scalar multiplication; `IsLocalization.isAlgebraic L
   (nonZeroDivisors A)` supplies algebraicity, and integral closedness gives
   `IsIntegrallyClosedIn A L`. Conversely,
   `IsIntegralClosure.isFractionRing_of_algebraic A A` supplies
   `IsFractionRing A L`: every algebraic element has a nonzero A-multiple
   integral over A, hence that multiple belongs to A. Injectivity ensures the
   denominator remains nonzero. Thus every element of L is a fraction from A.
   This also gives item 2. Verdict: exact, with both directions checked in Lean.
4. B is a commutative A-algebra: `(B : Type*) [CommRing B] [Algebra A B]`.
   Verdict: exact; B is not required to be a domain, field, or nonzero ring.
5. B/A is weakly etale in `def-weil-pbc-ind-etale-algebra`:
   `[Algebra.WeaklyEtale A B]`. I opened that node's recorded module
   `Sheaf.RingTheory.IndPrincipalZariski` and the public upstream imports, then
   the actual Mathlib class in `Mathlib/RingTheory/Etale/Weakly.lean`.
   Its fields assert flatness of B over A and flatness of tensor multiplication
   `B ⊗[A] B → B`, exactly the node and Stacks definition. The class docstring
   has a codomain typo, but its actual `flat_lmul'` field has codomain B.
   Verdict: the existing notion is used, with no private copy or extra instance.
6. Conclusion: `IsIntegrallyClosedIn B (B ⊗[A] L)`. I opened Mathlib's
   `IsIntegrallyClosedIn`, its `IsIntegralClosure` definition, and
   `isIntegrallyClosedIn_iff`: this asserts injectivity of the canonical B-map
   and that every integral element of the tensor product is in its image.
   The B-algebra structure is the standard left inclusion, not an arbitrary
   map. With L identified as K by item 3, this is the node's only conclusion.
   Verdict: exact; no extra conclusion or reordered dependent quantifier.

Edge cases: A is necessarily nonzero because it is a domain, as in Stacks.
A may already be a field and L = A is allowed; there is no proper-extension
hypothesis. B may be the zero ring, so the empty affine scheme is retained.
There is no index set, degree n, or geometric object in the statement; empty
products appear only in the proof, and the A = K case is covered independently
of that construction. There is no characteristic restriction. The printed
signature has independent universes `u_1`, `u_2`, `u_3` for A, B, L. The
bidirectional check used explicitly independent universes u, v, w and compiled.

I also read the source proof against the four proof paragraphs: the valuation
product/weak-dimension exact square, flat tensor base change, ascent of weak
dimension, and the integral finite-subalgebra ring-epimorphism argument followed
by the pullback. The existing source declaration bears `@[stacks 092W]` and a
source docstring; existing declarations are reused, not rewritten to add project
docstrings. Its complete proof has no sorry. There are no delivered definitions,
new nodes, dependency modules, or newly postponed theorems, so H5/H6/H12/H13
introduce no further obligations. I opened the recorded proof-dependency
signatures in `Sheaf.RingTheory.IndEtaleStability` and
`Sheaf.RingTheory.WeaklyEtaleTor`; they supply the expected stability and
flat-resolution bounds. No alternative notion is needed.

Independent searches, using wording other than the first reader:

- `msearch.py ... leanfinder "normal domain fraction field weakly etale algebra
  integral closure"`: eight hits, including
  `IsIntegralClosure.isFractionRing_of_algebraic`, which resolves the apparent
  fraction-field mismatch; no separate weakly-etale closure statement.
- `msearch.py ... leansearch "weakly etale algebra over an integrally closed
  domain is integrally closed in tensor product with fraction field"`: eight
  general integral-closure/tensor and etale hits, no competing exact theorem.
- `msearch.py ... loogle "IsIntegrallyClosedIn"`: twelve hits, including the
  fraction-field equivalence and the actual integral-closure definitions; no
  Mathlib weakly-etale tensor closure theorem. An earlier tensor-notation query
  failed to parse and is not counted as negative evidence.
- `msearch.py ... grep "normality-goes-up"`: zero indexed hits. Direct `rg` on
  Mathlib, `WeilConjectures`, and `lean/Sheaf`, using `IsIntegrallyClosedIn`,
  `IsFractionRing`, `integrallyClosed`, `weakly.*[Ii]ntegral`, and
  `isIntegrallyClosedIn_tensorProduct`, found the existing upstream theorem
  and its uses, not a separate project statement. I checked the proposed
  specialization name against `dag/lean_names_upstream.json` as well.

Mismatches found and changes made: the worker report did not justify the reverse
fraction-field implication, making its assertion that L renders K incomplete.
I supplied and compiled that implication, and strengthened `lean.note` to record
both directions. An initially drafted specialization was removed after this
check: it would duplicate an equivalent existing theorem. The original
statement, dependency list, and chosen existing declaration remain correct.
The worker report's attribution of a positive hit to its msearch grep is also
inaccurate: its logged indexed grep had zero hits; the positive identification
comes from direct source `rg`, independently repeated here. No statement
correction or citer audit is required because the mathematical node is unchanged.

Validation: `scompile.py Q05 lem-weil-pbc-weak-etale-integral-closure` compiled
`scratchpad/EquivalenceCheck.lean`, which proves both hypothesis translations,
checks the upstream declaration, and prints its axioms. The final run had no
warnings or errors. The theorem uses exactly `propext`, `Classical.choice`, and
`Quot.sound`. This scratch file is not delivered and adds no library statement.
The node's `lean.statement` was copied verbatim from the existing source
signature, including its trailing `:=`. No variable or universe is unbound.
