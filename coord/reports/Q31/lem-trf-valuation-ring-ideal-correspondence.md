## Worker report

The module `Sheaf.RingTheory.ValuationRingIdealCorrespondence` states
`ValuationSubring.exists_ideal_orderEquiv_valueGroup`, with its sole proof `sorry`.
It states Stacks `algebra.tex`, Tag 00IH, using the value-group convention of Tag
00IE. Both source passages were read in the local Stacks source, including the
paragraph defining group ideals and their primality immediately before 00IH.
The node's statement needs no correction. No definitions or additional nodes
are introduced.

Hypothesis and conclusion correspondence:

- A field K is `{K : Type u} [Field K]`, in an arbitrary explicit universe `u`.
- The subring A of K satisfying the valuation alternative is
  `(A : ValuationSubring K)`. Its `mem_or_inv_mem'` is the exact alternative,
  also at zero (where membership holds automatically). Mathlib supplies
  `CommRing A`, `IsDomain A`, `ValuationRing A`, and `IsFractionRing A K`.
  Thus no extra fraction-field, locality, finiteness, or nontrivial-valuation
  assumption is imposed.
- The quotient Gamma is `Additive (OrderDual A.ValueGroupˣ)`. This is a direct
  use of Mathlib's quotient, not an arbitrary valuation into another group.
  `ValuationRing.ValueGroup A K` is `Quotient (MulAction.orbitRel Aˣ K)`;
  `ValuationSubring.ValueGroup` is that type with its ordered group-with-zero
  structure. Units remove precisely the class of zero. Its nonzero classes
  are exactly K-units modulo multiplication by A-units. The inherited unit
  order compares their values. `OrderDual` reverses Mathlib's convention:
  by `valuation_le_iff`, v(y) <= v(x) means y=c*x for c in A, equivalently
  y/x is in A. `Additive` writes multiplication as addition and one as zero.
  These standard type tags and unit instances provide the exact additive
  ordered group of the node, without a second value-group definition.
- Ideals of Gamma are the subtype
  `{I : Set (Additive (OrderDual A.ValueGroupˣ)) //
  I ⊆ Set.Ici 0 ∧ IsUpperSet I}`. The first predicate is exactly containment
  in the nonnegative cone; the second is upward closure in Gamma.
- Ideals of A, with inclusion, are `Ideal A`. Existence of
  `e : Ideal A ≃o ...` gives a bijection preserving inclusion in both
  directions. The order on sets and their subtype is inclusion.
- Canonicity is specified by the first conjunct, for every ideal J and x in
  K-units. The term
  `Additive.ofMul (OrderDual.toDual
  (Units.map A.valuation.toMonoidWithZeroHom.toMonoidHom x))`
  is exactly [x]. Its membership in `(e J).1` is equivalent to
  `∃ a : A, a ∈ J ∧ (a : K) = (x : K)`: x has a representative in J.
  Since x is a unit of the field, that representative is nonzero. This is
  exactly the value-set map in the node's proof, and determines the map
  uniquely since the valuation is surjective and the units map covers all
  nonzero classes. The inverse order isomorphism consequently has the
  specified inverse construction: zero together with those nonzero elements
  whose values belong to I.
- Prime ideals correspond by the second conjunct, for every J:
  `J.IsPrime ↔ 0 ∉ (e J).1 ∧ ...`. The remaining quantified condition is
  `∀ γ δ, 0 ≤ γ → 0 ≤ δ → γ + δ ∈ (e J).1 →
  γ ∈ (e J).1 ∨ δ ∈ (e J).1`, exactly the stated group-ideal primality.
  Both directions are included. Zero here is [1], as required by Stacks.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, full
  declaration and docstring read (lines 170–180).
- `def-trf-valuation-ring`: Mathlib `ValuationRing` and
  `ValuationRing.TFAE`, `Mathlib.RingTheory.Valuation.ValuationRing`, read at
  lines 62–64 and 407–416. The more directly bundled, equivalent subring
  interface `ValuationSubring` is imported from
  `Mathlib.RingTheory.Valuation.ValuationSubring`; its full declaration,
  domain/fraction-field/valuation-ring instances, `ValueGroup`, `valuation`,
  `valuation_eq_iff`, `valuation_le_iff`, and `valuation_surjective` were read.
  Thus the dependency's notion is used with its specified ambient field.
- `def-trf-totally-ordered-abelian-group`: the recorded Mathlib representation
  is `[AddCommGroup] [LinearOrder] [IsOrderedAddMonoid]` (the former
  `LinearOrderedAddCommGroup` name is only a namespace). The representation
  and the additive ordered-monoid class were read. The group operations,
  linear order, and translation invariance on the type used here come from
  the existing units, order-dual and additive instances, imported via
  `Mathlib.Algebra.Order.Group.Units` and
  `Mathlib.Algebra.Order.Monoid.TypeTags`. No dependency repair is necessary.

Edge cases checked mathematically before writing: for A=K, Gamma is the
zero group, and the zero and unit ring ideals correspond respectively to
empty and singleton-{0} value sets. The empty value set is prime and
corresponds to the zero prime ideal of the field. For any valuation ring,
the zero ideal maps to the empty set, and the unit ideal maps to the entire
nonnegative cone; the latter contains the zero class and is not prime.
Zero field elements do not acquire a group value: representatives are
quantified as K-units, and zero is restored automatically in the inverse
ring ideal. Non-discrete, higher-rank, and trivial valuations are all
allowed, as are both characteristics and arbitrary universe sizes.

Searches made with the prescribed wrapper (all outputs inspected):

- LeanFinder: "ideals of a valuation subring correspond in order to upward
  closed subsets of the nonnegative additive value group preserving prime
  ideals". Eight results, including `ValuationSubring.primeSpectrumOrderEquiv`
  and `idealOfLE` lemmas; these concern overrings, not group ideals.
- Loogle: `ValuationSubring.valuation_le_iff, Units.map`. Zero hits.
- LeanSearch: "ideals of a valuation ring correspond to upward closed sets
  in its value group". Eight results, including `Valuation.leIdeal`,
  `ltIdeal`, and principal-ideal descriptions; no complete correspondence.
- Wrapper grep in Mathlib/RingTheory/Valuation:
  `ideal.*[Ee]quiv|[Ee]quiv.*ideal|ValueGroup|valuation_le_iff`. Twenty-five
  results locate the existing quotient and valuation interfaces; none is
  this theorem.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, the side `lean/Sheaf`
  library and `dag/lean_names_upstream.json` for
  `idealOrderEquiv|ideal_orderEquiv|ideal_valueGroup|valueGroupIdeal|valueGroup_ideal`
  found no match. The exact chosen declaration name also had no match.
  Upstream search for the item's id found no match. Concept searches in
  the project and DAG found the separate
  `AddSubgroup.orderedGroup_primePositiveConeIdeal_orderDualEquiv_convexAddSubgroup`,
  whose source and full statement were read; it is the subsequent
  prime-group-ideal/convex-subgroup correspondence, not the present theorem.

Validation: the prescribed `scompile.py Q31
lem-trf-valuation-ring-ideal-correspondence` compiled this delivered file
successfully in both sandbox and library phases, with no errors or warnings.
All binders and universes are explicit, and `autoImplicit` is disabled.
The only postponed proof has the node's complete four-step proof in its
docstring. There are no statement disputes or hollow definitions.

## Second reading by Q31

Author's second pass, performed with the node, source passage and final Lean
file open; this is not an independent review. The task explicitly assigns
independent review to the maintainer and prohibits spawning another agent.
The field and valuation-subring hypotheses match. The quotient is the actual
Mathlib quotient with zero discarded, with order reversed before switching
to additive notation. The subtype includes both nonnegativity and upward
closure. The order isomorphism asserts the full ideal correspondence, the
representative formula fixes the canonical map, and the final iff includes
both clauses of primality. The class of 1 is additive zero, while the field
zero has no class in Gamma. No extra assumption, missing clause, or mismatch
was found; no edits were required on this pass.
