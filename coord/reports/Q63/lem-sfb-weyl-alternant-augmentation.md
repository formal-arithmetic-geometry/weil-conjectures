## Worker report

The delivery states `RootPairing.weylAlternant_augmentation` in
`Sheaf.LinearAlgebra.RootSystem.WeylAlternantAugmentation`. Its sole theorem has proof
`sorry`; there are no new definitions, nodes, or dependency repairs. The existing node is
changed only in `lean`.

Source read: Milne, Algebraic Groups (2017), printed p.480 (PDF p.492), including the
antisymmetry operator and integral half-sum before Theorem 22.50; Appendix C.15,
C.18--C.22, printed pp.611--612 (PDF pp.623--624). The augmentation argument itself is
agent-supplied, as the node explicitly says. Its eight proof steps are all reproduced in
the declaration docstring, including the nonzero leading coefficient argument.

Hypothesis and clause correspondence:

- `X : Type v` and `Y : Type w`, each with `AddCommGroup`, `Module.Free ℤ`, and
  `Module.Finite ℤ`, are the two finite-rank free abelian groups. Separate, explicitly
  bound universes impose no equality or smallness restriction.
- `P : RootPairing ι ℤ X Y` is precisely the integer root-pairing convention cited by
  the dependency. `P.toLinearMap` is the bilinear pairing, and the structure's
  `isPerfPair_toLinearMap` makes its two induced maps to integer duals bijective.
  `P.root` and `P.coroot` are embeddings with the common index type `ι`. The structure
  supplies pairing two and simultaneous reflection permutations of roots and coroots.
  Pairing two over ℤ also implies each root and coroot is nonzero. `[Fintype ι]` is the
  finiteness of the root set. Crystallographic integrality is automatic over ℤ, via
  Mathlib's self-valued `RootPairing.IsValuedIn` instance.
- `hroot` and `hcoroot` say that a nonzero integer multiple of every lattice vector
  belongs to the corresponding integer root span. For free abelian groups these are
  exactly rational spanning: clear the finitely many rational denominators in an
  expression in the rational span; conversely divide by the displayed nonzero integer
  after scalar extension. No integral spanning assumption is added. In particular,
  `[P.IsRootSystem]` over ℤ would be too strong and is deliberately not used.
- `[P.IsReduced]` says a dependent pair of roots consists of equal or opposite roots.
  In a free integer lattice this is exactly reducedness over ℚ: rational dependence can
  be cleared to integer dependence, and conversely integer dependence remains rational
  dependence. This excludes precisely the other scalar multiples of a root.
- `b : P.Base` supplies the simple-root subset and the one-sign integral expansions.
  `RootPairing.Base` also expresses the analogous coroot conditions. Its module
  docstring explicitly states their equivalence with the usual base definition for
  reduced pairings. Thus this uses the established definition without adding a new
  hypothesis to the mathematical base notion. `b.IsPos` selects the positive roots;
  it is positive height, equivalent to nonzero nonnegative simple coordinates here.
- `ρ : X` and `hρ : (2 : ℤ) • ρ = ∑ i ∈ Finset.univ.filter b.IsPos, P.root i`
  are exactly the assumption that the half-sum is integral. Since X is torsion-free,
  this determines the half-sum uniquely and includes rank zero.
- `P.weylGroup` is Mathlib's reflection-generated group of root-pairing automorphisms.
  Its module explains its identification with the usual group of linear reflections
  on the weight space. The weight action is faithful and is the action `g • x` used
  here. `[Fintype P.weylGroup]` renders the stipulated finite Weyl group and permits
  its finite sum; it does not substitute a larger arbitrary group.
- The two sums in `hq` are exactly `A(σ)` and `A(ν)`. `AddMonoidAlgebra ℚ X` is the
  actual group algebra, with convolution multiplication, and
  `AddMonoidAlgebra.single (g • λ) (det g)` is `det(g) e^(gλ)`.
  `P.weylGroupRootRep g` is the integral linear endomorphism on X. Its integer
  `LinearMap.det`, cast to ℚ, equals its rational determinant: an integral lattice
  basis gives the same matrix before and after rational scalar extension. No sign
  character or arbitrary representation is supplied instead of the determinant.
- `ν σ : X` are arbitrary lattice elements. `hσ` is nonzero pairing of σ with
  **every** coroot, exactly the regularity hypothesis. There is no regularity or
  dominance assumption on ν.
- `q` is an actual group-algebra element. `hq` is just `q * A(σ) = A(ν)`, with no
  extra quotient existence assumption and no chosen fraction-field quotient.
- `q.coeff.sum (fun _ a ↦ a)` is augmentation, the finite sum of all coefficients.
  The first conjunct is exactly the product of the rational ratios of the ν and σ
  pairings over the positive roots. Coercions into ℚ occur before division.
- The second conjunct says `0 < P.toLinearMap ρ (P.coroot i)` for every `b.IsPos i`.
  The value already has type ℤ, so both its integrality and positivity are present.

Dependency declarations read and used:

- `lem-sfb-crystallographic-positive-base` is a Mathlib leaf with match
  `RootPairing.linearIndepOn_root_baseOf'` in
  `Mathlib.LinearAlgebra.RootSystem.BaseExists`. I read its full signature and
  docstring at lines 61--92 and its `RootPairing` setup. Its module is publicly imported.
  The node gives the integer-pairing conventions rather than a separate bundled
  object. The statement uses that exact `RootPairing` structure, not a private copy;
  it does not need to apply the linear-independence theorem when a base is already given.
- `RootPairing`, `RootPairing.Base`, `RootPairing.Base.IsPos`,
  `RootPairing.IsReduced`, `RootPairing.weylGroup`, and
  `RootPairing.weylGroupRootRep` were read in Mathlib's Defs, Base, Reduced, and
  WeylGroup files, including their full signatures and docstrings.
- `lem-sfb-polynomial-field-ufd` has Mathlib match
  `MvPolynomial.uniqueFactorizationMonoid, MvPolynomial.instIsDomainOfIsCancelAdd`.
  The recorded module `Mathlib.RingTheory.Polynomial.UniqueFactorization` is imported
  privately as a proof dependency. `lem-sfb-distinct-hyperplane-polynomial-divisibility`
  has no Lean record or Mathlib match yet, so no module can currently be imported for it.
  Its use and node id remain in the proof docstring; it is not a statement prerequisite.

Edge cases checked mathematically before delivery:

- Empty index set and zero rank: `hroot` and torsion-freeness force X = 0;
  `hcoroot` forces Y = 0. The generated Weyl group is trivial, both sums are the
  monomial one, `hq` forces q = 1, coefficient sum is one, the product is one,
  and positivity is vacuous. No `Nonempty ι` or positive-rank assumption occurs.
- Rank-one integral half-sum case: X = Y = ℤ with the standard perfect pairing,
  roots ±2 and coroots ±1; the positive half-sum is 1. This is allowed by `hroot`
  even though the roots span 2ℤ, not ℤ. The formula becomes augmentation ν/σ;
  for σ = 1 and ν = 2, q = e^1 + e^(-1) has augmentation 2, as required.
- Singular ν, including ν = 0 in positive rank, is allowed. Its product is zero;
  the formal-exponential coefficient argument does not cancel D(ν).
- σ has all root pairings nonzero, so none of the rational denominators is zero.
  Positive and negative σ pairings are both allowed. Reducible root systems are
  not excluded. q has finite support by the group-algebra definition; its lattice
  exponents can be negative without any Laurent-polynomial restriction.

Searches made (all through the prescribed wrappers or read-only source searches):

- `msearch.py ... leanfinder "The augmentation of a quotient of Weyl alternants equals
  the product of positive coroot pairings"`: eight hits, including
  `RootPairing.coxeterWeightIn`, the canonical-bilinear product results, and the
  Lie-algebra coroot cast result. None states the group-algebra augmentation formula.
- `msearch.py ... leansearch` with that same query: eight hits, including
  `RootPairing.coxeterWeight`, `InvariantForm.apply_weylGroup_smul`, `weylGroup`,
  `weylGroupCorootRep`, and `span_orbit_eq_top`; no augmentation theorem.
- `msearch.py ... loogle "RootPairing, AddMonoidAlgebra"`: zero hits.
- `msearch.py ... grep "alternant|denominator|augmentation" LinearAlgebra/RootSystem`:
  zero hits. Direct `rg` in Mathlib located the existing RootPairing/Base/WeylGroup
  constructions, the determinant, and AddMonoidAlgebra's real finite-coefficient
  structure and singleton basis terms, which are used directly.
- `rg -n "alternant|Alternant|weyl.*augmentation|weylAlternant"` in
  `lean/WeilConjectures` and `lean/Sheaf`: no matching declaration.
  `rg -n "lem-sfb-weyl-alternant-augmentation" lean/WeilConjectures`: zero hits.
- Collision search for `weylAlternant_augmentation|weylAlternantAugmentation` in
  Mathlib, both project Lean roots, and `dag/lean_names_upstream.json`: zero hits.
- Read-only blueprint/latest and DAG searches for alternant/antisymmetry locate the
  supporting chain, not an existing formalization of this formula. All required
  notions are already Mathlib constructions, so no new definition node is needed.

No statement correction, unresolved node fault, or STATEMENT-DISPUTED flag is needed.
The final module compiled through `scompile.py` in sandbox and library modes, with
no errors or warnings. No global build or direct repository mutation was run.

## Second reading by Q63

This is a second pass by the same dispatched worker; the explicit dispatcher instruction
forbids starting another agent. The maintainer's independent review follows delivery.
I reopened the item JSON and the complete Lean signature and checked the correspondence
above clause by clause. In particular I checked that `hq` multiplies the σ alternant,
that ν is the numerator of each product factor, that the determinant is of the weight
representation, and that positivity is an integer inequality for the given half-sum.
The initial compiler run found the scoped-Classical style warning; I replaced the
file-wide Classical opening with `open Classical in` on this declaration and recompiled
cleanly. I also checked the potential mismatch between integral and rational spanning:
the delivered `hroot`/`hcoroot` use nonzero multiples, preserving the rank-one 2ℤ example.
The Mathlib Base documentation justifies its extra coroot fields under reducedness.
There were no mathematical signature mismatches to repair and no changes to the node's
statement, dependencies, or proof plan. The copied `lean.statement` is the declaration
signature verbatim, excluding the `:=` proof delimiter.
