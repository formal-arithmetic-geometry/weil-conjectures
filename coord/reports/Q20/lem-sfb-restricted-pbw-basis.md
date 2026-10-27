## Worker report

The delivery states `RestrictedEnvelopingAlgebra.exists_restricted_pbw_basis` in
`Sheaf.Algebra.Lie.RestrictedPBWBasis`. Its only postponed proof is this theorem,
with `sorry`; its docstring contains all seven steps of the node's proof. The
supporting definition module contains actual constructions and no `sorry`.
The item's natural-language statement is unchanged. Its only extra statement
dependency is the new definition node listed below.

Hypothesis and clause correspondence, with the node and Lean file read together:

- A field F: `(F : Type u) [Field F]`, exactly `def-weil-field`'s Mathlib match.
- Prime characteristic p > 0: `(p : ℕ) [Fact p.Prime] [CharP F p]`. Primality
  entails positivity and p ≥ 2; neither characteristic two nor finite fields are
  excluded.
- A finite-dimensional Lie algebra: `(L : Type v) [LieRing L] [LieAlgebra F L]`
  and `(n : ℕ) (e : Module.Basis (Fin n) F L)`. A specified finite basis itself
  expresses finite dimensionality, so no independent finrank equation is needed.
  Index `i : Fin n` corresponds to the paper's `e_(i+1)`.
- The given restricted operation: `(q : L → L)` and
  `(hq : LieAlgebra.IsRestrictedOperation F p q)`. Unfolding the latter gives
  exactly the three node axioms: scalar p-semilinearity, equality of adjoint
  endomorphisms `ad F L (q x) = ad F L x ^ p`, and the Jacobson sum formula.
  No p-nilpotence assumption is made.
- The coefficient normalization: `restrictedJacobsonTerm F p x y i` is inverse
  scalar multiplication by `(i : F)` on `jacobsonAdjointCoefficients x y
  (p-1) (i-1)`. The recursion computes formal coefficients of `ad(tx+y)^m(x)`:
  the initial coefficients are x at zero and zero otherwise, and bracketing
  with `tx+y` sends coefficient k to `[x,C_(k-1)] + [y,C_k]`. Negative
  coefficients are zero. Thus this is the specified scalar-extension
  computation, including over finite fields; no detection by evaluation is
  assumed. On `Finset.Ico 1 p`, every divided scalar is nonzero.
- The tensor algebra and inclusion: Mathlib `TensorAlgebra F L` and
  `TensorAlgebra.ι F`. Multiplication is its existing concatenation product.
- The full defining ideal: `LieAlgebra.restrictedEnvelopingIdeal F p q` is
  `TwoSidedIdeal.span` of the union of all `tensorBracketRelation F x y` and
  all `tensorRestrictedRelation F p q x`. These helpers are exactly the two
  displayed differences in the node, with the same signs and all x,y.
- The quotient u(L): `RestrictedEnvelopingAlgebra F L p q` is that ideal's
  ring-congruence quotient, with inherited Ring and Algebra F structures.
  Two-sided ideals are closed under scalar multiplication by algebra scalars
  (multiplication by the scalar's central image), so this is the F-algebra
  quotient. Its generator map `RestrictedEnvelopingAlgebra.ι F p q` is the
  quotient algebra map composed with the degree-one linear map.
- Truncated basis: existential `B : Module.Basis (Fin n → Fin p) F (...)`
  supplies precisely one basis vector for each tuple with `0 ≤ a_i < p`.
  The first conjunct identifies `B a` with the product of generator powers
  in `List.finRange n` order. `.prod` is a list product, so this preserves
  order without assuming the quotient commutative.
- Basis-generator presentation: the second conjunct is equality of the full
  defining ideal with the two-sided span of all basis bracket relations
  `(i,j : Fin n)` and all basis p-relations `(i : Fin n)`. It is equality
  of tensor ideals, rather than merely an abstract quotient isomorphism.
- Empty basis: the third conjunct says `n = 0 → ∀ a, B a = 1`. When n = 0
  there is exactly one function `Fin n → Fin p`; the ordered product is
  empty. This explicitly retains the node's sole basis monomial one.

Dependency declarations inspected and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`; read its full
  signature extending `CommRing` and `DivisionRing`, including the latter's
  `Nontrivial` and inverse axiom.
- `def-wf-lie-algebra`: `LieRing` and `LieAlgebra` in
  `Mathlib.Algebra.Lie.Basic`, and `LieAlgebra.ad` in
  `Mathlib.Algebra.Lie.OfAssociative`. Read their docstrings and signatures;
  the alternating and Leibniz bracket laws are Mathlib's Jacobi interface.
- The new dependency `def-sfb-restricted-enveloping-algebra` owns the
  restricted operation, normalized coefficients and quotient constructions.
- Proof imports: `Sheaf.Algebra.Lie.FieldFilteredPBW`, declaration
  `UniversalEnvelopingAlgebra.exists_field_filtered_pbw_basis`, and
  `Sheaf.Algebra.Lie.AssociativeJacobsonIdentities`, declaration
  `Algebra.associative_jacobson_identities`. Both current source modules and
  their complete theorem docstrings and signatures were read. The former's
  local DAG record had not yet acquired `lean`, but its source module is
  already present and compiles as a proof import. Neither proof input is
  redefined here.

Edge cases checked before writing and on a second pass:

- n = 0: q(0) = 0 follows by scalar semilinearity with zero; no basis relation
  generators remain, and the unique tuple indexes one. No Nonempty basis
  index or positive-dimension binder is imposed.
- p = 2: the correction coefficient is `[y,x]`, equal to `[x,y]` in
  characteristic two; no division by two or sign restriction is imposed.
- One-dimensional abelian L: the quotient is `F[X]/(X^p-aX)` when
  q(e) = ae; the family has exponents 0,...,p-1, including when a is nonzero.
- The all-zero exponent tuple gives one in every dimension. No assumption
  that each basis element has positive exponent is added.
- The coefficient recursion is formal, so finite fields are covered.
- Independent universe variables u and v allow a field and Lie algebra in
  different universes. The quotient is the existing tensor quotient universe.

Searches (also captured verbatim in the new node's `mathlib_searches`):

- msearch leanfinder, `A restricted Lie algebra in prime characteristic has a
  PBW basis of its restricted enveloping algebra with exponents less than p`:
  eight unrelated ordinary-enveloping/root/weight hits; no restricted PBW.
- msearch loogle, `"RestrictedLieAlgebra"`: zero hits.
- msearch grep, `RestrictedLie|restricted.envelop|PBW`, Algebra/Lie:
  only a comment in Mathlib/Algebra/Lie/Free.lean requiring PBW.
- msearch leansearch, `Restricted Lie algebra p map Jacobson sum axiom and
  restricted enveloping algebra`: eight ordinary UniversalEnvelopingAlgebra
  hits; these have no p-relation quotient.
- msearch leanfinder, `Definition of restricted p Lie algebra p operation
  scalar ad and Jacobson sum axioms`: eight scalar-restriction/Engel/subalgebra
  hits; no restricted operation.
- msearch grep, `restricted.?Lie|RestrictedLie|restricted.envelop`, all Mathlib:
  zero hits.
- Direct rg over both `lean/WeilConjectures` and `lean/Sheaf` for restricted
  operations/enveloping algebras, and the item's blueprint id in upstream:
  no existing declaration of either notion or theorem. Ordinary PBW and
  associative Jacobson identities are distinct inputs, imported as above.
- DAG search for restricted operation/Lie/enveloping text found this theorem
  and other theorem nodes but no independent definition node. Searches of
  `def-*.json` found no definition. `tools/blueprint_refs.py search
  'restricted Lie'` returned zero nodes; search `envelop` found unrelated
  compactification/Karoubi envelopes. The ancestor command returned None,
  as already recorded for the item, so the new node retains null ancestry
  and prepends this item to the existing via chain.

Source checked directly: local Milne PDF, Definition 10.39 and Theorem 10.40,
printed pp. 206–207, including the central basis elements in the proof and
its ordinary-PBW triangular argument. No statement fault or dispute found.

Validation: both delivered modules compile separately via prescribed
`scompile.py`, against the live server's published build and private sibling
source overlay. Compiler messages are clean (the theorem's expected sorry
is the sole postponed proof). No global build or live-source edit was run.

## New nodes

`def-sfb-restricted-enveloping-algebra` records the missing restricted-operation
and tensor-quotient notion from Milne Definition 10.39, pp. 206–207, using the
coefficient normalization of Proposition 10.38(b). It includes the real finite
coefficient recursion, the three-axiom predicate, the actual two-sided span
and quotient, and the canonical linear inclusion. Ordinary Mathlib enveloping
algebras impose only bracket relations. The semantic, name and source/DAG
searches above found no existing notion carrying the p-operation or quotient.
Its module has eight named declarations, all listed in `lean.declarations`,
each documented with the new node's id. The definitions allow general p,q;
the PBW theorem imposes precisely the prime-characteristic restricted axioms.

## Second reading by Q20

I reopened the node and both finished files for a second clause-by-clause
pass. The dispatcher explicitly prohibits starting other agents, so this is
an additional self-reading, not a claim of independent worker review; the
maintainer's independent review remains the next review step.

The second pass checked all three restricted axioms against the predicate;
the coefficient recurrence's initial and successor equations against the
formal bracket with tx+y; the signs and quantifiers of both tensor generators;
the exact quotient used as B's codomain; the order and exponent bounds of
its list product; equality of tensor ideals for the second conclusion; and
unique indexing plus the explicit one clause at n=0. The finite basis
supplies finite dimensionality without an additional restriction. The
nonzero restricted operation in the one-dimensional test confirmed that
there is no inadvertent p-nilpotence assumption. Both theorem proof imports
were retained. No mismatch was found and no mathematical statement changed.
