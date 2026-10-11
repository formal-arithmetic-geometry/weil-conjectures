## Worker report

The module `Sheaf.FieldTheory.ExistsPBasis` states `Field.exists_p_basis`, with its proof
left as `sorry`. No definitions or extra nodes are needed: all mathematical data in the
statement use existing Mathlib constructions. The node's statement is unchanged.

Hypothesis and conclusion correspondence:
- A prime number p: `(p : ℕ) [Fact p.Prime]`.
- A field k: `(k : Type u) [Field k]`, exactly the dependency `def-weil-field`.
- Characteristic p: `[CharP k p]`. Together with primality this supplies `ExpChar k p`,
  as required by Frobenius; this adds no hypothesis.
- The subfield k^p = {a^p}: `(frobenius k p).fieldRange`, whose underlying set is exactly
  the range of the map `a ↦ a ^ p`. Its canonical subfield algebra gives k its vector
  space structure over k^p, without an arbitrary choice of scalar action.
- There exists a family `(t_i)`: `∃ (I : Type u) (t : I → k)`.
- All integer exponent families with 0 ≤ e_i < p and finite support:
  `{E : I →₀ ℕ // ∀ i : I, E i < p}`. Natural numbers encode exactly the nonnegative
  integers, and Finsupp encodes exactly the finite-support condition. The bound applies
  to every index, including those outside the support.
- The monomial product: `E.val.prod (fun i e => t i ^ e)` is the product over its finite
  support; omitted factors are powers with exponent zero, hence 1.
- These monomials form a basis: existence of `b : Module.Basis ... (frobenius k p).fieldRange k`
  and `∀ E, b E = ...` prescribes every basis vector, and entails both linear independence
  and spanning. The scalar field and underlying vector space are exactly k^p and k.

Dependency declaration read: `def-weil-field` is a Mathlib leaf with `mathlib_match = ["Field"]`.
Its full signature and docstring were read in `Mathlib.Algebra.Field.Defs:180`, where
`class Field (K : Type u) extends CommRing K, DivisionRing K`.
Additional standard Mathlib declarations read and used: `frobenius` in
`Mathlib.Algebra.CharP.Lemmas` (imported through `Mathlib.Algebra.CharP.Frobenius`),
`RingHom.fieldRange` and `Subfield.toAlgebra` in `Mathlib.Algebra.Field.Subfield.Basic`,
`Module.Basis` in `Mathlib.LinearAlgebra.Basis.Defs`, and `Finsupp.prod` in
`Mathlib.Algebra.BigOperators.Finsupp.Basic`.

Edge cases checked before writing: a perfect field admits the empty p-basis; for empty I
there is exactly one Finsupp, the zero function, and its product is 1. In an imperfect field
I can be infinite, since no finiteness condition is imposed on I, only on each exponent
family. The zero exponent gives the required constant monomial 1. Primality excludes p=0
and p=1; p=2 includes both exponents 0 and 1. A field cannot be the zero ring.
Taking I in the field's universe excludes no case of existence: the source constructs
I as a subset of k. No Nonempty requirement excludes the perfect-field case.

Source read: local literature/stacks-project/more-algebra.tex is not present on this machine;
the original source was read at https://stacks.math.columbia.edu/tag/07P1 and
https://stacks.math.columbia.edu/tag/07P2. The latter's Zorn/maximality proof is the node's
route; the docstring includes all six steps of the node's expanded proof.

Searches (2026-10-11):
- msearch.py leansearch, "Every field of positive characteristic has a p-basis over its
  subfield of p-th powers": service unavailable (Internal Server Error), recorded as
  unavailable without a mathematical verdict.
- msearch.py leanfinder, "Every field of characteristic p has a p-basis: restricted
  finite-support monomials form a basis over the subfield of p-th powers": eight hits,
  including `Module.Basis.mapPowExpCharPowOfIsSeparable`, power-basis lemmas and
  separable transcendence-basis existence. None states p-basis existence.
- msearch.py loogle, "frobenius, RingHom.fieldRange, Module.Basis": no hits.
- msearch.py grep, "pBasis|p_basis|p-basis|pIndependent|p_independent", FieldTheory:
  nine unrelated hits (galGroupBasis and basisOfBasisRight), no p-basis declaration.
- rg over WeilConjectures and lean/Sheaf for pBasis, p_basis, p-basis and the item id:
  source hits are unrelated app_basis names; Sheaf hits are references in proof docstrings
  of IntersectionSubfieldsDifferentials, KaehlerDifferentialZeroIffPow and DetectNonPthPower,
  not a statement or definition of p-basis.
- rg for `exists_p_basis` over Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no existing declaration with the proposed name.
- Direct rg/read of Frobenius, fieldRange, Basis and Finsupp.prod located the standard
  constructions used in the statement.

No statement dispute, correction or dependency fault was found. Only the theorem proof
is deferred, and its docstring records the natural-language proof and dependency nodes.

## Second reading by G1

I reread the node statement, its Stacks 07P1/07P2 source description, and the Lean
signature item by item. The prime is rendered by `(p : ℕ) [Fact p.Prime]`; the field by
`(k : Type u) [Field k]`; and characteristic p by `[CharP k p]`. The subfield of p-th
powers is exactly `(frobenius k p).fieldRange`, with its canonical algebra structure on
`k`. The existential family is `∃ (I : Type u) (t : I → k)`. Exponent families are
`{E : I →₀ ℕ // ∀ i : I, E i < p}`, which gives natural nonnegative exponents, the strict
p bound at every index, and finite support through `Finsupp`. The monomial is rendered as
`E.val.prod (fun i e => t i ^ e)`. The final clause is an existential
`Module.Basis` over `(frobenius k p).fieldRange` with underlying module `k`, followed by
`∀ E` identifying each basis vector with that monomial. Quantifier order and all source
clauses agree; no extra finiteness, nonemptiness, separability, or universe hypothesis is
present.

Edge cases remain covered: `I = Empty` gives the unique zero exponent and monomial 1,
so perfect fields may have an empty p-basis; infinite families are allowed while each
exponent has finite support; p is prime (hence nonzero and greater than one); and the
field cannot be the zero ring. The index universe `Type u` matches the field universe and
excludes no construction from the source.

I repeated the searches over Mathlib, the source repository, and `lean/Sheaf`; only
ordinary power-basis, transcendence-basis, and unrelated basis declarations were found.
No existing p-basis notion or theorem matches this statement. The dependency
`def-weil-field` is the Mathlib `Field` class and is usable as recorded. The module
compiled cleanly with `scompile.py`; no mismatch was found and no change was needed.

## Reviewer fix (R-pbe1254, stage 2)

The subfield `k^p` is restated from `(frobenius k p).fieldRange` (a `Subfield` with
`Subfield.toAlgebra`) to the inline p-basis form landed by C1 for
lem-weil-pbc-p-basis-differentials-basis (63e688ffc):
`Module.Basis {E : I →₀ ℕ // ∀ i : I, E i < p} (IntermediateField.adjoin (ZMod p) (Set.range (fun x : k => x ^ p))) k`
with `∀ E, b E = E.val.prod (fun i e => t i ^ e)`, the base field being the prime field
`ZMod p` (the node's extension F_p → k; `(ZMod p) k^p = k^p`), with Mathlib's
`ZMod.algebra` registered locally as in the landed IntersectionSubfieldsDifferentials.
The two subfields have the same carrier; the change makes the p-basis one notion, so the
existence feeds C1's differentials-basis lemma with `k := ZMod p` directly. Hypotheses
(prime p, field k, `CharP k p`; `CharP (ZMod p) p` is an instance) and the tied
existential `∃ (I : Type u) (t : I → k) (b : …)` are unchanged.
