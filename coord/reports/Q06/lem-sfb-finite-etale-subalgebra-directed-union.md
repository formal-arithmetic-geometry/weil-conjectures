## Worker report

The module `Sheaf.RingTheory.FiniteEtaleSubalgebraUnion` states
`Algebra.finiteEtaleSubalgebra_directed_union`. The only postponed proof is this
named theorem, with all six DAG proof steps in its docstring. Two real helper
definitions belong to the same notion introduced by this node:
`Algebra.finiteEtaleSubalgebras` is the set of finite étale subalgebras, and
`Algebra.finiteEtaleSubalgebraUnion` is its subalgebra supremum. The theorem explicitly
identifies the supremum's carrier with the literal set union, so the construction
does not assume directedness or choose data from an unproved existence theorem.
No new nodes, dependency repairs, or statement corrections are needed.

Clause-by-clause correspondence:

- A field k is `(k : Type u) [Field k]`. The arbitrary commutative unital algebra
  is `(A : Type v) [CommRing A] [Algebra k A]`. No `Nontrivial A`, reducedness,
  finite-type or weakly-étale assumption is imposed.
- The unital k-subalgebras are `Subalgebra k A`. The family consists exactly of
  those D with `Module.Finite k D ∧ Algebra.Etale k D`. These are the affine-local
  notions from the recorded dependencies, not new predicates for finiteness or
  étaleness. `IsFinite.SpecMap_iff`, `RingHom.finite_algebraMap`,
  `HasRingHomProperty.Spec_iff` and `RingHom.etale_algebraMap` identify them with
  finiteness and étaleness of `Spec D → Spec k`. Thus the wording with spectra
  is rendered equivalently at the algebra level without changing hypotheses.
- Nonemptiness is `(finiteEtaleSubalgebras k A).Nonempty`.
- Directedness under inclusion is `DirectedOn (· ≤ ·) (finiteEtaleSubalgebras k A)`.
- Being a subalgebra is given by the real `Subalgebra k A`-valued supremum
  definition. Its equality with the set-theoretic union is the third conjunct,
  `(finiteEtaleSubalgebraUnion k A : Set A) =
  (⋃ D ∈ finiteEtaleSubalgebras k A, (D : Set A))`.
- Every finite subset is quantified as `∀ s : Set A, s.Finite →
  s ⊆ (finiteEtaleSubalgebraUnion k A : Set A) → ...`, with conclusion
  `∃ D ∈ finiteEtaleSubalgebras k A, s ⊆ (D : Set A)`.
- Every idempotent is `∀ e : A, e ^ 2 = e → e ∈ finiteEtaleSubalgebraUnion k A`.
- The final universal quantifier ranges over `(C : Type w) [CommRing C]
  [Algebra k C]`, with hypotheses `Module.Finite k C → Algebra.Etale k C →`.
  The image of every unital algebra map `h : C →ₐ[k] A` is its existing Mathlib
  `h.range`, and its membership in the family is the first final conjunct.
- Unique factorization is `∃! g : C →ₐ[k] finiteEtaleSubalgebraUnion k A,
  (finiteEtaleSubalgebraUnion k A).val.comp g = h`. Mathlib's `Subalgebra.val`
  is precisely the inclusion. The independent universe w covers source
  algebras of any size; it is not a testing hypothesis restricted below A.

Recorded dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, full class and docstring.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme, full definitions and docstrings; used through
  the standard affine/algebra identification explained above. The two recorded
  morphism modules are public imports, as are the algebra predicates used.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  Mathlib.AlgebraicGeometry.Morphisms.Finite, full signature and docstring;
  only the finite part is needed. Its `SpecMap_iff` justifies Module.Finite.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale, full signature and docstring;
  `HasRingHomProperty.Spec_iff` and `RingHom.etale_algebraMap` give the
  algebraic formulation used in the statement.
- Proof import Mathlib.RingTheory.Etale.Field:
  `Algebra.Etale.iff_exists_algEquiv_prod` for
  `lem-weil-pbc-etale-algebra-over-field-product`; read full signature/docstring.
- Proof import WeilConjectures.Mathlib.RingTheory.Etale.Field:
  `Algebra.Etale.of_finite_of_isSeparable`, exactly the recorded declaration of
  `lem-weil-pbc-finite-separable-extension-etale`; read full signature/docstring.
- Proof import Mathlib.RingTheory.Etale.Pi: finite-product étale instance
  recorded by `lem-weil-pbc-etale-algebra-finite-product`; read its signature.
- Mathlib.RingTheory.Etale.Basic supplies the public predicate `Algebra.Etale`
  and `Algebra.Etale.baseChange` for `lem-weil-pbc-etale-ring-base-change`.
- Mathlib.AlgebraicGeometry.Morphisms.Etale supplies `Etale.etale_comp` for
  clause (2) of `lem-weil-pbc-etale-composition-cancellation` (read all clauses).
- Existing Mathlib `AlgHom.range`, `Subalgebra.val`, complete lattice/sSup
  construction were read, and reused directly.

Edge cases checked mathematically before writing: the zero algebra has one
subalgebra, which is finite étale, and the map k → 0 has this image. There is
no injectivity assumption on h. Empty products in the image classification
and the empty finite subset are covered. For e=0 and e=1, both lie in every
stage. For k[ε]/ε², the union is k; reducedness is not assumed on A. For
k×k, both coordinate idempotents occur, and quotients can delete either or
both factors. For an imperfect field and a purely inseparable finite
extension, no separability of A is imposed. Independent universes u, v, w
exclude no zero/small/large algebra case.

Searches performed using the prescribed msearch wrapper:

- leanfinder: "The finite etale subalgebras of an arbitrary algebra over a field
  form a nonempty directed family whose union contains every idempotent and every
  finite etale algebra image". Eight hits: coefficient descent
  `Algebra.Etale.exists_subalgebra_fg`, classification
  `Algebra.Etale.iff_exists_algEquiv_prod`, formally-étale classification,
  étale-locus and finite-product infrastructure. No match for this statement.
- loogle: `"Etale", "Subalgebra"`: one hit,
  `Algebra.Etale.exists_subalgebra_fg`. Read its full signature/docstring;
  this descends coefficients of an already étale algebra, not this family/union.
- grep: `max.*[Ee]tale|[Ee]tale.*[Ss]ubalgebra|finiteEtaleSubalgebra`,
  RingTheory: two hits, NoetherianDescent.lean and Etale/Field.lean.
  Neither states the item.
- rg over lean/WeilConjectures and lean/Sheaf for the item id and family/union
  names: no declaration of this item. Broad étale/subalgebra searches found
  `Algebra.WeaklyEtale.etale_of_fg`, inertia-invariant subalgebras, and related
  proof text; these require weakly étale hypotheses or other specialized data.
- rg over both source roots and dag/lean_names_upstream.json for all three
  proposed declaration names: no existing names.

Source inspected: literature/stacks-project/more-algebra.tex lines 30845–30980,
Tags 0CKR/0CKS/0CKT, especially the finite-product quotient argument and image
of the tensor product. No mathematical statement fault found.

The previous BLOCKED ending described an already-accepted stage-1 split. The
current queue marks this item stage 2, the node has no lean or reviewed_lean,
and its reviewed record concerns Q05's stage-1 split. This delivery preserves
that accepted split byte-for-byte outside the new lean field.

## Second reading by Q06

A separate agent was expressly forbidden by the dispatcher. I reread the node
and file in the same worker; the maintainer performs the independent review.
The family uses finite and étale, not finite type alone. Directedness and
nonemptiness are distinct conjuncts. The explicit carrier equality prevents
subalgebra closure from being mistaken for the literal union. The finite-subset
quantifier covers arbitrary finite sets and the empty set. The final source
algebra C has its own explicit universe, no Nontrivial restriction, an arbitrary
unital algebra map, an image clause, and existence and uniqueness of the
factorization through the actual inclusion. Added parentheses around the
bounded indexed union make its conjunction boundary explicit. No statement
correction or stronger assumption was introduced.
