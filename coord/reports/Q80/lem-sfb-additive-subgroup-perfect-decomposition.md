## Worker report

The module `Sheaf.AlgebraicGeometry.AdditiveSubgroupPerfectDecomposition` states
`AlgebraicGeometry.additive_subgroup_perfect_decomposition`, with one whole-proof
`sorry`. No definitions or auxiliary theorems are introduced. The node is unchanged
except for `lean`.

I read Milne, Algebraic Groups (2017), Definition 14.45 (printed p.295),
Proposition 14.52 and Corollary 14.53 (printed p.297) in the specified local PDF.
Definition 14.45 identifies closed subgroups of additive powers with elementary
unipotent groups; Proposition 14.52 gives exactly the three kinds of factors.
The full six-step accepted DAG proof, including the mixed inseparable/etale
cyclic factors, is included in the theorem docstring. The declaration names of
all statement dependencies and their actual source signatures were inspected.

Hypotheses and clauses, in node order:

- Field k: `{k : Type u} [Field k]`. The universe `u` is explicit and arbitrary.
- Positive characteristic p: `(p : ℕ) [CharP k p] (hp : 0 < p)`.
  Primality follows from being the positive characteristic of a field, so no
  additional prime hypothesis is imposed.
- Every field element is a p-th power:
  `(hperfect : ∀ x : k, ∃ y : k, y ^ p = x)`.
- Nonnegative n: `(n : ℕ)`, including zero.
- H is a k-group scheme: `(H : Grp (Over (Spec (.of k))))`. Bundling records
  precisely the `GrpObj` structure required by the dependency.
- The closed subgroup inclusion into Ga^n is
  `(i : H ⟶ ∏ᶜ fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.additive k))`
  with `[IsClosedSubgroupScheme i.hom.hom]`. The underlying map is a group
  homomorphism, a closed immersion, and injective on every algebra's points,
  using the recorded upstream definition. Products in `Grp` have the
  coordinatewise group law and are created by the forgetful functor.
- Finite type over k:
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, exactly the two
  conditions in the finite-type dependency's record.
- Nonnegative d, s, a and positive r_j:
  `∃ (d s a : ℕ) (r : Fin s → ℕ), (∀ j : Fin s, 1 ≤ r j) ∧ ...`.
- The factors alpha_(p^r_j) are expressed by group schemes `A : Fin s → Grp ...`,
  each with an underlying k-scheme isomorphism
  `e : (A j).X ≅ StandardGroupSchemes.alpha k (p ^ r j)` and
  `IsMonHom (e.hom ≫ StandardGroupSchemes.alphaInclusion k (p ^ r j))`.
  The existing `alpha k m` is literally affine Spec of
  `Polynomial k ⧸ Ideal.span {Polynomial.X ^ m}` for every natural m.
  The existing `alphaInclusion k m` is Spec of its quotient map.
  Thus these are the exact specified quotient schemes, and requiring the
  inclusion to be a group homomorphism fixes their law to addition inherited
  from Ga. Since this inclusion is a monomorphism, it uniquely determines
  multiplication, identity and inverse: the coordinate maps are respectively
  t ↦ t⊗1+1⊗t, t ↦ 0 and t ↦ -t. Consequently their points on every
  commutative k-algebra R are exactly `{x : R | x^(p^r_j) = 0}` with addition.
  This is a presentation of the specified factors by underlying-scheme
  isomorphisms, not a hypothesis of an unspecified group structure. No
  independently missing notion or new definition is needed. In particular,
  the characteristic-p instance `alphaGroup k p` is not incorrectly applied
  with characteristic p^r when r > 1.
- The group E is bundled as `E : Grp (Over (Spec (.of k)))`, with
  `IsCommMonObj E.X ∧ IsFinite E.X.hom ∧ Etale E.X.hom`.
- Its exact coordinate-ring rank is `E.X.hom.finrankΓ = p ^ a`.
  The upstream `finrankΓ` uses the k-algebra on global sections induced by
  the structure map; this includes scheme-theoretic nilpotent multiplicity.
- The final conclusion is `Nonempty (H ≅ ((∏ᶜ ...Ga...) ⨯ (∏ᶜ ...A...)) ⨯ E)`.
  This is an isomorphism in the category of k-group schemes, so it respects
  the base and the group law. Replacing each A by its displayed alpha
  presentation is exactly the product isomorphism in the node. `Nonempty`
  expresses existence of an isomorphism, with no canonical map prescribed.
- Empty products are Mathlib's categorical terminal group. No smoothness,
  connectedness, algebraic closure or commutativity of H is assumed.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`, `IsMonHom`;
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mon`: `IsCommMonObj`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (and its subgroup and
  group-homomorphism parent classes).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.additive`, `additiveGroup`, `alpha`, `alphaIdeal`,
  `alphaAlgebra`, `alphaInclusion`, `alphaQuotient`, `affine`, `map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.finrankΓ`, via the recorded group-scheme dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`;
  `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`;
  `Mathlib.Algebra.Algebra.Hom`: `AlgHom`;
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: quotient algebras and `mkₐ`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits`: limits of group
  objects, created by `Grp.forget`; the finite products in the statement.

The plain proof imports cover recorded proof dependencies already stated:
`Mathlib.RingTheory.AdjoinRoot` (`AdjoinRoot.powerBasis'`),
`Mathlib.AlgebraicGeometry.Pullbacks` (`pullbackSpecIso`), and
`Mathlib.Topology.Connected.Basic` (`ConnectedSpace`). The etale base-change
and composition lemmas come from the public Etale import. The primitive
Frobenius duality, perfect skew cyclic decomposition, and finite commutative
reduced splitting proof nodes have no Lean records in the read repository;
there are therefore no recorded modules to import for these proof-only inputs.
No statement prerequisite is missing, and no dependency record is repaired.

Edge cases checked mathematically:

- n = 0 and H trivial: d = s = a = 0, E terminal, both products empty.
- H = Ga^n: d = n, s = a = 0, E terminal.
- H = alpha_(p^2), embedded in Ga: d = a = 0, s = 1, r_0 = 2;
  no false characteristic-p^2 assumption is introduced.
- H a separable additive-polynomial kernel: d = s = 0, E = H.
- Mixed kernel t^(p^2)-t^p: one alpha_p factor and an etale factor of
  rank p; nonreduced input is allowed.
- E may be a nonconstant finite etale k-group scheme: no rational-point or
  constant-group condition is imposed. Empty finite factors give rank p^0 = 1.

Searches for an existing statement or notion:

- `msearch.py` LeanFinder, query "Closed subgroup schemes of additive group
  powers over perfect fields decompose into additive Frobenius kernels and
  finite etale groups": eight hits, including `PerfectClosure`,
  `bijective_iterateFrobenius`, `IsPerfectClosure`, and
  `FiniteField.frobeniusAlgEquiv`; none is the group-scheme classification.
- `msearch.py` Loogle, query
  `CategoryTheory.GrpObj, AlgebraicGeometry.additiveGroup`: zero hits; the
  latter expected identifier was unknown. This failed name query is not
  evidence of absence; the actual group-scheme declarations were found by
  source search and reused.
- `msearch.py` grep, query `alphaP|alpha_p|frobeniusKernel|additiveGroup` in
  Mathlib/AlgebraicGeometry: zero hits.
- `msearch.py` LeanSearch, query "Closed subgroup schemes of additive groups
  over perfect fields product classification": eight hits on abstract or
  topological `ClosedAddSubgroup`, `ClosedSubgroup`, `AddSubgroup` and their
  constructors and products. None states a scheme-theoretic decomposition.
- `rg` in the project's `WeilConjectures` and `Sheaf` found the upstream
  subgroup definitions and existing `StandardGroupSchemes` quotient schemes,
  inclusions and Frobenius. Their source definitions were read in full.
  The higher exponent underlying quotient is already covered by `alpha k m`.
- Exact item-id grep in `WeilConjectures` returned no existing statement.
  Grep for the proposed declaration name in Mathlib, `WeilConjectures`,
  `Sheaf`, and the upstream names index found no clash. A parsed DAG
  title search for additive groups and Frobenius kernels found the current
  item and `def-sc-gm-ga`, not an additional definition node to reuse.

No statement correction, disputed statement, new node, hollow definition,
private notation or auto-bound variable is used. Initial server `scompile.py`
passed both its sandbox and library module checks with no errors or warnings.

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
