## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.PerfectFiniteCommutativeReducedSplitting`
states `AlgebraicGeometry.GrpObj.perfect_finite_commutative_reduced_splitting`.
Its only theorem has proof `sorry`; it defines no new objects or notions.
Only the item's `lean` field changes. There is no statement correction or dispute.

Hypotheses and clauses, checked against the node and Milne, Algebraic Groups (2017),
Proposition 11.3, printed p.210, and Proposition 2.37, printed pp.51-52:

- Field: `(k : Type u) [Field k]`.
- Positive characteristic: `(p : ℕ) [CharP k p] (hp : 0 < p)`.
  No primality hypothesis is added: characteristic of a field, when positive, is prime.
- Every element is a p-th power: `hperfect : ∀ a : k, ∃ b : k, b ^ p = a`.
  This is the node's exact hypothesis, rather than an assumed algebraic closure.
- A k-group scheme: `G : Over (Spec (.of k))` with `[GrpObj G]`.
- Commutativity: `[IsCommMonObj G]`, the multiplication/swap condition.
- Finiteness: `[IsFinite G.hom]`, the finite structure morphism. No reducedness,
  smoothness, connectedness, constantness, or algebraic closedness hypothesis is added.
- The identity component: `GrpObj.identityComponent G` and its canonical inclusion
  `GrpObj.identityComponentι G`, from the upstream Basic module. Its definition is
  `Over.mk ((GrpObj.identityComponentOpens G).ι ≫ G.hom)`, where the open set is
  exactly `connectedComponent (GrpObj.onePoint G)`. Thus it has the full open
  subscheme structure, including nilpotents; it is not the reduced induced subscheme.
  Finiteness supplies the finite-type instances needed by this existing interface.
- That identity component is a closed subgroup: the first conjunct is
  `IsClosedSubgroupScheme (GrpObj.identityComponentι G)`. Together with the
  existing open immersion, this gives the required open-and-closed subscheme.
- The reduction: the actual scheme `G.left.nilradical.subscheme`, with canonical
  inclusion `G.left.nilradical.subschemeι`, equipped with its composite structure
  morphism to Spec k. Thus the object used throughout is exactly
  `Over.mk (G.left.nilradical.subschemeι ≫ G.hom)`. The Mathlib nilradical subscheme
  uses the radical of the zero ideal on affine charts, so for G = Spec B this
  is Spec(B / sqrt(0)). No new definition of reduction or algebra quotient is made.
- The reduction carries a group structure and is a closed subgroup: the existential
  `∃ (_ : GrpObj (Over.mk (G.left.nilradical.subschemeι ≫ G.hom))), ...`
  is followed by `IsClosedSubgroupScheme` of its actual inclusion `Over.homMk
  G.left.nilradical.subschemeι`. The inclusion being a homomorphism fixes the
  group law as the restriction of G's law; it cannot introduce an unrelated law.
- The reduced factor is finite etale: the next two conjuncts are `IsFinite` and
  `Etale` of `G.left.nilradical.subschemeι ≫ G.hom`.
- Multiplication induces the specified isomorphism: the final two conjuncts are
  `IsMonHom` and `IsIso` of the same explicit morphism
  `((GrpObj.identityComponentι G ⊗ₘ (Over.homMk ...)) ≫ μ[G])`.
  The tensor in the cartesian monoidal category Over(Spec k) is the fibre product
  over k. Hence this is multiplication of the two canonical inclusions, not an
  unspecified isomorphism. `IsIso` is in Over(Spec k); `IsMonHom` says that this
  is an isomorphism of group schemes. The inverse is a homomorphism by the existing
  Mathlib instance for the inverse of a monoid-homomorphism isomorphism
  (`Mathlib.CategoryTheory.Monoidal.Mon`, near line 236).
- The last sentence of the node is respected: no constant-group-scheme condition
  appears anywhere, and the splitting is over k itself, not merely over its closure.

Statement-dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` (inverse plus the monoid laws),
  `CategoryTheory.IsCommMonObj` and `CategoryTheory.IsMonHom`, in
  `Mathlib.CategoryTheory.Monoidal.Grp` / `.Mon`. The recorded upstream explanation
  and subgroup interfaces are in `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, inherited publicly through Defs.
  The integral alternative is not used by this finite-only statement.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`; the component here uses its underlying
  connected-component API through upstream `GrpObj.identityComponentOpens`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`, inherited through the public imports.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom`, `Ideal.Quotient.algebra` and
  `Ideal.Quotient.mkₐ`, `Mathlib.Algebra.Algebra.Hom` and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`. The quotient is already implemented
  inside the recorded subscheme construction, so the signature does not duplicate it.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. It extends
  `IsSubgroupScheme` (which includes `IsMonHom` and injectivity on algebra points)
  and asserts that the underlying morphism is a closed immersion.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-pbc-scheme-reduction`: `Scheme.nilradical`,
  `Scheme.IdealSheafData.subscheme` and `.subschemeι`,
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` / `.Subscheme`.

Additional existing interface: `GrpObj.identityComponent` and `.identityComponentι`,
`WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`. Their definitions and inherited
`GrpObj`/`IsMonHom` instances were read in full; no private substitute is needed.
The same interface is recorded by `def-wf-algebraic-components`.

Proof imports retain all recorded, stated proof dependencies: the reduced induced
closed subscheme theorem; finite reduced perfect algebras being etale; the etale
Spec/ring criterion; the perfect reduced tensor theorem; affine fibre products;
the component functor theorem; separatedness/properness terminology; the Artinian
zero-dimensional theorem; etale geometric-point full faithfulness; and separable
closures. Statement imports are public, while proof-only imports are plain imports.
The four-step proof docstring follows all four steps of this node, including descent
from geometric points and the explicit inverse `(a,r)`.

Edge cases checked mathematically before writing:

- The trivial group Spec k: both factors are trivial and multiplication is its
  isomorphism. Its order is one; no nontriviality condition excludes it.
- A finite connected nonreduced group such as alpha_p or mu_p in characteristic p:
  the identity component retains its nilpotents, while the reduction is Spec k.
- An arbitrary finite etale commutative group: the identity component is the
  identity copy of Spec k and the reduction is the whole group. Nonconstant
  examples, such as mu_l with l prime to p over a field without all l-th roots
  of unity, are included. There is no rationality or constantness assumption.
- Products of infinitesimal and nonconstant etale factors use the actual canonical
  inclusions in the product map. No arbitrary identification can satisfy the
  conclusion in place of multiplication.
- Empty schemes cannot be group schemes over a field: the unit section rules them
  out. An empty finite factor is not incorrectly included or excluded by a binder.
- p = 0 is excluded precisely by hp; p = 1 is impossible for a field with CharP 1.
  No characteristic-zero case is silently required.
- The only universe is explicit `u`; all variables are explicit and
  `set_option autoImplicit false` is present. No undersized test-algebra quantifier
  or field-extension quantifier has been introduced.

Searches for an existing statement:

- `msearch.py ... leanfinder "A finite commutative group scheme over a perfect field
  is the product of its identity component and its reduced subgroup"`: 8 hits,
  including `PerfectRing.ofFiniteOfIsReduced`, abstract primary-component lemmas,
  and finite-field Frobenius maps; no group-scheme splitting theorem.
- `msearch.py ... loogle '"GrpObj", "IsClosedSubgroupScheme"'`: 0 hits.
- `msearch.py ... grep 'connected.etale|reduced.*subgroup|subgroup.*reduced'
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in project `lean/WeilConjectures` for this blueprint id: no declaration.
  Searches of upstream GroupScheme for identity components/reduced subgroups found
  the reusable Basic/Defs interfaces, not the requested splitting theorem.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for identity components and reduced
  subgroups found `GroupNeutralComponentTranslates`, `BoundedExponentReducedPKernel`
  and the downstream `AdditiveSubgroupPerfectDecomposition`; none states this
  splitting. The latter cites this item in its proof and has matching positive
  characteristic and p-th-power-surjectivity hypotheses.
- Exact name searches for `perfect_finite_commutative`,
  `finite_commutative_reduced`, and `perfectFiniteCommutative` in both project
  roots and `dag/lean_names_upstream.json` found no existing declaration.

Validation: `scompile.py Q46 lem-sfb-perfect-finite-commutative-reduced-splitting`
compiled this file in both sandbox and library module modes successfully, with no
compiler errors or unexpected warnings. No global or direct local build was run.

## Second reading by Q46

A separate self-review pass reread the node, the source excerpt and the complete
Lean signature; the maintainer supplies the independent review under this worker's
brief. No other agents were started. Field, characteristic, perfectness,
commutativity and finiteness match their binders exactly. The first inclusion is
upstream's open identity component and the second is the actual nilradical quotient
inclusion. Both are asserted closed subgroups; the reduced factor is finite etale.
The very same explicit multiplication morphism is both a group homomorphism and
invertible, which also makes its inverse a group homomorphism. The existential
class binder supplies precisely the subgroup law on the specified reduced scheme;
it does not quantify over a substitute scheme or map. There are no extra
hypotheses, base changes, constantness clauses, let-bound statements or new
unproved helper results. No mismatches were found, and no statement changes were made.
