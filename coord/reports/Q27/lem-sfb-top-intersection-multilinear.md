## Worker report

The module `Sheaf.AlgebraicGeometry.TopIntersectionMultilinear` states
`AlgebraicGeometry.Scheme.Modules.top_intersection_multilinear`, with a single
`sorry` and the complete five-step DAG proof in its docstring. No definitions
or proofs are added. The item's mathematical statement and proof are unchanged.
The only additional statement dependency is the already recorded
`def-sc-picard-group`, needed to express its rational-extension clause using the
existing Picard group rather than introducing another quotient.

Source read: Stacks `literature/stacks-project/varieties.tex`,
`definition-intersection-number` (0BEP), lines 10389 onward, and
`lemma-intersection-number-additive` (0BER), lines 10432 onward. The rational
extension is the explicit finite-sum construction in step 5 of this node.
Also read the current blueprint
`literature/blueprint/latest/blueprint/sec-abelian-varieties/sk-def-av-pic/def-sc-picard-group.md`,
which explicitly defines Picard groups for schemes, not only curves.

Hypotheses and conclusions, clause by clause:

- The field is `(k : Type u) [Field k]`.
- The scheme over that field is `(X : Scheme.{u}) [X.Over (Spec (.of k))]`;
  `[IsProper (X ↘ Spec (.of k))]` is properness of its structure map.
- `[Nonempty X]` is the specified nonemptiness. `(g : ℕ) (_hg : 1 ≤ g)`
  and `hd : topologicalKrullDim X = ((g : ℕ∞) : WithBot ℕ∞)` render its
  positive dimension exactly. No equidimensionality, reducedness, algebraic
  closure, or characteristic restriction is imposed.
- Each quantified family `L : Fin g → X.Modules` has the instance binder
  `[∀ j, (L j).IsInvertible]`, and likewise for comparison families `M`, `N`.
- Every intersection expression is the recorded definition
  `intersectionNumber k X X (𝟙 X) g hd L`, namely the identity closed immersion
  case, with the actual structure sheaf pushed forward by that identity.
- The first conjunct asserts equality under `∀ j, Nonempty (L j ≅ M j)`.
  These are actual module isomorphisms, not merely equality of stalk ranks.
- The second conjunct quantifies over `σ : Equiv.Perm (Fin g)` and compares
  any family `M` with `M j ≅ L (σ j)` in each entry. This is symmetry,
  expressed with a separately bound invertible family to avoid hidden
  instance proofs for reindexing.
- The third conjunct quantifies over every slot `i : Fin g`. The equalities
  `M j = L j ∧ N j = L j` for `j ≠ i` specify that precisely that slot is
  replaced. `Nonempty (L i ≅ M i ⊗ N i)` specifies the tensor product in
  the slot, and the conclusion is the sum of the two intersection numbers.
  The families introduce no restriction on the replacement modules: for any
  two invertible modules one can use their function updates in the slot.
- The fourth conjunct says a trivial entry has value zero, with triviality
  rendered by `Nonempty (L i ≅ 𝟙_ X.Modules)`. It includes any trivialization.
- The fifth conjunct specifies unchanged other entries and
  `Nonempty (M i ≅ (L i).dual)` in the chosen slot. Its value is the negative
  of the original intersection value, using the recorded module dual.
- The last conjunct constructs a `MultilinearMap ℚ` from `g` copies of
  `ℚ ⊗[ℤ] Additive X.Pic` to `ℚ`. Its first condition asserts symmetry under
  all permutations of arbitrary rationalized classes. Its second condition
  identifies its value on `1 ⊗ₜ[ℤ] Additive.ofMul (Pic.ofIsInvertible (L j))`
  with the existing intersection number for every invertible family.
  Its third condition quantifies over every rational multilinear map `G`
  with that agreement, and concludes `G = F`; uniqueness is not limited to
  maps separately assumed symmetric.

The vector space in the last clause is the requested space of rational
linear combinations of isomorphism classes modulo tensor relations:
`X.Pic` already consists of those classes; its group multiplication is
induced by tensor product. `Additive` writes that law additively, and
extension of scalars along `ℤ → ℚ` gives precisely the rational vector space
with those relations. Thus no private free-space quotient or arbitrary
canonical map is substituted. The generating map is the actual pure tensor.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`, extending `CommRing` and
  `DivisionRing` (line 180).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (line 42), separated, universally closed and locally of finite type.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` (line 39), the
  Krull dimension of irreducible closed subsets.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, with its full local
  rank-one trivialization signature; the tensor product and its instances
  are those of this module.
- `WeilConjectures.AlgebraicGeometry.Modules.Dual`: the existing `dual` and
  `IsInvertible.dual`, and the evaluation isomorphism described there.
- `Sheaf.AlgebraicGeometry.IntersectionNumber`:
  `AlgebraicGeometry.Scheme.Modules.intersectionNumber`; read its complete
  signature, integer-power polynomial construction and identity-case docstring.
- Added dependency `def-sc-picard-group`:
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`,
  `AlgebraicGeometry.Scheme.Pic`, with `val`, `mk` and equality iff isomorphism;
  its recorded audit also names the group structure in
  `WeilConjectures.AlgebraicGeometry.Picard.Group`. Read `Pic.ofIsInvertible`,
  `mul_def`, `inv_def`, `one_def` and `Pic.instCommGroup` there. They use the
  scheme-module invertibility predicate and the existing tensor and dual.
- Proof imports retain the recorded Snapper theorem
  `exists_mvPolynomial_eulerChar_tensorPowers`, the recorded
  `eulerChar` from `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  the invertible-module module and
  `Polynomial.eq_of_infinite_eval_eq` from `Mathlib.Algebra.Polynomial.Roots`.
  The direct statement import also exposes Snapper and module duality.
- `Mathlib.LinearAlgebra.TensorProduct.Basic` and
  `Mathlib.LinearAlgebra.Multilinear.Basic` supply the existing tensor
  product, scalar extension and multilinear-map structures.

Edge cases checked before writing: `g = 1` gives a single additive map and
no other-entry conditions; `g = 0` is expressly excluded by the node.
The empty scheme is expressly excluded. Nonreduced and reducible proper
schemes remain included; the proof uses the structure sheaf and support,
not smoothness or purity. Trivial and dual entries give the asserted zero
and sign; torsion Picard classes vanish after rationalization, consistently
with tensor-additivity. All characteristics are included. The Picard group
lives in `Type (u + 1)`, and the tensor and multilinear-map types retain that
universe without shrinking or equating universes.

Searches actually run with `msearch.py Q27 lem-sfb-top-intersection-multilinear`:

- `leanfinder`: "Top intersection numbers of invertible sheaves are symmetric,
  additive under tensor product, and extend uniquely to a rational multilinear
  pairing". Eight hits including `CommRing.Pic.mk_tensor`,
  `CommRing.Pic.mul_eq_tensor` and unrelated root pairings and Proj results;
  none states the scheme intersection theorem.
- `loogle`: `MultilinearMap, ModuleCat, PicardGroup`. Reported zero hits with
  `unknown identifier 'PicardGroup'`; this query did not establish absence.
- `loogle`: `MultilinearMap.domDomCongr`. Twelve hits describing reindexing
  multilinear maps and alternatization; useful API, no intersection theorem.
- `grep` of Mathlib `AlgebraicGeometry`:
  `intersectionNumber|intersection_number|Picard`. Three incidental Picard
  mentions in elliptic-curve documentation, no intersection-number declaration.
- `leansearch`: "Intersection numbers of invertible sheaves are additive under
  tensor product and symmetric". Eight hits: additive module pullback,
  ring-module invertibility, bilinear tensor symmetry, tensor relations and
  set intersection; none states this scheme intersection result.
- `rg` in both `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for
  `intersectionNumber|intersection_number|top_intersection_multilinear|rationalPicard`:
  the recorded intersection definition and positivity, reduction and Cartier
  formulas, but no multilinearity or rational-extension theorem.
- `rg` for the item's id throughout `lean/WeilConjectures`: no hits.
  The upstream declaration index also has no matching intersection theorem.
- Search for rationalized Picard constructions using
  `ℚ.*⊗\[ℤ\].*Pic|Pic.*⊗\[ℤ\]|rationalPicard|RationalPic` in
  `lean/Sheaf`, `lean/WeilConjectures` and `dag/nodes`: no hits.
  Existing Picard definitions were read and reused directly; no additional
  notion or definition node is required for the inline tensor-product type.

No statement dispute or node correction is needed. There are no new nodes
and no dependency-record repairs.

## Second reading by Q27

This is a second pass by the worker; the maintainer performs the independent
review required by the dispatcher. Reopened the node and the complete final
Lean signature and checked all six conjuncts. The structure map, properness,
nonemptiness, positive dimension and each family's invertibility match the
node. The identity closed immersion agrees with the top-intersection case.
The equality conditions away from a selected slot merely specify the entry
replacement; they impose no additional scheme or line-bundle hypothesis.
The symmetry clause allows every permutation and entrywise isomorphisms.
The trivial entry uses an isomorphism to the tensor unit, and the dual entry
uses the existing sheaf dual. The rational extension uses all Picard classes,
not numerical-equivalence classes, and its uniqueness condition covers all
extensions, even without a symmetry hypothesis on the competing map.
No mismatch was found and no mathematical statement was changed.
