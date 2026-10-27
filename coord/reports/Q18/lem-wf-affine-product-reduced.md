## Worker report

The module `Sheaf.AlgebraicGeometry.AffineProductReduced` states the whole node as
`AlgebraicGeometry.affine_product_reduced`, with `sorry` as its only proof. No definitions,
new nodes, dependency repairs, or statement corrections are needed. The latest blueprint
is `literature/blueprint/latest/blueprint/sec-algebraic-groups-lie-algebras/sk-i-cartier/lem-wf-affine-product-reduced.md`
and its `.proof.md`; their statements agree verbatim with the DAG statement.

Hypotheses and clauses:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- The affine varieties are represented by their coordinate rings `(A B : Type u)` with
  `[CommRing A] [CommRing B] [Algebra k A] [Algebra k B]`, as the source proof does.
- Finite generation of both coordinate rings: `[Algebra.FiniteType k A]` and
  `[Algebra.FiniteType k B]`. This is the algebra-instance form of the recorded
  `RingHom.FiniteType (algebraMap k A)` (respectively B), equivalent by
  `RingHom.finiteType_algebraMap`; it uses the same existing finite-type notion.
- Reducedness of both rings: `[_root_.IsReduced A] [_root_.IsReduced B]`.
- The tensor algebra is reduced: first conjunct `_root_.IsReduced (A ⊗[k] B)`.
- It is finitely generated: second conjunct `Algebra.FiniteType k (A ⊗[k] B)`.
- The product is the affine spectrum of the tensor algebra: the third conjunct is
  `IsPullback` for the two `Spec.map` tensor inclusions and the two structure maps to
  `Spec k`. This states the actual product universal property with its canonical
  projections; its top-left object is definitionally `Spec (.of (A ⊗[k] B))`.
  Together with the first two conjuncts, this says precisely that this product is an
  affine variety in the source's sense (reduced finite-type affine scheme, allowing
  disconnected and empty varieties).
- Its k-points are exactly pairs: `Function.Bijective` for the canonical function
  `(x,y) ↦ Algebra.TensorProduct.productMap x y` from pairs of algebra homomorphisms to
  algebra homomorphisms out of the tensor algebra. The existing definition satisfies
  `productMap x y (a ⊗ₜ b) = x a * y b`; its restrictions are `x` and `y`.
  The affine-spectrum correspondence identifies these algebra homomorphisms with
  scheme morphisms from `Spec k` over `Spec k`, as in the source.
- The vanishing principle: the next conjunct quantifies every `t : A ⊗[k] B` and says
  `(∀ x y, productMap x y t = 0) → t = 0`.
- Equality of regular maps: the last conjunct quantifies an arbitrary affine variety
  with coordinate algebra `C : Type v`, reduced, commutative, and finite type over k,
  and two coordinate maps `f g : C →ₐ[k] A ⊗[k] B`. Equality of all composed point maps
  `(productMap x y).comp f = (productMap x y).comp g` implies `f = g`. By `Spec.homEquiv`
  this is precisely equality of the corresponding regular maps. The nested `∀ x y`
  renders checking one variable at a time. Affineness of the target is explicit in
  the source proof's final paragraph. There is no separatedness or irreducibility
  assumption added.

Dependency declarations read and used:

- `lem-wf-affine-nullstellensatz-vanishing`: upstream module
  `WeilConjectures.Mathlib.RingTheory.Nullstellensatz`, declarations
  `exists_algHom_ker_eq_of_isMaximal`, `eq_zero_of_forall_algHom_apply_eq_zero`, and
  `existsUnique_comp_mkₐ_eq_of_forall_algHom`. The node's short `lean` record omits a
  module, but its closed `lean_audit.slopmaster2.decls` gives this exact module.
  The theorem docstring follows its vanishing principle separately in the two factors.
- `def-weil-pbc-finite-type-algebra`: `Mathlib.RingTheory.FiniteType`,
  `RingHom.FiniteType`, `Algebra.FiniteType`, and `RingHom.finiteType_algebraMap`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; canonical `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`; the additional linear tensor-map clauses
  use `LinearMap.rTensor`, `rTensorHom`, `rTensor_tmul`, `rTensor_comp`, `rTensor_id` in
  `Mathlib.LinearAlgebra.TensorProduct.Map`. These existing constructions underlie
  the imported algebra tensor product; none are copied.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Mathlib.RingTheory.TensorProduct.Basic`, `Algebra.TensorProduct.instCommRing`,
  `tmul_mul_tmul`, `includeLeft`, `includeRight`, `ext`; and
  `Mathlib.RingTheory.TensorProduct.Maps`, `Algebra.TensorProduct.productMap`,
  `productMap_apply_tmul`, `productMap_left`, `productMap_right`.
- `lem-weil-pbc-fibre-product-affine-spectra`: `Mathlib.AlgebraicGeometry.Pullbacks`,
  `AlgebraicGeometry.pullbackSpecIso`, `pullbackSpecIso_inv_fst`,
  `pullbackSpecIso_inv_snd`. This existing isomorphism proves the displayed cartesian
  square; the statement imports this exact dependency module publicly.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`; `Spec.homEquiv` in
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` gives the coordinate-map reading.
- The proof-only basis dependency `lem-weil-pbc-vector-space-basis-through-vector`
  is imported without `public`: `Mathlib.LinearAlgebra.Basis.VectorSpace`,
  `Module.Basis.extend`, `coe_extend`, `subset_extend`, `exists_basis`.

The module docstring and theorem docstring describe the same affine coordinate-ring
interpretation; the latter includes all six steps of the accepted DAG proof. Every
variable and universe is explicitly bound. A common ambient universe for k, A and B
permits Mathlib's scheme product; C has an independent universe v. No rational-point
test is confined to a smaller unrelated universe.

Edge cases checked before writing:

- A zero coordinate algebra is allowed: there is no `Nontrivial A` or `Nontrivial B`.
  Its variety is empty, the tensor algebra is zero, both point sets are empty, the
  vanishing implication is valid, and maps into the zero coordinate algebra are unique.
- A zero target algebra is allowed too. Its map type into a nonzero tensor algebra
  can be empty; the map-equality implication is still correctly quantified.
- Empty generating sets (A = k or B = k), disconnected reduced algebras such as finite
  products of k, polynomial algebras of positive dimension, and every characteristic
  are included. Neither coordinate ring is assumed finite-dimensional or a domain.
- The reducedness hypothesis matters: dual numbers contain a nonzero function
  vanishing at every rational point. Over an imperfect field an inseparable field
  extension tensored with itself need not be reduced. The statement retains both
  reducedness assumptions and algebraic closedness.

Searches for an exact existing statement (outputs also in `searches.jsonl`):

- `msearch.py ... leanfinder`: "Tensor product of reduced finitely generated algebras
  over an algebraically closed field is reduced and its rational points are pairs,
  detecting equality of regular maps". Eight results concern geometric reducedness
  and tensor products with fields; none gives the whole item.
- `msearch.py ... loogle "TensorProduct, IsReduced"`: six results about geometric
  reducedness and flat filtered reduction; no whole-item statement.
- `msearch.py ... leansearch`: "Products of reduced affine varieties over an
  algebraically closed field are reduced and morphisms are determined by pairs of
  rational points". Eight results concern geometric reducedness and affine reducedness;
  no whole-item match.
- `msearch.py ... grep` in RingTheory for
  `isReduced_tensorProduct|eq_zero_of_forall.*(tensor|Tensor)|productMap.*[Bb]ijective|[Ff]initeType.*tensorProduct`:
  four finite-type descent hits, no whole-item match.
- `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for the node id,
  `isReduced_tensorProduct`, `eq_zero_of_forall_algHom`, `affineProductReduced`, and
  `affine_product_reduced`: upstream Nullstellensatz contains
  `Algebra.TensorProduct.eq_zero_of_forall_lift_algHom_eq_zero`, and upstream
  `WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced` contains
  `isReduced_tensorProduct_of_perfectField`. Read their full signatures/docstrings.
  They give only the product-vanishing and reducedness clauses respectively. The
  whole node additionally asserts finite generation, the affine product, point
  correspondence, and equality of regular maps. This delivery states the complete
  conjunction, without redeclaring either existing component theorem or any notion.
  Name checks for `affine_product_reduced`, `affineProductReduced`, and
  `affine_product_properties` found no declaration collision.

Validation: the prescribed `scompile.py Q18 lem-wf-affine-product-reduced` compiled
the delivered module successfully against the live server library, with no errors
or warnings.

No statement dispute or mathematical node fault found. The provided CompactObject
example in `Sheaf` has been withdrawn; read the surviving upstream
`WeilConjectures.CategoryTheory.CompactObject` as the module-header example instead.

## Second reading by Q18

Clause-by-clause reading of `AlgebraicGeometry.affine_product_reduced` against the node
statement and the source (blueprint `lem-wf-affine-product-reduced`, order 2488, and its
proof), done by the maintainer's second reader (cc review, 2026-10-24). It replaces the earlier
placeholder that only noted the dispatcher's direct-delivery policy.

Objects and hypotheses:
- $k$ algebraically closed: `(k : Type u) [Field k] [IsAlgClosed k]`. Correct.
- Affine varieties $X,Y$ given by reduced finitely generated coordinate algebras $A,B$:
  `[CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [Algebra.FiniteType k A]
  [Algebra.FiniteType k B] [IsReduced A] [IsReduced B]`. `Algebra.FiniteType` is the same
  notion as the recorded `RingHom.FiniteType (algebraMap k A)` (`RingHom.finiteType_algebraMap`).
  There is no `Nontrivial`, domain, or finite-dimensionality assumption. Correct.
- The common universe `u` for k, A and B is the one Mathlib's `Scheme.{u}` pullback needs. It
  loses no finite-type case, because a finite type k-algebra is a quotient of
  `MvPolynomial (Fin n) k : Type u`.

Conclusion:
- $A\otimes_kB$ reduced: `IsReduced (A ⊗[k] B)`. Correct.
- Finitely generated: `Algebra.FiniteType k (A ⊗[k] B)`. Correct.
- $X\times Y=\operatorname{Spec}(A\otimes_kB)$: `IsPullback` of `Spec.map includeLeft`,
  `Spec.map includeRight` over `Spec.map (algebraMap k A)`, `Spec.map (algebraMap k B)`. The
  orientation is right (fst : Spec(A⊗B) → Spec A, f : Spec A → Spec k), the square commutes
  because both composites are the map induced by `algebraMap k (A ⊗[k] B)`, and the statement
  holds by `pullbackSpecIso` (lem-weil-pbc-fibre-product-affine-spectra). Correct.
- $k$-points are the pairs: `Function.Bijective (fun xy ↦ productMap xy.1 xy.2)`. This is true:
  `productMap_left` and `productMap_right` give injectivity, and `Algebra.TensorProduct.ext`
  gives surjectivity. Combined with `Spec.homEquiv` and the cartesian square, it is the node's
  identification of $k$-points. Correct.
- Vanishing principle on $X\times Y$: `∀ t, (∀ x y, productMap x y t = 0) → t = 0`. Correct.
  The component theorem `Algebra.TensorProduct.eq_zero_of_forall_lift_algHom_eq_zero` exists
  upstream and is not redeclared.
- Identities between regular maps checked on points, one variable at a time: for any affine
  variety `Spec C` (`C : Type v`, finite type and reduced) and `f g : C →ₐ[k] A ⊗[k] B`,
  agreement of `(productMap x y).comp f` and `(productMap x y).comp g` for all `x` and `y`
  implies `f = g`. This is the node's proof step 6, with the target affine. The nested `∀ x y`
  renders "one variable at a time". Correct.

Edge cases: a zero A or B (empty variety) is covered, and every clause stays true. A = k, all
characteristics, and disconnected or positive-dimensional factors are covered. C is in an
independent universe v.

Searches: Mathlib `IsGeometricallyReduced`, `isReduced_tensorProduct*`, `productMap`, and
`liftEquiv`; upstream `Nullstellensatz.lean` and `GeometricallyReduced`. These give component
facts only, not the whole node. No H4 duplicate.

Records: `lean.statement` is verbatim equal to the file signature. Only the `lean` field of the
node changed relative to live. The docstrings carry the source place, `(blueprint: …)` and the
six proof steps. The proof is `sorry`. No definitions were introduced.

Advisory: the module docstring names the blueprint path `sk-i-cartier/` (latest blueprint), while
the node source names `sk-i-geometry/` (master). The node id is identical, so this is not a
fault.
