## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedGroupSpaceGeometricScheme` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_over_algebraicClosure_of_separated`.
Its only theorem has proof `sorry`; there are no new definitions. The reviewed
stage-1 statement, split and dependency lists are preserved. The earlier worker's
stage-1 live-wins refusal does not apply: `coord/brief-stage2.md` section 0 explicitly
permits this handoff, the current queue lists stage 2, and the item has no Lean record.
The retained sandbox contained only brief markers, so there was no interrupted
compile or delivery to repeat. No released repair note exists for this item.

Source read: `literature/stacks-project/spaces-more-groupoids.tex`, Tag 0B8E,
`lemma-group-space-scheme-over-kbar`, including its complete proof. The source assumes
separatedness and no finite-type condition, exactly as the DAG statement does.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field `k` is `{k : Type u} [Field k]`.
- Its chosen algebraic closure is `(Ω : Type u) [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]`. This allows any chosen algebraic closure, including the
  canonical `AlgebraicClosure k`; it does not replace it with an arbitrary
  algebraically closed extension. `IsAlgClosure` supplies algebraic closedness and
  algebraicity, and the field algebra map is the specified embedding.
- The algebraic space over `Spec k` is `(G : AlgebraicSpace (Spec (.of k)))`.
  This is the recorded fppf-sheaf full subcategory, with representable diagonal and
  a representable surjective etale scheme atlas, not a scheme assumed in advance.
- Multiplication, identity, inverse and their laws on every scheme test are
  encoded by `(F : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u})` and the natural
  isomorphism `(e : F ⋙ forget GrpCat ≅ G.obj.obj)`. Each value is a group and each
  restriction is a group homomorphism. Transport along `e` therefore gives exactly
  the natural operations on the specified sheaf, with all group identities. This
  is also the encoding already used by the landed consumer
  `Sheaf.AlgebraicGeometry.LocallySeparatedGroupSpaceScheme`.
- The separatedness hypothesis is `hsep : IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left)
  (prod.lift (𝟙 G.obj.obj) (𝟙 G.obj.obj))`. The presheaves live on `Over (Spec k)`,
  so this product is the relative product over `k`, and `prod.lift` is its diagonal.
  `IsRepresentableWith` quantifies over every scheme test and requires the
  representing projection to be a closed immersion, exactly as stated in the node.
- The base-changed sheaf is expressed by its functor of points on the new base:
  `(Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).op` followed by
  `G.obj.obj` (the Lean file contains the properly parenthesized expression).
  A test object `T → Spec Ω` already supplies the second coordinate of a section
  of `G ×_(Spec k) Spec Ω`. The remaining datum is precisely a section of `G` on
  `T → Spec Ω → Spec k`. Restriction along `Over.map` therefore expresses the
  actual sheaf fibre product, including its restriction maps. It is not an
  arbitrary comparison map or an assumed base-change object.
- Being represented by an Ω-scheme is `∃ X : Over (Spec (.of Ω)), Nonempty
  ((the restricted presheaf) ≅ yoneda.obj X)`. The representing object includes
  its structure morphism to `Spec Ω`, and the isomorphism is natural on all tests.
  This conclusion does not assert extra finiteness or a chosen presentation.
- Sheaf fibre products being computed on tests and agreeing with scheme fibre
  products is used through this functor-of-points expression and the recorded
  algebraic-space fibre-product module. It is an explanation of the same object,
  not an additional hypothesis. No finite-type hypothesis occurs anywhere.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, from `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: `IsAlgClosure`, `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, and `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`. The latter module is public.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`; their definitions were read in full.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`, from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections and
  universal property, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `lem-trf-space-fibre-products-etale-covers`: `fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, and `etale_fibreProduct_isScheme` in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`; all signatures
  and their docstrings were read. This module is publicly imported.
- Already stated proof dependencies have plain imports:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage` and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`. Their point-open
  correspondence and `OpenSubspace` definitions were read. The other mathematical
  proof dependencies have no recorded declarations yet; the theorem docstring
  retains the full six-step DAG argument and names each of them.
- Existing Mathlib `GrpCat`, its forgetful functor, `Over.map` and Yoneda supply
  the group functor and the base-change/representability expressions. No second
  definition of a group algebraic space or of base change is introduced.

Edge cases checked before writing: the trivial group is included; noncommutative
groups are included; arbitrary characteristic, nonreduced groups and groups without
any finite-type or quasi-compactness condition are included. An empty algebraic
space cannot satisfy the group-functor hypothesis, because the identity is present
on every test, including the base field. When `k` is already algebraically closed,
the identity extension is covered. All schemes, field extensions and presheaf
values use the existing algebraic-space framework's universe `u`; algebraic
closures exist in that same universe. There is no independently smaller test
universe or added universe equality. The translation in the proof has inverse
`h ↦ g' g⁻¹ h`, so its use does not require commutativity. The atlas-complement
argument uses the Jacobson hypothesis on the large extension, not an unstated
finite-type assumption.

Searches made with the prescribed `msearch.py` wrapper:

- LeanFinder: “A separated group algebraic space over a field is represented by
  a scheme after algebraic closure”; eight hits, all scheme separatedness or
  scheme properties, no theorem for algebraic spaces.
- LeanSearch: “A separated group algebraic space becomes a scheme after extension
  to an algebraic closure”; eight scheme-separatedness hits, no match.
- Loogle: `GrpObj` and `AlgebraicGeometry.AlgebraicSpace`; both returned zero hits
  with unknown-identifier diagnostics in the search index. Direct source searches
  found the existing project algebraic-space definition and Mathlib group APIs.
- Mathlib grep: `GroupAlgebraicSpace|group_space|scheme_over_kbar`, restricted to
  `AlgebraicGeometry`; zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `scheme_over_algebraicClosure`, `group_space` and `groupSpace`: the consumer's
  proof docstring mentions this item, but no existing theorem states it. Additional
  searches for `GrpObj`, group algebraic spaces and representability found the
  consumer's group-valued functor interface, which is reused here.

No statement correction, disputed statement, new node or dependency repair is
needed. The module compiled cleanly through `scompile.py` against the published
server library, both as the sandbox module and under its final module name.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
