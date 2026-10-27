## Worker report

The module `Sheaf.RingTheory.DirectedTensorLeastSupportStabilization` states
`Module.directed_tensor_least_support_stabilization`, with `sorry` as its entire proof.
It introduces no definitions, additional nodes, or dependency repairs. The item's
statement, statement dependencies, proof, and proof dependencies are unchanged.

Read the node and both statement dependencies, their recorded Mathlib declarations,
and both additional proof dependencies. Read Stacks Project `algebra.tex`,
Tag 059S (`lemma-flat-ML-criterion`), in particular its commutative square and final
paragraph. The theorem follows the node's image-based generalization of that argument:
no tensor product with a submodule is treated as a submodule without taking its image.
Its docstring carries all four proof steps and their dependency ids.

Hypothesis and clause correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`; the arbitrary coefficient
  module is `{H : Type w} [AddCommGroup H] [Module R H]`.
- The small nonempty directed partially ordered index set is
  `{I : Type v} [PartialOrder I] [Nonempty I] [IsDirectedOrder I]`.
  Mathlib's preorder-category instance supplies the arrows `homOfLE hk`.
  The ring, module, and index universes are all explicitly bound. The diagram's
  modules have universe `v`, matching the index universe and the project's
  filtered-module-colimit size convention. Arbitrarily large choices of `v` and
  `w` are allowed; there is no countability or cardinal-finiteness constraint.
- The directed system is `(F : I ⥤ ModuleCat.{v} R)`. Its transition map
  `mu_kl` is `(F.map (homOfLE hkl)).hom`, with identity and composition laws
  supplied by the functor. Its given colimit is `(c : Cocone F) (hc : IsColimit c)`:
  `c.pt` is `N`, and `(c.ι.app k).hom` is `mu_k`. This accepts any colimit
  cocone, rather than specifying a particular construction of the colimit.
- The chosen initial stage and tensor are `(i : I)` and
  `(xi : TensorProduct R H (F.obj i))`.
- At a stage `k` with `hk : i ≤ k`, the displayed term
  `LinearMap.lTensor H (F.map (homOfLE hk)).hom xi` is precisely `x_k`.
  The term `LinearMap.lTensor H (c.ι.app i).hom xi` is `x` in the colimit.
- The inclusion-induced map for `G` and a module `L` is
  `LinearMap.rTensor L G.subtype`. Membership in its `LinearMap.range` is
  exactly membership in the image, whether or not this map is injective.
- `Q : Submodule R H` and `hQ : IsLeast {G | ...} Q` say both that `Q`
  supports `x` and that `Q` is contained in every supporting submodule.
  Mathlib's `IsLeast` is membership together with the lower-bound condition.
- `(C : ∀ k : I, i ≤ k → Submodule R H)` only specifies stage supports
  above `i`; it requires no choices below `i`. `hC` is the corresponding
  `IsLeast` assertion for each `x_k`. Dependence on the inequality proof is
  harmless by proof irrelevance.
- The first conjunct, `∀ k hk, Q ≤ C k hk`, is containment of the colimit's
  least support in every stage support above `i`.
- The second conjunct, `∀ k l hk hkl, C l (hk.trans hkl) ≤ C k hk`, is
  decreasingness whenever `l ≥ k ≥ i`.
- The final conjunct binds `∃ j hj t`, where `hj : i ≤ j` and
  `t : TensorProduct R Q (F.obj j)`. Its first clause is the required equality
  between the image of `t` under the tensor inclusion and `x_j`.
- Its last clause, `∀ k hk, C k (hj.trans hk) = Q`, asserts equality at every
  stage `k ≥ j`, including `j` itself. The witness and stabilization share
  the same `j`, as required.
- There are no hypotheses of injective transitions, flatness, finite generation
  of `Q`, finite freeness of the stages, or countability of `I`.

Dependency declarations used:

- `def-weil-pbc-category-colimit`: the recorded Mathlib interface is
  `CategoryTheory.Limits.Cocone` and `CategoryTheory.Limits.IsColimit`, available
  through public import `Mathlib.CategoryTheory.Limits.HasLimits` (their source
  definitions are in `Limits.Cones` and `Limits.IsLimit`). The source record's
  chosen `colimit` is unnecessary because the node supplies an arbitrary colimit
  cocone. `Mathlib.CategoryTheory.Filtered.Basic` gives the directed-order
  instance of `CategoryTheory.IsFiltered` used by the proof.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` from
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, and `LinearMap.lTensor` /
  `LinearMap.rTensor` from the public import
  `Mathlib.LinearAlgebra.TensorProduct.Map`. These are the existing tensor
  construction and canonical maps, with `Submodule.subtype` the inclusion.
- `lem-weil-pbc-tensor-commutes-with-colimits`: proof-only imports include
  `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed`,
  `Mathlib.CategoryTheory.Monoidal.Closed.Braided`, and
  `Mathlib.CategoryTheory.Adjunction.Limits`. These supply the module-category
  closed monoidal structure, the recorded right-tensor left-adjoint instance,
  and its preservation of colimits. `Limits.isColimitOfPreserves` is the
  recorded canonical transport of a colimit cocone.
- `lem-weil-pbc-filtered-colimit-modules-elementwise`: proof-only imports
  `Mathlib.Algebra.Category.ModuleCat.FilteredColimits` and
  `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` supply
  `ModuleCat.FilteredColimits.forget_preservesFilteredColimits`,
  `CategoryTheory.Limits.Concrete.isColimit_exists_rep`, and
  `CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists`.

Searches for an existing statement (all through `msearch.py Q53` for this item,
2026-10-24, except the specified direct source searches):

- LeanFinder: "In a directed colimit of modules the least supporting submodules
  of a tensor eventually equal its least support in the colimit". Eight hits:
  `Submodule.FG.lTensor.directLimit_apply'`, `Submodule.FG.lTensor.directLimit_apply`,
  `Submodule.FG.rTensor.directLimit_apply'`, `Submodule.FG.rTensor.directLimit_apply`,
  `Submodule.FG.rTensor.directedSystem`, `TensorProduct.directLimitLeft_rTensor_of`,
  `Submodule.FG.lTensor.directedSystem`, `TensorProduct.fromDirectLimit`.
  These describe tensor-colimit comparisons, not least-support stabilization.
- Loogle: `TensorProduct, IsLeast`. Zero hits.
- Mathlib grep: `least.*support|support.*stabil|IsLeast.*Tensor`. Zero hits.
- LeanSearch: "Least tensor supporting submodule stabilizes at a finite stage of
  a directed colimit". Eight hits on `Submodule.FG` tensor direct limits and
  `TensorProduct.toDirectLimit`, `TensorProduct.directLimitLeft`; no stabilization.
- Direct `rg` with `least.*[Ss]upport|[Ss]upport.*stabil|IsLeast.*Tensor` in
  `lean/WeilConjectures` and `lean/Sheaf`: the pertinent results were
  `FlatMittagLefflerMinimalSupport.lean` and `FlatMittagLefflerCriterion.lean`.
  Read both: the former asserts existence and finite generation of a least
  support under flat Mittag-Leffler hypotheses; the latter states the criterion.
  Neither states this directed-system stabilization theorem. Other hits concern
  unrelated geometric support or degree bounds.
- The prescribed `grep -rn` for this item's id in `lean/WeilConjectures`
  returned no declaration. Direct searches for the new theorem/module name in
  Mathlib's/project's source inventory and `dag/lean_names_upstream.json`
  found no collision.

Edge cases checked mathematically before writing:

- The empty index is excluded by the node; `Nonempty I` makes that explicit,
  and `i : I` is also supplied. Singleton posets are allowed: choose `j = i`.
- For `xi = 0`, the least support is bottom at every stage and in the colimit;
  `t = 0` works. This includes `H = 0`, zero stage modules, and the zero ring.
- A noninjective system `Z → 0` with `H = Z` has initial tensor `1`, initial
  support top, and colimit support bottom. Its supports become bottom at the
  zero stage. Hence the statement needs neither injective transitions nor
  equality of every stage support with the colimit support.
- Tensoring `2Z ⊆ Z` with `Z/2` can destroy injectivity. The statement only uses
  the range and an explicit preimage witness, so this presents no problem.
- No assumption is imposed on stages below `i`; no largest stage or sequential
  enumeration is selected. Least-support hypotheses are actual hypotheses,
  rather than assertions that every tensor necessarily has a least support.

Validation: the prescribed `scompile.py` compiled the delivered file both as a
sandbox module and under its actual module name, with no errors or warnings
(1.3 seconds and 1.4 seconds respectively). No node fault or statement dispute
was found. No direct library edits, Git commands, or global builds were run.

## Second reading by Q53

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
