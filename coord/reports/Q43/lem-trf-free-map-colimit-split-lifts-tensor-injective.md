## Worker report

The module `Sheaf.RingTheory.FreeMapColimitSplitLiftsTensorInjective` states
`LinearMap.lTensor_injective_of_finite_basis_eventually_split_lifts`, with its
whole proof postponed by `sorry`. It introduces no definitions or extra nodes.
The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`.
- The free module with its chosen arbitrary basis is `{M : Type w}` with
  `[AddCommGroup M] [Module R M]` and `(b : Module.Basis B R M)` for `{B : Type z}`.
  A chosen basis is the data underlying the recorded `Module.Free` notion;
  no redundant freeness hypothesis or replacement definition is introduced.
- The small nonempty directed partially ordered index set is `{I : Type v}`
  with `[PartialOrder I] [Nonempty I] [IsDirectedOrder I]`. The canonical
  preorder category structure gives an arrow `homOfLE h` for each `h : i ≤ j`.
- The module diagram is `F : I ⥤ ModuleCat.{max u v} R`. Its stages are
  `F.obj i`; transitions are `(F.map (homOfLE h)).hom`. Functor laws express
  precisely the required identity and composition laws.
- The given module `N` is the vertex `c.pt` of `(c : Cocone F)`; its maps
  `q_i` are `(c.ι.app i).hom`. Cocone naturality supplies their compatibility,
  and `(hc : IsColimit c)` says exactly that these maps exhibit this vertex
  as the colimit. This quantifies over arbitrary colimit cocones, rather than
  requiring the vertex to be a particular chosen construction.
- The given map is `(u : M →ₗ[R] c.pt)`.
- Each finite subset is `E : Finset B`. The exact submodule `P_E` is
  `Submodule.span R (b '' (E : Set B))`, and its inclusion `a_E` is `.subtype`.
  This uses the existing span construction directly.
- `hlifts` says, for every `E`, there exist `(i : I)` and a linear map `f`
  from that span to `F.obj i`. The first conjunct
  `(c.ι.app i).hom.comp f = u.comp (...).subtype` is `q_i v_E = u a_E`.
- The second conjunct quantifies over every `(j : I) (h : i ≤ j)` and supplies
  a linear map `s` back to the same span with
  `s.comp ((F.map (homOfLE h)).hom.comp f) = LinearMap.id`.
  The quantifiers keep the same `i` and `f` while allowing each `s` to be
  chosen individually. No transition or finite-subset coherence is imposed.
- `(L : Type t) [AddCommGroup L] [Module R L]` is an arbitrary test module.
  `Function.Injective (u.lTensor L)` is precisely injectivity of `1_L ⊗ u`.
  `LinearMap.lTensor` is `TensorProduct.map LinearMap.id u`.
- There are no free or flat assumptions on diagram stages, no flatness
  assumption on `L`, and no nonzero or finite-rank assumptions.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Mathlib.LinearAlgebra.FreeModule.Basic`,
  `Module.Free`, `Module.Free.of_basis`; the chosen basis is
  `Module.Basis` in `Mathlib.LinearAlgebra.Basis.Defs`, whose data is the
  linear coordinate equivalence `M ≃ₗ[R] (B →₀ R)`.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, and its recorded accompanying
  `Cocone` and `IsColimit`, read in `Limits.Cones` and `Limits.IsLimit`.
  `CategoryTheory.IsFiltered` in `CategoryTheory.Filtered.Basic` and its
  nonempty directed preorder instance provide the filtered interpretation.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, canonical bilinear `mk`,
  `TensorProduct.lift` and `ext'` in `.Basic`, and `LinearMap.rTensor` and
  `LinearMap.lTensor` in `.Map`; the statement needs the left tensor map.
- Proof input `lem-weil-pbc-tensor-commutes-with-colimits`: the recorded
  `CategoryTheory.ihom.instIsLeftAdjointTensorRightOfClosed` in
  `Mathlib.CategoryTheory.Monoidal.Closed.Braided` and
  `CategoryTheory.Limits.isColimitOfPreserves` in `.Limits.Preserves.Basic`.
  Nonpublic proof imports also supply the closed module category and
  adjoint preservation of colimits. These categorical APIs use a common
  module/ring universe; the theorem does not impose such an equality on
  its independent ring and index universes. A future proof can lift to a
  common universe, or use the arbitrary-universe direct-limit tensor API.
- Proof input `lem-weil-pbc-filtered-colimit-modules-elementwise`:
  `Concrete.isColimit_exists_rep` and `Concrete.isColimit_rep_eq_iff_exists`
  in `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
  `ModuleCat.FilteredColimits.forget_preservesFilteredColimits` in
  `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`, imported nonpublicly.

Source and edge cases:

Read `literature/stacks-project/flat.tex`, proof of Tag 05FQ
(`lemma-universally-injective-local`). The source first reduces to finite
free direct summands, obtains split injections at every later stage, and
then tensors and passes to the directed colimit. The node isolates this
last argument; it does not need the local-ring or residue-field assumptions
used earlier to obtain the splitting hypothesis. Its four proof steps are
carried into the theorem docstring, including the tensor flip and zero
 detection. No statement correction or disputed claim is needed.

Checked empty `B`, empty `E`, infinite `B`, zero ring and zero modules,
one-point directed systems, nonflat stages and test modules, and retractions
without coherence. The empty span is the zero submodule and causes no
special binder restriction. Infinite bases are represented by finitely
supported coordinates. All universes are explicitly declared; `R`, `M`,
`B`, `I` and `L` have independently named universes. Diagram modules and
its vertex use `max u v`, the common universe containing ring and index
sizes, without requiring those sizes equal. For an instance with larger
stage modules, take the index universe at a common larger level (or lift
its index type); no mathematical diagram is lost.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: “A map from a free module into a directed
  colimit is tensor injective if every finite basis span lifts to a stage
  and splits at every later stage”. Eight results, including
  `Module.DirectLimit.lift_injective`, `LinearMap.rTensor_injective_of_fg`,
  and finite-submodule tensor direct-limit lemmas. None is this criterion.
- `msearch.py ... leansearch`: “A linear map from a free module into a
  directed colimit is tensor injective if each finite basis span has a lift
  that splits in every later stage”. Eight results, including direct-limit
  injectivity, tensor direct-limit comparison and flatness criteria; none
  has these hypotheses and conclusion.
- `msearch.py ... loogle`: `LinearMap.lTensor, Function.Injective`.
  Twelve hits: left/right tensor equivalence, flat/faithfully-flat tensor
  criteria, exact-sequence criteria and local residue-field splitting.
  None states this directed-colimit finite-basis-lift criterion.
- `msearch.py ... grep`: `split|injective` in
  `LinearAlgebra/TensorProduct/DirectLimit.lean`: zero reported hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `split_lifts`, `eventually.*split`, and `finite.*basis.*span` returned
  contextual uses (including `LocalUniversalInjectiveResidue`) but no
  equivalent statement. A separate full-name search in those trees,
  Mathlib and `dag/lean_names_upstream.json` found no name collision.

Validation: the prescribed `scompile.py Q43
lem-trf-free-map-colimit-split-lifts-tensor-injective <module>` passed for
both its sandbox and final library module names (8.0 s and 4.6 s), with
no errors or warnings. Every variable is explicitly bound. The delivery
contains exactly one theorem, with `sorry` as its whole proof.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
