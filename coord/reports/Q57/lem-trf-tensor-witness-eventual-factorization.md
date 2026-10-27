## Worker report

The module `Sheaf.RingTheory.TensorWitnessEventualFactorization` states
`Module.exists_eventual_factorization_of_tensor_witness`, with its proof left as
`sorry`. The node is unchanged except for its `lean` record. No definitions,
dependency repairs, or statement corrections are needed.

The source read was `literature/stacks-project/algebra.tex`, lines 20916–21067
(Tags 059C, 059D, 059E) and 21415–21531 (Tags 059L and 059M). Killing the universal
kernel element in the prescribed system is exactly the argument of 059L;
naturality in the test module is the square in 059M. The finite-presentation
and factorization argument is 059E (2) implies (3). The docstring gives all four
accepted proof steps, including the augmented finite relation matrix.

Each hypothesis and clause is rendered as follows:

| Node text | Lean |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| Small nonempty directed partially ordered index set | `{I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]`; the standard preorder category is small |
| Directed system of R-modules with compatible transitions | `(F : I ⥤ ModuleCat.{max u v w} R)`; transition `f_st` is `(F.map (homOfLE hst)).hom`, with the system identities supplied by functoriality |
| Every stage finitely presented | `[∀ s : I, Module.FinitePresentation R (F.obj s)]` |
| Compatible maps u_s to M exhibiting its colimit | `(c : Cocone F) (hc : IsColimit c)`; `M` is the arbitrary cocone vertex `c.pt`, and `u_s` is `(c.ι.app s).hom`; naturality gives precisely compatibility |
| Fixed i and an arbitrary R-module T | `(i : I) (T : Type t) [AddCommGroup T] [Module R T]` |
| Tensor element z | `(z : F.obj i ⊗[R] T)` |
| `(u_i ⊗ id_T)(z) = 0` | `(hz : (c.ι.app i).hom.rTensor T z = 0)` |
| Every finitely presented test module Q | The `∀ Q` and three module/finite-presentation instance binders in `hwitness` |
| Every x in the kernel for Q | `∀ x : F.obj i ⊗[R] Q, (c.ι.app i).hom.rTensor Q x = 0 → ...` |
| There exists q : T → Q carrying z to x | `∃ q : T →ₗ[R] Q, q.lTensor (F.obj i) z = x`; `lTensor` is `id ⊗ q`, whereas `rTensor` above is `u_i ⊗ id` |
| There exists a single j ≥ i | `∃ (j : I) (hij : i ≤ j), ...` |
| For every k ≥ j there exists h_k : M_k → M_j | `∀ (k : I) (hjk : j ≤ k), ∃ h : F.obj k →ₗ[R] F.obj j, ...` |
| `f_ij = h_k ∘ f_ik` | `(F.map (homOfLE hij)).hom = h.comp (F.map (homOfLE (hij.trans hjk))).hom` |
| No flatness, Mittag-Leffler, or countability hypothesis | None of these occurs among the binders |

The carrier universe `max u v w` contains the ring and the small index universe,
as required for the filtered-colimit APIs; `w` permits arbitrarily large module
carriers. The auxiliary module T has an independent universe `t`. Test modules
are in the common carrier universe, which contains every finite free R-module
and every finite-presentation quotient. This tests every finitely presented
module up to linear equivalence: an arbitrary such module is isomorphic to a
quotient of a finite free module (the `Module.FinitePresentation.exists_fin`
description read in Mathlib). Thus there is no vacuous testing universe smaller
than R and no excluded finite-presentation test. Linear equivalences transport
both the tested tensor element and the witnessing map from T.

Statement dependencies used, with their source declarations read:

- `def-sc-finitely-presented-module`:
  `Mathlib.Algebra.Module.FinitePresentation`, `Module.FinitePresentation`
  (class at lines 67–69, finite generation with finitely generated relations).
- `def-weil-pbc-category-colimit`:
  `Mathlib.CategoryTheory.Limits.HasLimits`, together with its public imports,
  `CategoryTheory.Limits.Cocone` and `CategoryTheory.Limits.IsColimit`.
  Their full structures were read in `Limits/Cones.lean:133` and
  `Limits/IsLimit.lean:62`. They describe an arbitrary colimit with the given
  legs, avoiding any additional identification with a chosen colimit object.
- `def-weil-pbc-module-tensor-product` has a Mathlib match, not a Lean record:
  `TensorProduct` and `LinearMap.rTensor` in
  `Mathlib.LinearAlgebra.TensorProduct.Map`; also the existing `LinearMap.lTensor`
  in that module for changing the right factor. The definitions and their
  pure-tensor formulas at lines 327–347 were read.

Proof dependency imports are ordinary, non-public imports. They provide
`CategoryTheory.Limits.isColimitOfPreserves`, the closed braided module-category
tensor adjunction and its colimit-preservation instances, and
`CategoryTheory.Limits.Concrete.isColimit_rep_eq_iff_exists` /
`Concrete.colimit_rep_eq_zero` with
`ModuleCat.FilteredColimits.forget_preservesFilteredColimits`.
The final factorization declaration is
`WeilConjectures.tensorKernelFactorization` in
`Sheaf.SecTraceFormula.TensorKernelFactorization`; its complete signature and
docstring were read. No proof dependency was omitted for an import cycle.

Edge cases checked before writing:

- A singleton index has an isomorphism as its colimit leg, and the identity map
  supplies the required backward factorization.
- Empty indices are expressly excluded by the node and by `Nonempty I`;
  arbitrary uncountable directed posets remain admitted.
- Zero stages and the zero ring are allowed; the required maps are zero maps.
- T = 0 or z = 0 is allowed. The universal witness condition then asserts that
  all the tested kernels are zero; it is retained, rather than silently assumed
  for these cases. The finite-cokernel factorization argument still applies.
- k = j is included (identity factorization). No strict inequality is used.
- The colimit leg need not be injective, and neither T nor the colimit needs to
  be flat. The proof uses tensor-colimit preservation and functoriality, not
  left exactness of tensoring.

Searches made for an existing exact statement:

- `msearch.py ... leanfinder "A universal tensor kernel witness in a directed
  colimit of finitely presented modules gives eventual backward factorization
  of transition maps"`: eight hits, including `TensorProduct.fromDirectLimit`,
  `TensorProduct.directLimitLeft`, and finite-submodule tensor direct-limit
  comparisons; none has the universal-witness hypothesis or conclusion.
- `msearch.py ... loogle "Module.DirectLimit, LinearMap.comp"`: eleven hits,
  including `Module.DirectLimit.lift_comp_of`, `map`, and `hom_ext`; none is the
  eventual backward factorization theorem.
- `msearch.py ... grep
  "tensor.*kernel.*factor|kernel.*tensor.*factor|dominat" LinearAlgebra`: one
  unrelated comment in `LinearIndependent/BaseChange.lean`.
- `msearch.py ... leansearch "A single tensor kernel witness for a directed
  colimit of finitely presented modules yields eventual backward factorization
  of transition maps"`: direct-limit/tensor comparison results and
  `ModuleCat.directLimitIsColimit_desc`, not this statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for kernel/tensor/factorization
  patterns, and `grep -rn` for this node id in `lean/WeilConjectures`: no exact
  existing declaration. The closely related project declaration is the proof
  dependency `WeilConjectures.tensorKernelFactorization`, whose hypotheses are
  kernel inclusions for a pair of maps, not a universal witness in a colimit.
- Exact proposed-name searches in both source roots and
  `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py Q57 lem-trf-tensor-witness-eventual-factorization` on
the delivered module passed both sandbox and library checks (5.8 s and 2.7 s),
with no errors or unexpected warnings. `autoImplicit` is disabled and all four
universe parameters are declared explicitly.

## Second reading by Q57

Independent second reading (maintainer reviewer NT-cc, 2026-10-24) of the
delivered module `Sheaf.RingTheory.TensorWitnessEventualFactorization` against
the node, its three statement dependencies and Stacks algebra.tex 059L
(l.21415), 059M (l.21443, proof of (2) ⇒ (1)), 059E/059C/059D. The worker's
own self-check is superseded by this section.

Clause by clause:

1. Commutative ring R — `(R : Type u) [CommRing R]`. Correct.
2. Small nonempty directed poset I — `{I : Type v} [PartialOrder I] [Nonempty I]
   [IsDirected I (· ≤ ·)]`; the preorder category is a `SmallCategory.{v}`.
   No countability. Correct.
3. Directed system (M_s, f_st) of finitely presented modules
   (def-sc-finitely-presented-module = `Module.FinitePresentation`) —
   `F : I ⥤ ModuleCat.{max u v w} R` with `[∀ s, Module.FinitePresentation R (F.obj s)]`;
   f_st = `(F.map (homOfLE h)).hom`, identities/composition from functoriality.
   Carrier universe `max u v w` is the standard filtered-colimit convention, `w`
   free; no restriction on the size of the modules. Correct.
4. Compatible u_s exhibiting M as colimit (def-weil-pbc-category-colimit,
   recorded declarations `Cocone`, `IsColimit`) — `(c : Cocone F) (hc : IsColimit c)`,
   M = `c.pt`, u_s = `(c.ι.app s).hom`. Arbitrary colimit, not a chosen one: as
   the node says. Correct.
5. i, R-module T (any universe `t`), z ∈ M_i ⊗ T with (u_i ⊗ id_T)(z) = 0 —
   `rTensor T` is `u_i ⊗ id`. Correct.
6. Witness hypothesis: ∀ fp Q, ∀ x ∈ ker(u_i ⊗ id_Q), ∃ q : T → Q with
   (id ⊗ q)(z) = x — `hwitness`, `lTensor (F.obj i)` is `id ⊗ q`. Q ranges over
   `Type (max u v w)`; every fp R-module is isomorphic to a quotient of
   `Fin n → R` in `Type u ⊆ Type (max u v w)`, and both kernel condition and
   witness transport along linear equivalences, so the hypothesis is equivalent
   to the node's (not stronger). Correct.
7. Conclusion ∃ j ≥ i ∀ k ≥ j ∃ h_k : M_k → M_j, f_ij = h_k ∘ f_ik — quantifier
   order ∃ j ∀ k ∃ h, composition `h.comp f_ik`, k ≥ j (not k ≥ i), equality of
   linear maps. Correct, neither weaker nor stronger.
8. No flatness/ML/countability — none among the binders. Correct.

Edge cases: singleton I (identity), k = j (identity factorization), T = 0 or
z = 0 (hypothesis then forces all tested kernels zero; conclusion still true via
059C/059D), zero ring, non-injective legs, uncountable I. All admitted; empty I
excluded by the node and `Nonempty I`.

Records: `lean.statement` verbatim equal to the file signature; only the `lean`
field of the node changed versus live; stmt_dep records read (FinitePresentation
existing Mathlib, colimit existing Mathlib, tensor product Mathlib match:
`TensorProduct`, `rTensor`/`lTensor`). No name collision for
`Module.exists_eventual_factorization_of_tensor_witness` in live/side-live.
Proof-dep import `Sheaf.SecTraceFormula.TensorKernelFactorization` is a module-mode
file whose `tensorKernelFactorization` has a free `uQ`, so the stated universes
suit the intended proof. Module and theorem docstrings carry the Stacks places,
`(blueprint: lem-trf-tensor-witness-eventual-factorization)` and the four proof
steps. No definitions (nothing hollow); proof is `sorry`; no pro-étale substitute.

Searches: Mathlib `Module.DirectLimit`, `TensorProduct.directLimit*`,
`Module.Flat.exists_factorization_of_isFinitelyPresented` (needs flatness),
`IsFinitelyPresentable.exists_eq_of_isColimit` — none states this result.

Mismatches found: none in the Lean or records; this section replaces the
worker's self-check (H11).
