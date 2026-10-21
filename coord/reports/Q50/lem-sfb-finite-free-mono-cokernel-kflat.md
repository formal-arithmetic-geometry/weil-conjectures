## Worker report

Item: `lem-sfb-finite-free-mono-cokernel-kflat`, group Q50, stage 2.
Module: `Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat`.
Main declaration: `CochainComplex.finite_free_mono_cokernel_kflat`.

The module supplies two real, noncomputable constructions belonging to the item's
specified resolution, and one theorem whose entire proof is `sorry`. There are no
new definition nodes, dependency repairs, or statement corrections. The copied node
changes only its `lean` field.

Hypothesis and clause correspondence:

- A small site: `{C : Type u} [Category.{v} C]`, topology `J`, and
  `[EssentiallySmall.{r} C]`. This expresses smallness relative to the coefficient
  and module universe. The universes `u`, `v`, `r` are independent. No equality of
  site object, site morphism, or coefficient universes is assumed.
- The arbitrary commutative ring sheaf is `(R : Sheaf J CommRingCat.{r})`.
  Its underlying ring sheaf is the standard `sheafCompose` along
  `forget₂ CommRingCat RingCat`. There is no constant-coefficient hypothesis.
- The module category is the recorded `CategoryTheory.ringedSiteModules.{r}`
  applied to that ring sheaf, transparently Mathlib's `SheafOfModules`.
- `S : ShortComplex ...` packages exactly `P = S.X₁`, `Q = S.X₂`, `T = S.X₃`,
  `u = S.f`, `q = S.g`, and `S.zero : u ≫ q = 0`.
- The monomorphism assumption is `[Mono S.f]`. The specified projection is a
  cokernel by `hq : IsColimit (CokernelCofork.ofπ S.g S.zero)`. Thus the theorem
  covers every specified cokernel, not only the implementation's chosen object.
  Supplying a colimit witness changes no mathematical hypothesis: it is precisely
  the cokernel universal property and is unique for the specified cofork.
- The ranks `(m n : ℕ)` include zero. The specified isomorphisms `eP`, `eQ` have
  codomains `∐ (fun (_ : Fin m) ↦ SheafOfModules.unit ...)` and the analogous
  rank-`n` sum. `unit` is the regular module sheaf, not a constant sheaf. Finite
  coproducts in this abelian category are the finite direct sums in the node.
- `monoCokernelComplex S.f` is, by its actual definition, the canonical
  `mappingCone ((singleFunctor _ 0).map S.f)`. This uses the node's expressly
  equivalent cone presentation. Its canonical component identifications give
  `P` in degree `-1`, `Q` in degree `0`, and zero otherwise, with all other
  differentials zero. In Mathlib the biproduct order is shifted source first;
  this is the canonical permutation of the Stacks order. The displayed final
  equality says the differential carries the shifted-source inclusion to the
  unshifted-target inclusion composed with `u`, with positive sign. In detail,
  `(mappingCone.inl ...).v 0 (-1) rfl ≫ C.d (-1) 0 =
  ((singleFunctor _ 0).map S.f).f 0 ≫ (mappingCone.inr ...).f 0`.
- `monoCokernelAugmentation S` is the existing
  `mappingCone.descShortComplex (S.map (singleFunctor _ 0))`. Its construction
  has zero shifted-source cochain and right component `q[0]`. It therefore
  has exactly degree-zero component `q` under the canonical identifications and
  zero components elsewhere, rather than an arbitrary quasi-isomorphism.
- The first conjunct is `QuasiIso (monoCokernelAugmentation S)`.
- The next three conjuncts are `∀ i : ℤ, SheafOfModules.IsFlatOnSite ...`
  for the terms of `monoCokernelComplex S.f`, `singleFunctor _ 0 |>.obj S.X₁`,
  and `singleFunctor _ 0 |>.obj S.X₂`, respectively. They assert flatness of
  every term, including the zero terms; they do not assert flatness of `T`.
- The next three conjuncts are `IsKFlatIndependentCoefficients` of those same
  three complexes, using the recorded arbitrary-universe K-flat predicate.
- The next conjunct is
  `IsKFlatResolutionIndependentCoefficients (monoCokernelAugmentation S)`.
  Its definition is exactly quasi-isomorphism together with K-flat source.
- The normalization conjunct is
  `mappingCone.inr ((singleFunctor _ 0).map S.f) ≫
  monoCokernelAugmentation S = (singleFunctor _ 0).map S.g`.
  This is the node's specified `Q[0] → C_u → T[0] = q[0]`.
- There is no assumption that `u` is scalar multiplication.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` (recorded module-sheaf category).
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`;
  `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso` (both publicly available through
  the construction/K-flat imports).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, exactness of the actual sheaf tensor functor.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and
  `CochainComplex.IsKFlatResolutionIndependentCoefficients`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`, the recorded abstract-derived-category interface;
  its cone convention is implemented by `CochainComplex.mappingCone`.
- `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`:
  `CochainComplex.mappingCone.descShortComplex`, the recorded
  `quasiIso_descShortComplex`, and the canonical cone summand maps.
- `Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`:
  `CochainComplex.singleFunctor`, the degree-zero single-complex functor.
- Proof-plan imports (private):
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`:
  `SheafOfModules.isFlat_coproduct`;
  `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`:
  `CochainComplex.isKFlat_of_boundedAbove_flat`.
  Their recorded equal-universe specializations do not impose equalities on the
  statement. For a later proof at independent universes, transport to the small
  model, or use the existing independently generalized bounded-flat interface in
  `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`.

Sources read locally: Stacks `sites-cohomology.tex`, lemma-bounded-flat-K-flat
(Tag 06YQ); `homology.tex`, definition-quasi-isomorphism-cochain (Tag 0115);
`derived.tex`, definition-cone, including the differential matrix. The theorem
docstring records all six proof steps with their DAG dependencies.

Edge cases checked before drafting:

- `m = 0`: the source is zero and the resolution gives the specified cokernel of
  `0 → Q`, canonically isomorphic to `Q[0]`.
- `n = 0`: monicity forces the source to be zero as well; all complexes are zero.
- Both ranks zero, the zero ring sheaf, or the empty site: every construction
  still exists and all conclusions hold. No nonempty or nonzero hypothesis appears.
- `u` an isomorphism: its cokernel is zero and its cone is acyclic and K-flat.
- Point site, `R = ℤ`, `u = 2 : ℤ → ℤ`: `T = ℤ/2` need not be flat. The
  theorem correctly asserts flatness of the resolution terms and of the single
  free complexes only.
- Arbitrary monomorphisms of positive ranks and arbitrary nonconstant ring sheaves
  remain allowed. No assumptions about points or sectionwise flatness are imposed.

Searches for existing statements, all performed through the prescribed tools:

- `msearch.py ... leanfinder "An injective morphism of finite free sheaves has a K flat
  two term complex resolving its cokernel with the quotient augmentation"`:
  eight results, including `SheafOfModules.generatorsOfIsCokernelFree`, its
  component declarations, and K-injective results; no matching theorem.
- `msearch.py ... loogle '"mappingCone", "quasiIso"'`:
  exactly `CochainComplex.mappingCone.quasiIso_descShortComplex`. This supplies
  the general cone quasi-isomorphism, not the finite-free flatness/K-flatness result.
- `msearch.py ... leansearch "A monomorphism of finite free module sheaves has a
  K flat two term cokernel resolution"`: eight results, including module-flatness
  criteria and `ShortComplex.exact_and_mono_f_iff_f_is_kernel`; no exact match.
- `msearch.py ... grep 'finiteFree.*[Cc]okernel|[Kk][Ff]lat|quasiIso_descShortComplex'
  Algebra/Homology`: five hits, all the general cone quasi-isomorphism or its
  derived/Ext consumers. No K-flat finite-free-sheaf result.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for finite-free monomorphism /
  cokernel / K-flat phrases and for the item ID found no exact theorem. A nearby
  `UniversalH0SplitDifferential` reference concerns a different statement.
- `rg` on both source roots and `dag/lean_names_upstream.json` for
  `monoCokernelComplex|monoCokernelAugmentation|finite_free_mono_cokernel_kflat`
  returned no declarations. No existing notion is copied: the helper definitions
  only assemble Mathlib's canonical cone and canonical descShortComplex.

Validation: `scompile.py Q50 lem-sfb-finite-free-mono-cokernel-kflat <module>`
passed both sandbox and library-module compilation, without warnings or errors
(26.8 s and 23.9 s). All variables and universes are explicitly bound; no local
notation or local instances are introduced. The only postponed theorem is the
main theorem, matching this DAG node. No statement is disputed.

## Second reading by Q50

I reopened the node and final module for a second clause-by-clause check, using
the correspondence above. The dispatcher explicitly prohibits starting other
agents; this is a worker self-check, with independent review left to the
maintainer as specified in the brief, not a claim of an independent worker review.

I checked the three termwise-flatness clauses and the three K-flatness clauses
separately; the target is the supplied cokernel and its own projection. I checked
the positive-sign formula against Mathlib's `mappingCone.inl_v_d` and Stacks'
cone matrix, and the augmentation normalization against
`mappingCone.inr_descShortComplex`. The cone representation is expressly allowed
by the node's equivalently clause and introduces no arbitrary representative.
The rank-zero and nonflat-cokernel cases are preserved. No mismatch in the node's
statement required correction. Compilation repairs made the single-functor import
public and pinned the topology argument of the flatness predicates; neither
changes the mathematical statement. No upstream or live source was edited.
