## Worker report

The module `Sheaf.CategoryTheory.CondensedActionInjectiveRestriction` states this node in
four named theorems, all with `sorry` as their entire proof. The auxiliary definitions
have actual data. The two induction structures specify a canonical construction by its
natural comparison with the actual relative tensor, its generalized-section action, and
its normalized adjunction. No functor or module is selected from their existence.

Hypothesis and clause correspondence:

- An arbitrary commutative condensed ring is `A : CategoryTheory.CondensedBar.Ring.{u}`,
  the existing `CommMon` of abelian sheaves; `A.toMon` is the recorded
  `Profinite.CondensedRing`, with its bundled commutativity instance. This is equivalent
  to an arbitrary `R : Profinite.CondensedRing` with `IsCommMonObj R.X`: bundle R and its
  proof as `CommMon.mk R.X`. There is no topological presentation or constant-ring condition.
- The coherent profinite site is `coherentTopology Profinite.{u}`. The represented set
  sheaf uses its `uliftYoneda.{u+1}`; coefficients and abelian groups live in `u+1`, and
  internal modules in `u+2`. All universes and variables are explicitly bound and
  `autoImplicit` is false. No equality of site object and morphism universes is imposed.
- Profinite groups are `G H : Type u`, with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
  Universal `P` in `forget_tensor_induction` includes 1, G, H and G times H.
- Internal modules and actions are the exact existing `Modules A.toMon` and
  `ActionModule A.toMon P`. The action is on every continuous generalized group
  element, not the abstract discrete group. `forgetAction` is U_P, and
  `inflate (ContinuousMonoidHom.inr G H)` is restriction to the H factor.
- `restrictionFree` is the existing composite free functor on the represented sheaf,
  and `restrictionGenerator` is exactly the unit of `InternalBar.freeAdjunction`.
  These helpers abbreviate and evaluate existing constructions; they do not define
  another free-module functor or another free-module notion.
- `restriction_free_flat_comparison` identifies its sectionwise realization with
  `SheafFreeModule.free` on the same represented sheaf. That definition is module
  sheafification of `PresheafOfModules.free`, whose sections are the direct sum of
  copies of A(V) indexed by V to S. The comparison sends each actual generator to
  `generatorRaw`, so this is the specified sheafification identification.
- The same theorem asserts `PreservesFiniteLimits` and `PreservesFiniteColimits` for
  `tensorLeft (restrictionFree A S)`, for EVERY `S : Profinite`, rendering flatness
  and exactness. It also asserts both preservation properties for the sectionwise
  equivalence. Tensor isomorphisms are natural in both variables and normalized by
  `InternalBar.pureTensor` and `comparison_sectionTmul`.
- Its Hom isomorphisms use the existing equalizer `Mod.ihom' A.X M`, and the existing
  `SheafOfModules.homObj`, with the ring argument explicit. Their naturality in both
  variables uses the canonical induced equalizer map: its composite with the inclusion
  is `equalizer.ι ≫ Mod.homModMap M.X g ≫ Mod.homModPre f.hom N'`, which uniquely
  determines that map. The evaluation equation identifies the local map evaluated at
  `Over.mk (𝟙 S)` with `restrictionHomEvaluation`. The latter is the actual ambient
  closed evaluation of the equalizer inclusion. Thus this comparison retains evaluation,
  rather than merely asserting an unrelated isomorphism of objects.
- `forget_tensor_induction` gives preservation and reflection of exactness as
  `K.Exact ↔ (K.map forgetAction).Exact`, and both finite-limit/colimit preservation
  classes. It asserts `Nonempty (ForgetTensorInduction A P)` and
  `forgetAction.PreservesInjectiveObjects`.
- `ForgetTensorInduction.underlying` is the natural comparison to
  `tensorLeft (restrictionFree A (Profinite.of P))`; `translation` is
  p([g] tensor m) = [pg] tensor m. `untranspose` sends f to the map
  [g] tensor m to gf(m). Since it is the inverse of the adjunction Hom equivalence,
  it also fixes the forward transpose (evaluation at [1] tensor m). `limits` and
  `colimits` assert exactness of this very functor, not an unrelated left adjoint.
- `product_tensor_induction` gives the same three conclusions for restriction to H,
  with `ProductTensorInduction.underlying` equal to forgetAction followed by A[G]
  tensor -. Its action is (g0,h)([g] tensor m) = [g0g] tensor hm. Its inverse
  transpose is [g] tensor m to (g,1)f(m), precisely the claimed formula. Exactness
  and preservation of injective objects are explicit conclusions.
- `action_injective_restriction` quantifies over every existing normalized
  `ProductInvariants A.toMon G H`. It asserts existence of `InjectiveResolution N`
  for every N, and that this invariants functor preserves injective objects.
  Mathlib's resolution is nonnegative and comes with a quasi-isomorphism from N[0];
  `I.cochainComplex` extends it by zero to integers.
- For EVERY such I and EVERY `q : ℤ`, the four `Injective` conjuncts are respectively
  U_(G times H) I^q, Res_H I^q, (I^q)^H as a G-action, and its underlying module.
- The next two conjuncts are `I.cochainComplex.IsKInjective` and
  `CochainComplex.IsKInjective (V.functor.mapHomologicalComplex ... |>.obj ...)` in
  the two respective action categories. The final `Nonempty (... ≅ ...)` identifies
  total right derived invariants at the degree-zero embedding of N with the
  localization of the termwise invariant complex. It does not assert that the latter
  resolves the underived invariants.

Dependency interfaces read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.CategoryTheory.CondensedProductActionInflation`:
  `Profinite.CondensedAction.product_action_inflation`; its public action module supplies
  `ActionModule`, `Modules`, `forgetAction`, `inflate`, `ProductInvariants`, and their
  precise generalized-section formulas. The existing
  `Sheaf.CategoryTheory.CondensedDerivedInvariants` supplies the compatible abelian and
  Grothendieck instances on these SAME categories, without importing the downstream
  product-bar comparison.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` and its module-object laws.
- `Sheaf.CategoryTheory.CondensedInternalBarResolution`:
  `InternalBar.free`, `freeAdjunction`, `onSections`, `pureTensor`. The first two are
  exactly the record of `def-sfb-condensed-free-module-adjunction`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`: `Mod.monoidalCategory` and
  its actual relative tensor quotient, publicly available through the free-module module.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `sectionModuleEquivalence`, `sectionRingSheaf`, `sectionModuleFunctor`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
  `internal_section_tensor_comparison` and `comparison_sectionTmul`.
- `Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`:
  `Mod.nonempty_equalizerInternalHomAdjunction`, reexporting the actual equalizer
  `Mod.ihom'`, `homModPre`, `homModMap`, `homModB` from upstream InternalHom.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`, `homObj` and `homObjMap`. The explicit Hom definition
  permits independent site and coefficient universes; no extra universe equation is used.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `Injective`, `InjectiveResolution`. The latter's `.cochainComplex` and degree-zero
  quasi-isomorphism are the existing Mathlib extension construction.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` and `isKInjective_of_injective`. These are also the
  generic interfaces named in the recorded K-injective-resolution node; its specialized
  étale abbreviation is not copied or applied to a different category.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  generic unbounded-derived convention. The final assertion uses the ordinary
  `Functor.rightDerivedFunctor`, `DerivedCategory.singleFunctor` and `DerivedCategory.Q`
  on the Grothendieck action categories, as permitted in that record's note.
- Proof imports include the recorded free-module universal property, extension-by-zero
  flatness, exact module sheafification, right-adjoint preservation of injectives,
  Grothendieck enough injectives, degree-zero resolution, bounded-below K-injectivity
  and `Sheaf.CategoryTheory.KInjectiveComputes`.

Edge cases: P may be the one-element group; G or H can be trivial. All modules and the
coefficient ring may be zero. S ranges over all profinite sets, including empty; free
on empty is zero by the empty-cover sheaf axiom (not by falsely claiming every section
module is globally free). q ranges over all integers, so negative zero terms are included.
No nontriviality, finite-index, discrete-action or constancy assumption is introduced.

Searches before writing:

- `msearch.py ... leanfinder "Exact induction for internal condensed group modules and
  injective restriction"`: ordinary CondensedMod and unrelated exactness hits, no exact
  statement for variable condensed rings and internal product actions.
- `msearch.py ... loogle "CategoryTheory.Adjunction.map_injective,
  CochainComplex.IsKInjective"`: no combined hit. The exact individual declarations were
  read directly in Mathlib and reused.
- `msearch.py ... grep "Condensed.*[Ii]nject|[Ii]nduc.*Condensed"`: two unrelated
  coinduced-topology hits, no relevant induction theorem.
- `msearch.py ... leansearch "Free modules on represented profinite sets over a
  condensed ring are flat, exact induction preserves injectives under restriction"`:
  ordinary `Module.Flat.of_free`, `Condensed.instAB4CondensedMod` and
  `Condensed.profiniteFree`; none gives this variable-ring internal-action statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  injective restriction/induction found nearby split-coset induction, tensor induction,
  bar rows and derived invariants. Their signatures were read. They neither state
  all these clauses nor supply the normalized A[G] tensor M product induction.
  `CondensedProductBarComparison` is a consumer and is deliberately not imported.
- Declaration-name search for all added names in both source roots found none.

Sources read: the latest blueprint direct-images proof paragraph (3); local Stacks
sites-modules.tex at internal-hom-adjoint-tensor (03EO), j-shriek-flat (03EV), and the
free-module construction in the proof of universal-module (04BL); homology.tex at
adjoint-preserve-injectives (015Z); derived.tex at injective-resolutions-exist (013K)
and acyclic-is-zero (013R). These support the generic ringed-site/homological inputs.
The node explicitly calls the assembled ordinary condensed-action reference WANTED;
no new external citation is invented. No counterexample or statement fault was found.
No statement correction, new node, or dependency-record repair is needed.

Validation: all delivered declarations compile through the prescribed scompile.py,
including compilation under the actual library module name. Every theorem is left
as `by sorry`, with the complete natural-language proof supplied in its docstring.

## Second reading by Q142

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
