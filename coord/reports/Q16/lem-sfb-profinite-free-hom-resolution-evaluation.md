## Worker report

The module `Sheaf.CategoryTheory.ProfiniteFreeHomResolutionEvaluation` states the node as
`CategoryTheory.CondensedBar.ProfiniteHom.exists_evaluation`, whose conclusion is
`Nonempty (Evaluation A)`. The `Evaluation` structure collects the specified normalized
isomorphisms and all their equations; no object is selected from this existence theorem.
The auxiliary theorem `hom_additive_leftExact` states the node's additive, left-exact
internal Hom clause and supplies the additive instance needed to type its derived functor.
Both theorem proofs are `sorry`. The remaining declarations are transparent constructions
or a structure specification, with no postponed data.

Hypotheses and universes:

- `A : CategoryTheory.CondensedBar.Ring.{u}` is the existing abbreviation for an arbitrary
  commutative monoid in tensor abelian sheaves on `coherentTopology Profinite.{u}`. This
  bundles exactly the arbitrary condensed ring and its commutativity; it assumes no
  topological presentation, field, flatness, or nonzero hypothesis.
- The site is the existing coherent profinite site, with finite jointly surjective covers.
  Objects have universe `u+1`, arrows universe `u`, coefficient sections universe `u+1`,
  and the module category universe `u+2`. No equality of object and arrow universes is
  imposed. `SheafOfModules.homObj.{u+1,u,u+1,u+1}` keeps exactly these sizes.
- `[HasDerivedCategory.{u+2} (Modules A)]` fixes the ordinary unbounded localization
  in the permitted ambient size, as in the existing bar interfaces. This structure is
  available from `HasDerivedCategory.standard`; it adds no mathematical restriction.
- `M : Modules A` and every profinite `P`, `S` are universally quantified. The resolution
  is an arbitrary integer-indexed cochain complex `I`, a map `s : M[0] ⟶ I`, vanishing
  `IsZero (I.X n)` for `n < 0`, injectivity of every term, and `QuasiIso s`. These are
  exactly a nonnegative injective resolution, including the zero terms in negative degrees.

Clause-by-clause rendering:

- Internal modules are the recorded `Mod` category through `CondensedBar.Modules`.
  `Evaluation.grothendieck` states Grothendieck abelianness at coefficient size;
  `Evaluation.resolutions` gives `Nonempty (InjectiveResolution M)` for every module.
- The fixed `sectionModuleEquivalence` is exact in `Evaluation.exact` and preserves
  injectives in `Evaluation.injectives`. Its forward functor is definitionally the existing
  `sectionsFunctor A`, so groups and restriction maps are unchanged.
- `Evaluation.tensor` and `tensor_value` identify relative internal tensor with section
  tensor and impose the identity on local pure tensors using the already published
  `comparison_internalTmul` and `comparison_sectionTmul`.
- `Evaluation.homIso` identifies the recorded equalizer Hom with the actual
  `SheafOfModules.homObj`. `hom_value` fixes this comparison by evaluation on every
  object of every slice: the image local map at `Over.mk f` acts on `y` by restricting
  the internal section along `f` and applying its actual equalizer evaluation `value`.
  This also uniquely fixes the comparison and its naturality in source and target.
- `hom A P` abbreviates `Mod.ihom' A.X (freeParameter A P)`. `freeParameter` is the
  existing free-abelian-sheaf/free-internal-module composite on the lifted representable.
  `generator` is only an abbreviation of the existing free adjunction's unit on a map
  of profinite spaces. No alternative free object is defined.
- `Evaluation.evaluate P S` is an isomorphism of functors into `AddCommGrpCat` from
  `hom A P ⋙ eval A S` to `eval A (Limits.prod S P)`. Its components are additive
  isomorphisms, and naturality in the module is part of `NatIso`.
- `tautological` fixes the forward map by restriction along the first projection and
  evaluation on the unit generator corresponding to the second projection.
  `value` uses `Mod.ihomDesc` on the identity and the lax tensor comparison of the
  sheaf inclusion; this is the actual evaluation, not an arbitrary pairing.
- `scalar` states the action through the section-ring restriction by the first projection.
  `restriction` states the product map `Limits.prod.map v (𝟙 P)` on the test variable.
  `parameter` states `Limits.prod.map (𝟙 S) v` for parameter precomposition.
  `pre A v` is the adjunction mate of the actual functorial free-module map, with both
  adjunctions the recorded equalizer `Mod.ihom'Adjunction`.
- `Evaluation.complexIso` is an isomorphism of full cochain complexes. Its
  `complex_component` is exactly `evaluate` in each degree. Consequently its chain
  equation is precisely the differential evaluated at the product, with no cohomology-only
  replacement. It is formulated for every complex, the direct termwise form of the
  already stated natural isomorphism, hence in particular every resolution.
- `complex_natural` is the chain-level naturality square for every chain map, including
  every map of resolutions and the given augmentation `s`. Evaluating its degree zero
  gives the given map `M(S×P) → I⁰(S×P)`; the source is concentrated in degree zero.
  In other degrees it is the corresponding zero map. Componentwise `restriction` and
  `parameter` apply to every term and every such chain map, so these identifications
  commute with both displayed restriction operations, including mixed compositions.
- `derived A P` is the recorded `rightDerivedFunctorOfQuasiIsoResolutions` of this
  specific additive internal Hom, with `enough` supplied by the published functorial
  K-injective replacement. `unit` is its canonical unit, not an arbitrarily chosen map.
- `Evaluation.computation` is the isomorphism from `RH_P(M[0])` to localization of the
  actual complex obtained by applying `H_P` to the given resolution. `computation_unit`
  fixes it by `computation.hom ≫ unit(I) = RH_P(Q(s))`; this determines the canonical
  comparison uniquely since `Q(s)` and the unit at a K-injective complex are invertible.
  `augmentation` says its composite with the unit at `M[0]` is exactly `Q(H_P(s))`.
  The fixed unit also ensures derived naturality for every commuting map of resolutions.
- No projectivity of `A[P]`, acyclicity of sections of `M`, or completeness assumption
  occurs anywhere.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CondensedInternalBarResolution`:
  `Profinite.CondensedAction.InternalBar.free`, `freeAdjunction`; these own the actual
  composite free functor and its generator unit.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`:
  `CategoryTheory.CondensedBar.Ring`, `Modules`, `sectionsFunctor`, `sectionRing`,
  `sections`, `sectionModule`, `freeParameter`. The corresponding already landed
  definition node is added to `stmt_deps` to cite their ownership. The graph below it
  was searched: no path back to this item was found.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`,
  `sectionModuleFunctor`, `sectionRingSheaf`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`:
  `internal_section_tensor_comparison`, `comparison_internalTmul`,
  `comparison_sectionTmul`; it supplies the fixed tensor and exactness interface.
- `Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom` and its public upstream
  import `WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom`:
  `CategoryTheory.Mod.nonempty_equalizerInternalHomAdjunction`, `ihom'`, `ihomDesc`,
  `ihom'Adjunction`; `Mod.tensorLeftMap` is the actual map between tensor functors.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj` and its slice-map section type. The universes are explicit.
- `Sheaf.CategoryTheory.SheafTensor`, publicly imported by the comparison module:
  `CategoryTheory.sfbSheafTensor_properties`; tensor means sheafified abelian tensor.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` through the above imports.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its unit.
  This is also the record of `sk-def-sfb-derived-categories`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CochainComplex.kInjectiveResolutionFunctor`, `toKInjectiveResolution`,
  `monoQuasiIso_toKInjectiveResolution_app` and the Grothendieck resolution instance.
- Proof imports include the recorded ringed-site Grothendieck theorem, equivalence
  preservation of limits/colimits, Grothendieck enough injectives, compact-Hausdorff
  quotient descent, section-module tensor closedness, and bounded-below injectives
  being K-injective. The proof dependency `lem-sfb-condensed-free-linearization-tensor`
  has no recorded module locally and thus contributes no invented proof import.
- `def-weil-size-convention` is recorded as a metatheoretic convention, not a declaration;
  its explicit universe choices are spelled out above.

Sources opened: the current blueprint `literature/blueprint/latest/`, direct-image stability
proof paragraph (3); `sites-modules.tex`, `lemma-internal-hom-adjoint-tensor` (03EO);
`sites-cohomology.tex`, `section-internal-hom`. The complete six-step node proof is copied
in mathematical prose into the primary theorem's docstring.

Edge cases checked before the statement: empty `P` and empty `S`, including the empty
cover of the empty space (sheaf sections there are zero); terminal `P` (the free regular
module, with evaluation returning the same section module); zero coefficient ring and
zero module; identity and composite parameter/test maps; the mixed product square;
resolution concentrated in degree zero for injective `M`; arbitrary nonzero higher
resolution cohomology of sections; negative degrees zero; and degree-zero augmentation.
No nonemptiness hypothesis or special choice of resolution excludes these cases.

Searches actually run with `msearch.py`:

- LeanFinder: `Internal Hom from free profinite module evaluated on products and arbitrary
  injective resolutions` returned eight hits, headed by `LightCondensed.ihomPoints` and its
  apply lemmas. These concern the light profinite site and constant coefficients, and do
  not state this arbitrary-ring internal-module resolution theorem.
- Loogle: `"ihomPoints"` returned four `LightCondensed.ihomPoints` declarations, likewise
  not an exact match.
- Mathlib grep: `ihomPoints|profiniteFree` in `Condensed` returned seven hits including
  `Condensed.profiniteFree` (a constant-ring free functor) and the light internal-Hom API.
- Project searches by `rg` covered `profiniteFree`, `freeYoneda`, `resolutionEvaluation`,
  `profinite.*[Hh]om`, `[Hh]om.*[Pp]rofinite`, `ihomPoints`, `freeParameter`,
  `InternalFunctions` in `lean/WeilConjectures` and `lean/Sheaf`, and a node-id search in
  `WeilConjectures`. Existing freeParameter was reused; no exact theorem was found.

No natural-language statement correction, disputed mathematical assertion, new node,
or dependency-record repair is needed. Only the existing owning definition node is
added to the item's statement dependencies.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
