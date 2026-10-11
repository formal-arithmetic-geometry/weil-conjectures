## Worker report

The module states `AlgebraicGeometry.Scheme.Modules.module_open_restriction_injectives`;
its sole proof is `sorry`. No definitions or auxiliary nodes are needed, and no statement
correction is made.

Hypotheses and clauses:
- `X : Scheme.{u}` is the arbitrary scheme; `U : X.Opens` is its arbitrary open subscheme,
  represented by `U.toScheme`, with inclusion `U.ι`. No finiteness, separatedness, or
  nonemptiness assumption is imposed.
- `R := restrictFunctor U.ι` is precisely restriction of modules and morphisms, using
  the dependency's Mathlib functor. `restrictAppIso` and `restrict_map` describe its
  sections and restriction maps. Direct image is `pushforward U.ι`, whose sections
  are on preimages (`pushforward_obj_obj`), namely intersections with U.
- Clause (1), additivity: `R.Additive`. Exactness at the middle: for every
  `S : ShortComplex X.Modules`, `S.Exact → (S.map R).Exact`. ShortComplex bundles
  both arrows and their zero composite, and Exact is the dependency's notion.
- Clause (2): `∀ I : X.Modules, Injective I → Injective (R.obj I)`.
- Clause (3): `∀ J : U.toScheme.Modules, Injective J →
  Injective ((pushforward U.ι).obj J)`.
- Consequence: for every F and `I : InjectiveResolution F`, there exists a resolution J
  of `R.obj F`. The equality h fixes its whole cocomplex to the mapped cocomplex,
  including every differential. The final equality fixes its degree-zero augmentation
  to the restricted augmentation, transporting its target along h. Mathlib's single₀
  augmentation has only the degree-zero component to specify.

Dependency declarations read and used:
- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme (imported transitively).
- def-weil-sheaf-of-modules-category: `SheafOfModules`, Mathlib.Algebra.Category.ModuleCat.Sheaf;
  `Scheme.Modules` specializes it to the structure sheaf and has Mathlib's abelian instance.
- lem-weil-pbc-module-restriction-open-immersion-colimits:
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, `restrictAdjunction`, and
  `pushforward`, Mathlib.AlgebraicGeometry.Modules.Sheaf. Its quasi-coherence clause
  is not needed in the present statement; the signature of
  `Scheme.Modules.isQuasicoherent_restrictFunctor` in Modules.Tilde was also read.
- def-sp-injective-resolutions: `CategoryTheory.Injective` (Basic) and
  `CategoryTheory.InjectiveResolution` (Resolution), Mathlib.CategoryTheory.Preadditive.Injective.
- def-weil-pbc-exact-sequence: `CategoryTheory.ShortComplex.Exact`, imported through
  the recorded module Mathlib.Algebra.Homology.ExactSequence.
- The upstream extension module WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
  provides restriction's Additive instance, needed to form mapped complexes. This is
  existing implementation data, not a new hypothesis.

Edge cases: U may be empty or all of X, and X may be empty. Zero modules and zero
resolutions are included. No point is selected and no degree is excluded (complexes are
ℕ-indexed as in the recorded InjectiveResolution specialization). Universe u is explicit
and consistent with Scheme.Modules; there are no auto-bound variables.

Searches (2026-10-11):
- msearch leansearch, "restriction of injective sheaves of modules to an open subset":
  unavailable (service Internal Server Error); no mathematical verdict attached.
- msearch leanfinder, "Restriction of sheaves of modules to an open subscheme is exact
  and preserves injectives": eight hits, including restrictFunctor, restrict, abelian
  module categories, and faithful pushforward; none states all the clauses.
- msearch loogle, `AlgebraicGeometry.Scheme.Modules.restrictFunctor, CategoryTheory.Injective`:
  zero hits.
- msearch grep, `restrictFunctor|InjectiveResolution`, AlgebraicGeometry/Modules:
  restriction functor, its adjunction, and quasi-coherence, no matching theorem.
- rg over WeilConjectures and lean/Sheaf for `module-open-restriction-injectives`,
  restriction/injective, and restrictFunctor; upstream contains Additive and limit
  preservation instances, but no theorem for all clauses. Project RingedSpace
  `restrict_injectiveResolution` states only the resolution clause in a different
  presentation, not this node. The upstream name index was searched too.

Sources opened: https://stacks.math.columbia.edu/tag/01E1 and
https://stacks.math.columbia.edu/tag/02N5 (the literature checkout lacks cohomology.tex).
01E1 states preservation of injectives by open restriction and its proof gives the
resolution consequence. 02N5 gives injective direct image for flat maps. The node's
stalkwise proof and adjunction arguments are included in the declaration docstring.
No disputed statement or node fault found.

## Second reading by E1

Read the delivered node and Lean independently, then opened all five statement
 dependency nodes and the actual declarations below. No statement correction,
new definition node, or dependency module is present or needed.

Object/hypothesis/conclusion checklist (H3):

- Arbitrary scheme X: `(X : Scheme.{u})`; verdict: exact. Read `Scheme` in
  Mathlib/AlgebraicGeometry/Scheme.lean, the locally ringed space with affine
  neighbourhoods; no field, characteristic, or finiteness assumption.
- Open subscheme U with inclusion j: `(U : X.Opens)`, `U.toScheme`, `U.ι`;
  verdict: exact. The inclusion's open-immersion instance supplies precisely
  the structure attached to an open, with no extra hypothesis on X or U.
- O_X- and O_U-modules and linear morphisms: `X.Modules` and
  `U.toScheme.Modules`; verdict: exact. Read the Mathlib `Modules` definition
  and abelian instance (Modules/Sheaf.lean:39 onwards), and `SheafOfModules`
  and its `Hom` (ModuleCat/Sheaf.lean:33 onwards). These use the dependency's
  ring-sheaf module category, not quasi-coherent modules or abelian sheaves.
- Restriction of objects and arrows: `let R := restrictFunctor U.ι`;
  verdict: exact. Read `restrictFunctor`, `restrict_obj`, `restrict_map`, and
  `restrictAppIso` in Mathlib/AlgebraicGeometry/Modules/Sheaf.lean. For an open
  inclusion its image-open evaluation is G(W), with the induced O_U-action.
  Read the dependency's `restrictAdjunction` signature (restriction LEFT
  adjoint to direct image, despite that declaration's misleading docstring),
  and `isQuasicoherent_restrictFunctor` in Modules/Tilde.lean:576; the latter
  is not needed and quasi-coherence is correctly not a hypothesis here.
- Direct image j_*: `pushforward U.ι`; verdict: exact. Read its definition,
  `pushforward_obj_obj`, and `pushforward_map_app`: evaluation on W is the
  original module on j-preimage(W), i.e. W intersect U, with scalar restriction.
- Clause (1), additive: `R.Additive`; verdict: exact. The upstream extension
  module supplies this instance at line 669, with sectionwise `map_add := rfl`.
  This is existing functor structure, not an added assumption. That import
  also permits `S.map R` and `R.mapHomologicalComplex` to elaborate.
- Clause (1), exact at the middle: `∀ S : ShortComplex X.Modules,
  S.Exact → (S.map R).Exact`; verdict: exact. Read `ShortComplex` and `map`
  in Basic.lean, `ShortComplex.Exact` in Exact.lean, and
  `exact_iff_image_eq_kernel` in CategoryTheory/Abelian/Exact.lean:94.
  Its bundled arrows have zero composite and exactness means Im = Ker;
  all consecutive triples of any finite or infinite complex are included.
- Clause (2): `∀ I : X.Modules, Injective I → Injective (R.obj I)`;
  verdict: exact. Read `Injective.factors` in Injective/Basic.lean:32:
  extension of every map along every monomorphism is the node's surjectivity
  of contravariant Hom. No restriction on the injective object is added.
- Clause (3): `∀ J : U.toScheme.Modules, Injective J →
  Injective ((pushforward U.ι).obj J)`; verdict: exact, same injective notion
  on the two actual module categories, in the correct direction.
- Consequence: `∀ (F : X.Modules) (I : InjectiveResolution F), ∃ J ...`;
  verdict: exact. Read `InjectiveResolution` in Resolution.lean:43–55,
  including its degreewise injectivity and quasi-isomorphic single-zero
  augmentation. The dependency explicitly identifies this with the usual
  nonnegative indexing of a bounded-below resolution. The equality `h`
  fixes the entire restricted cocomplex, including differentials; the final
  equation identifies the degree-zero augmentation after target transport
  by `eqToHom (congrArg (fun K ↦ K.X 0) h)`. All positive-degree components
  of a single-zero augmentation are forced zero, so none is omitted.

Source reading: the local literature checkout has no stacks-project directory.
Fetched the actual Stacks `cohomology.tex` and `modules.tex` into this item's
scratchpad from https://raw.githubusercontent.com/stacks/stacks-project/master/.
Read `lemma-cohomology-of-open` (01E1), including the whole proof and restricted
resolution consequence; `lemma-pushforward-injective-flat` (02N5);
`lemma-exactness-pushforward-pullback` (01AJ); and `lemma-j-shriek-exact` (01AK).
Also opened https://stacks.math.columbia.edu/tag/01E1 and
https://stacks.math.columbia.edu/tag/02N5. The source works for arbitrary ringed
spaces and open subspaces; specializing to the node's schemes adds no hidden
hypothesis. Flatness in 02N5 is automatic for the open inclusion. The module
proof docstring follows all four node steps: stalkwise restriction exactness,
stalkwise extension-by-zero exactness and its adjunction, the restriction/direct
image adjunction, and termwise restriction of the augmented resolution.

Edge cases: U = bottom and U = top, empty X, zero F/I/J, and degree zero are
all allowed. There is no index-set/nonemptiness requirement; no characteristic
assumption or selected point; the zero-composite condition includes zero arrows.
Universe u is bound explicitly; `Scheme.Modules` uses the recorded dependency's
u-small module convention, and raising u accommodates any larger sheaf universe.
Every variable in the signature is bound. There are no extra typeclass binders.

Independent H4 searches, with wording different from the first reader:
- msearch leansearch: `open restriction functor preserves injective module objects`:
  unavailable, Internal Server Error; no mathematical verdict inferred.
- msearch leanfinder: `exact open immersion restriction module sheaf injective
  resolution direct image`: eight hits, mainly restrict/restrictFunctor,
  restrict_obj/restrict_map, and unrelated locally-injective sheafification;
  none states this node's conjunction.
- msearch loogle: `AlgebraicGeometry.Scheme.Modules.pushforward,
  CategoryTheory.Injective`: zero hits.
- rg on Mathlib/AlgebraicGeometry, upstream WeilConjectures, project lean/Sheaf,
  and dag/lean_names_upstream.json for open_restriction_injectives,
  restrict/injective in either order, pushforward/injective in either order,
  and restrict_injectiveResolution. No existing declaration states the item.
  Opened project `RingedSpace.restrict_injectiveResolution`: only the resolution
  consequence, using `SheafOfModules.overFunctor`, without clauses (1) and (3).
  Opened `flat_module_pullback_exact_pushforward_injective`: a flat-morphism
  tensor-pullback theorem, without open restriction preserving injectives or
  the restricted resolution. Neither is a duplicate of this item. The upstream
  TopCat/etale injectivity hits concern different coefficient categories.

Mismatches/changes: none in the Lean or node. Preserved both verbatim and added
this independent reading. No hollow definitions: the delivery defines none.
Only the named theorem has `sorry`, as stage 2 requires. Source/blueprint tags,
namespace, imports, and the proof docstring comply with H5–H9. Verified the
node's `lean.statement` is verbatim the file signature and all lines are at
most 100 characters. scompile on the absolute sandbox module path succeeded
in 1.7 seconds with no errors or warnings. The first invocation used a relative
path from the read-only repository and failed before compilation; corrected
that invocation to the absolute sandbox path, without changing tools or sources.

## Review fix by R-mor1148 (stage 2)

The delivery stated restriction to U with Mathlib's `Scheme.Modules.restrictFunctor U.ι`
(into `U.toScheme.Modules`) and direct image with `pushforward U.ι`. Open restriction of
O_X-modules is the project convention `SheafOfModules.overFunctor X.ringCatSheaf U` /
`M.over U` / `Hom.over` (C1 d9e3a07ba, G1 9abd41a1b module-extension-by-zero-adjunction,
M1 lem-sc-ringed-space-restrict-injective-resolution), one notion per H4/H12. Restated:
(1) `(overFunctor X.ringCatSheaf U).Additive` (the shared `moduleOverFunctor_additive`
instance of Sheaf.Paper.DerivedHomMayerVietoris supplies the zero-morphism structure needed
by `S.map`/`mapHomologicalComplex`, imported, not restated) and short-complex exactness;
(2) `Injective I → Injective (I.over U)`; (3) J an injective module over `𝒪_X.over U`,
j_* J as Mathlib's right adjoint of restriction
`SheafOfModules.pushforward (SheafOfModules.pushforwardOver U)` (`overPushforwardOverAdj`,
sections J(W ∩ U)); the resolution consequence in M1's landed form with `F.over U` and
`(I.ι.f 0).over U`. Module binders are `SheafOfModules.{u} X.ringCatSheaf` (= `X.Modules`
by `rfl`), so `S.map` finds the zero-morphism instance. Compiled clean on L's mirror.
