## Worker report

Item: `lem-trf-relation-incidence-open-model`, group Q62, stage 2.

The delivery adds `Sheaf.AlgebraicGeometry.RelationIncidenceOpenModel`, with the
single theorem `AlgebraicGeometry.Scheme.relation_incidence_open_model`. Its only
proof is `sorry`. There are no definitions, auxiliary theorems, new nodes, dependency
repairs, or changes to the natural-language statement. The copied node changes only
in `lean`. All variables and the universe `u` are explicitly bound;
`set_option autoImplicit false` checks this.

Source read: `literature/stacks-project/spaces.tex`, the full statement and proof of
`lemma-finding-opens` (Tag 02WU), starting at line 1310. The item is the incidence
part of that proof after choosing a map to the presenting scheme. It retains the
source's flat, locally finitely presented hypotheses, without assuming that `g` is
surjective or that the relation is étale.

The earlier Q16 PASS is the node's stage-1 `reviewed` record. The current node has
no `lean` or `reviewed_lean` record and no repair note. Thus it is a stage-2 item;
that stage-1 proof review is not an existing Lean statement or a duplicate delivery.

### Every hypothesis and construction

- A scheme `S`: `{S : Scheme.{u}}`, using Mathlib's scheme definition.
- The three `S`-schemes: `{R U U' : Over S}`. All morphisms in the statement are
  morphisms in this slice, so they are the required `S`-morphisms.
- The projections of `j`: `(s t : R ⟶ U)`; the product in the slice is the fibre
  product over `S`, and `prod.lift s t` is exactly `j`.
- Identifying `R(T)` with an equivalence relation: `[Mono (prod.lift s t)]`
  gives injectivity on every test object, and `hrel` states reflexivity, symmetry
  and transitivity of the relation whose witness is an actual `r : T ⟶ R`
  with the prescribed two endpoints. Together these say precisely that `j(T)`
  identifies `R(T)` with an equivalence relation, for every `S`-scheme `T`.
- Surjectivity, flatness and local finite presentation of `s`:
  `[Surjective s.left] [Flat s.left] [LocallyOfFinitePresentation s.left]`.
- The same three hypotheses on `t`: the corresponding instances on `t.left`.
- The map `g`: `(g : U' ⟶ U) [Flat g.left]
  [LocallyOfFinitePresentation g.left]`. No surjectivity instance is imposed.
- The incidence scheme `E`: `pullback g s` in `Over S`; its underlying scheme is
  `(pullback g s).left`. Its map `p` is `(pullback.snd g s ≫ t).left`.
- The restricted relation `R'`:
  `pullback (pullback.snd g s ≫ t) g`. Its first endpoint is
  `pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s`, and its second
  endpoint is `pullback.snd (pullback.snd g s ≫ t) g`. These are the actual
  iterated pullback and projections, not an independent abstract relation.
- The big fppf site is `Scheme.fppfTopology.over S` on `Over S`.
- The presheaf `U(-)/R(-)` is the presheaf coequalizer of `yoneda.map s` and
  `yoneda.map t`. Functor-category coequalizers in types are pointwise; since
  `hrel` is an equivalence relation, this is the ordinary relation quotient.
  The coequalizer for `R'` uses precisely the two restricted endpoints above.
- The two quotient sheafifications are `F` and `F'`, sheaves on that site;
  `η` and `η'` are maps from the respective coequalizers. `hη` and `hη'`
  state their universal properties: precomposition gives a bijection to the
  maps from each quotient presheaf to every sheaf. This is the universal
  property defining sheafification in `def-weil-pbc-sheafification`, also used
  by the existing kernel-pair and finding-opens modules. It does not impose
  a global small-valued sheafification instance on the large category.
- Representable functors `h_X`: `yoneda.obj X` on the slice category.
- The quotient map `q`: `coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η`.
  The analogous composite with `η'` is `q'`.
- The canonical map: `(α : F'.obj ⟶ F.obj)` with `hα` expressing
  `q' ≫ α = yoneda.map g ≫ q`. This specifies the canonical induced map
  uniquely: cancel the epi coequalizer projection and use injectivity in
  `hη'` with target `F`. Hence this is not a replacement by an arbitrary map.
- Sectionwise injectivity: `hα_injective : ∀ T : Over S,
  Function.Injective (α.app (op T))`, exactly the node's assumption.

### Every conclusion

- Flatness of `p`: `Flat (pullback.snd g s ≫ t).left`.
- Local finite presentation of `p`:
  `LocallyOfFinitePresentation (pullback.snd g s ≫ t).left`.
- Its set-theoretic image is open: the conclusion supplies `W : U.left.Opens`
  with `(W : Set U.left) = Set.range (pullback.snd g s ≫ t).left`.
  Thus it supplies precisely the image, equipped with its open subscheme
  structure `W.toScheme`, without using an unspecified chosen scheme.
- Its factor through the open: an actual scheme map
  `pW : (pullback g s).left ⟶ W.toScheme`, with
  `pW ≫ W.ι = (pullback.snd g s ≫ t).left`. This equation determines `pW`
  uniquely because `W.ι` is an open immersion and therefore a monomorphism.
- The factor is surjective, flat and locally of finite presentation:
  `Surjective pW ∧ Flat pW ∧ LocallyOfFinitePresentation pW`.
- Every `v : V → U`: the family is indexed by all `(V : Over S) (v : V ⟶ U)`.
  Its open `W_V` is `v.left ⁻¹ᵁ W`; the representing `S`-scheme is exactly
  `Over.mk ((v.left ⁻¹ᵁ W).ι ≫ V.hom)`. No open-cover or affine restriction
  is made on `V` or on the test schemes of its representable.
- The required natural isomorphism over `h_V`: the conclusion supplies `β V v`
  from this representable to `F'.obj` and asserts the square
  `IsPullback (yoneda.map (Over.homMk (v.left ⁻¹ᵁ W).ι rfl)) (β V v)
  (yoneda.map v ≫ q) α`. The pullback universal property is equivalent to
  an isomorphism from this representable to `h_V ×_F F'` whose first projection
  is the given open inclusion. This is an isomorphism of presheaves, hence
  natural on all test `S`-schemes, not merely a collection of pointwise bijections.
  Both representables are sheaves for the subcanonical fppf topology; limits
  of sheaves are computed as presheaf limits. Thus it is also the asserted
  sheaf isomorphism. `IsPullback.isoPullback` is the existing Mathlib construction
  extracting that isomorphism, including its equation over `h_V`.
- Compatibility with every `V₁ → V` over `U`: the last universally quantified
  clause uses `(k : V₁ ⟶ V)` and the composite `k ≫ v`. A map `kW` between
  the two actual open preimages is characterized by its commuting square with
  their open inclusions. For every such `kW`, the equality
  `yoneda.map kW ≫ β V v = β V₁ (k ≫ v)` is asserted. These `kW` exist:
  restrict `k.left` to the inverse image of `v.left ⁻¹ᵁ W`, using
  `AlgebraicGeometry.morphismRestrict`, and equip it with its inherited map to
  `S`. The source open is exactly `(k ≫ v).left ⁻¹ᵁ W`. They are unique since
  the target inclusion is mono. Quantifying over the commuting square therefore
  states compatibility for the canonical restriction map and is not vacuous.
  Together with that first-coordinate square, the displayed equality is exactly
  commutativity of the induced comparison isomorphisms into the fibre products.
  Their inverses commute as well, by invertibility.

### Dependency declarations and imports

Every node in `stmt_deps` was opened, including its full statement and Lean record
or Mathlib match. The recorded source signatures and docstrings were read.

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, declarations
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`. The delivered statement uses
  these through `Mathlib.AlgebraicGeometry.Pullbacks`, which supplies the scheme
  pullbacks, and the standard slice-category limits.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; its stalkwise equivalence `Flat.iff_flat_stalkMap`
  matches the node's definition.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicGeometry.Scheme.fppfTopology`, with the slice construction
  `CategoryTheory.GrothendieckTopology.over` from `Mathlib.CategoryTheory.Sites.Over`.
- `def-weil-pbc-sheafification`: `Mathlib.CategoryTheory.Sites.Sheafification`,
  `CategoryTheory.presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`.
  Their universal property is rendered by `hη` and `hη'` for the two specified
  quotient presheaves, as in the already recorded kernel-pair theorem.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`. The actual open subscheme and inclusion are
  `W.toScheme` and `W.ι` from `Mathlib.AlgebraicGeometry.Restrict`.

The available proof dependencies are imported without `public`: the generic site
axioms, the monomorphic-relation kernel-pair theorem, the local sheafification
sections theorem, and `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`.
The remaining geometric proof dependencies are in the public Mathlib imports.
No parent finding-opens/quotient theorem is imported; there is no circular use
of the assertion this item supports. The theorem docstring gives all seven
proof steps and their DAG dependencies.

### Edge cases checked before writing

- Empty `U'`: `E` and its image are empty. Its map onto the empty open is
  surjective and fppf, and the representing open is empty for every `V`.
- Empty `U` or empty test scheme: all constructions still exist. The empty
  test has its unique map to every scheme and a unique section in every sheaf,
  as forced by the empty fppf covering; no nonempty binder excludes this case.
- `g = id`: surjectivity of `t` makes `W = U`, and the restricted quotient is
  canonically the original quotient. The square then represents all of `h_V`.
- Diagonal relation and `g` an open immersion that is not surjective: the
  restricted quotient is that open; `W` is precisely its image, not all of `U`.
- Diagonal relation and `g` a noninjective flat locally finitely presented cover
  of its image: the restricted relation is the kernel pair of `g`, not the
  diagonal of `U'`. Thus the quotient has the right image and the formalization
  does not accidentally require `g` to be mono.
- Arbitrary `V₁ → V`, including identities, open inclusions, maps with empty
  inverse image and maps that are not flat: the last clause has no extra property
  on `k`; the canonical open-preimage map is determined by its inclusion square.
- Universe `u` is arbitrary, all scheme and test objects use `Scheme.{u}`,
  and the Yoneda values are `Type u`, consistently with the existing sibling
  quotient interfaces. No independent smaller test universe or equality of
  otherwise independent site universes has been added.

### Searches

- `msearch.py`, LeanFinder, query
  `incidence open model for the quotient sheaf of an fppf equivalence relation`:
  eight hits on locally-ringed-space coequalizers and gluing, including
  `LocallyRingedSpace.HasCoequalizer.imageBasicOpen_image_open`; none states
  this quotient-sheaf representation or its pullback compatibility.
- `msearch.py`, Loogle, query
  `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`:
  twelve hits including `UniversallyOpen.of_flat`, `IsOpenImmersion.of_flat_of_mono`
  and fppf coverage facts. These give geometric ingredients, not the item.
- `msearch.py`, grep, query `incidence|quotient.*relation|relation.*quotient`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py`, LeanSearch, query
  `The open incidence image for a flat locally finitely presented equivalence relation
  represents the pullback of the restricted fppf quotient sheaf`: eight hits,
  including `pullbackRestrictIsoRestrict` and `UniversallyOpen.of_flat`, with
  no statement of this incidence quotient model.
- `rg` in the project's `lean/WeilConjectures/` for
  `relation_incidence_open_model|incidence.*[Qq]uotient|[Qq]uotient.*incidence`
  and for the item id: no existing statement of the item.
- `rg` in `lean/Sheaf/AlgebraicGeometry/` for quotient/relation constructions
  found `EtaleRelationKernelPair`, `EtaleRelationRestrictionQuotient`,
  `EtaleRelationQuotient` and `EtaleRelationFindingOpens`. Their source was read.
  None states this incidence-open model. The parent finding-opens theorem states
  representability of `α` by open immersions for arbitrary maps to `F`, without
  identifying the actual incidence image or its fppf factor; it is not an exact
  existing declaration for this node. The restriction module's helper definitions
  are the very same Mathlib iterated pullback expressions used here; no second
  definition of that construction is introduced.

No statement dispute or node correction is needed.

### Validation

`scompile.py Q62 lem-trf-relation-incidence-open-model` compiled the delivered
module on the server against the live published library, with no errors or
unexpected warnings. The delivery dry run passed the server preflight and
per-file compilation (`OK (dry run)`, candidate `b85ab4ca258`). A local packet
check also confirmed that `lean` is the only changed node field, the recorded
signature matches the source verbatim, every Lean line has at most 100 characters,
and the sole postponed proof is the item's theorem.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
