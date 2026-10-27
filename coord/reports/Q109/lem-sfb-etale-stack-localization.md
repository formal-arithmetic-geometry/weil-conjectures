## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleStackLocalization` states
`CategoryTheory.etaleStack_localization`, with its sole proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The source is Stacks `stacks.tex`, section-localize (04WT), Constructions A and B,
and lemma-localize-stacks (04WV), read in full in the supplied literature.

Clause-by-clause correspondence:

- The schemes and arbitrary base morphism are `{S S' : Scheme.{u}} (g : S ⟶ S')`.
  There is no algebraicity, finiteness, flatness, smoothness, or separation binder.
- The size convention is explicit `universe u v₁ w₁ v₂ w₂`. Schemes have object
  universe `u+1` and hom universe `u`; total categories independently use
  `BasedCategory.{v₁,w₁}` and `BasedCategory.{v₂,w₂}`. No equality between
  their universes is imposed. The theorem can be instantiated at each chosen bound.
- `Sch/S` and `Sch/S'` are `Over S` and `Over S'`. Composition with `g` is
  Mathlib's `Over.map g`, whose object structure map is `a ≫ g` and whose
  arrows retain the original underlying scheme arrow.
- The represented `h_S` in the node's specified slice model is
  `BasedCategory.ofFunctor (Over.map g)`. The first conjunct asserts it is an
  `IsModuliStack`; the second asserts `IsRepresentedByScheme` with the particular
  scheme `Over.mk g`. Its fibres are discrete: above a fixed scheme the only
  arrow of the slice with underlying identity has identical structure maps.
  The representation predicate gives the equivalence with
  `discreteModuli (yoneda.obj (Over.mk g))`, in precisely the dependency's sense.
- The `∀ F` conjunct uses `IsModuliStack F` for the node's stack hypothesis.
  Its composite is literally `BasedCategory.ofFunctor (F.p ⋙ Over.map g)`;
  `ofFunctor` keeps `F.obj`, its category instance, and every arrow. The forward
  implication is Construction A. Its morphism `p` to `h_S` is the real term
  `({toFunctor := F.p, w := rfl} : BasedFunctor
  (BasedCategory.ofFunctor (F.p ⋙ Over.map g))
  (BasedCategory.ofFunctor (Over.map g)))`, requiring no choice or new definition.
- The `∀ G q` conjunct quantifies over every stack over `S'` and every morphism
  `q : BasedFunctor G (BasedCategory.ofFunctor (Over.map g))`. The field `q.w`
  is exactly `q.toFunctor ⋙ Over.map g = G.p`, the map-over-the-base condition.
  Its right hand side `IsModuliStack (BasedCategory.ofFunctor q.toFunctor)`
  is Construction B: the same total category projected by `q` to `Sch/S`.
- The two displayed iff statements combine the forward construction with its
  inverse; the reverse implications follow from the opposite construction in
  04WV. They add no assumption or extra case. At objects the composites are
  exactly inverse: A then B projects by `F.p`; B then A projects by
  `q.toFunctor ⋙ Over.map g = G.p`. The unchanged total category is built into
  `BasedCategory.ofFunctor`, rather than merely asserted equivalent.
- The last conjunct provides an equivalence `E` between the category
  `BasedFunctor F F'` of 1-morphisms over `S` and the full subcategory of based
  functors between the composite projections whose condition is
  `h.toFunctor ⋙ F'.p = F.p`. This is exactly the commuting triangle over `h_S`.
  Its homs are `BasedNatTrans`: natural transformations projecting to identities.
  Because the projections are fibred in groupoids, all these transformations are
  invertible, so this describes natural isomorphisms (2-morphisms), not any extra
  noninvertible 2-cells. Compatibility with `h_S` follows from faithfulness of
  `Over.map g`: an arrow in a slice is determined by its endpoints and underlying
  arrow. This is the dependency's `ModuliTwoIso` convention, also represented by
  isomorphisms in the category of based functors via Mathlib's `BasedNatIso`.
- The four normalizations state that `E.functor` and `E.inverse` retain each
  underlying functor and each underlying natural transformation. `HEq` on maps
  handles equality of dependent endpoint types; it is not a weakening of the
  asserted unchanged component maps. These normalizations force the two maps
  to be inverse on the actual 1- and 2-cell data. Identities, vertical composition,
  and horizontal composition agree, since the forgetful maps to functors and
  natural transformations are faithful and those operations use the same data.
  This is a componentwise formulation of the inverse 2-category equivalences,
  covering arbitrary pairs as well: take `F = ofFunctor q.toFunctor`.
- `IsModuliStack` is used without alteration. Its definition is fibred in
  groupoids plus colimiting descent cocones on every covering sieve for
  `Scheme.etaleTopology.over S`. As its recorded docstring explains, this is
  effective object descent together with unique descent of isomorphisms. Thus
  jointly surjective étale families are the coverings throughout, without any
  restriction to small étale objects or replacement by isomorphism classes.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `ModuliTwoIso`, `discreteModuli`,
  `IsRepresentedByScheme`, `IsModuliStack`. The complete signatures and
  docstrings of the relevant general stack vocabulary were inspected.
- That dependency imports Mathlib's
  `Mathlib.CategoryTheory.FiberedCategory.BasedCategory`: `BasedCategory`,
  `BasedCategory.ofFunctor`, `BasedFunctor`, `BasedNatTrans`, and their hom
  categories and bicategory structures. Their definitions were read directly.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over.map`; existing
  `ObjectProperty.FullSubcategory` and category equivalences are reused.
- `def-weil-size-convention` is a recorded metatheoretic convention, with no
  declaration to import; explicit universe levels implement it here.
- Proof-only import:
  `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`,
  `AlgebraicGeometry.smallEtaleRepresentablePresheaf_isSheaf` (full source read).
  It is applied on `T_et` to `T ×[S'] S`, not incorrectly to an arbitrary object
  of the small site. No étaleness of `g` is required.
- Proof-only import: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and universal property.

The theorem docstring reproduces all seven proof steps from the node, including
both fibred-axiom checks, both isomorphism-sheaf checks, both object-descent
checks, and the inverse action on morphisms and 2-morphisms.

Edge cases checked before finalizing: `g = id` gives the identity localization;
empty `S` gives the empty represented sheaf, retaining its required object over
the empty test scheme; the empty covering on the empty scheme is still included
by the covering-sieve definition. An empty total category is not silently assumed
to be a stack on that empty test scheme. For two different maps `a,b : T → S`,
isomorphisms in the composite can only occur on tests where `a` and `b` agree,
which is why representable descent is used in the proof. Nonseparated `g` is
allowed. Arbitrary independent total-category sizes and nontrivial automorphism
groups remain in scope.

Searches made with the supplied msearch wrapper:

- LeanFinder: `Etale stacks on a slice site are equivalent to stacks with a
  morphism to the representable stack`: eight hits, chiefly `Scheme.Etale.forget`,
  its full/faithful instances, and small/big étale topologies. No localization of
  groupoid-valued stacks with their 1- and 2-morphisms.
- Loogle: `CategoryTheory.Pseudofunctor.IsStack, CategoryTheory.Over`: two hits,
  `Pseudofunctor.IsStack.essSurj_of_sieve` and `.mk`, both about a fixed
  pseudofunctor's descent rather than changing its base.
- Mathlib grep, CategoryTheory:
  `locali[sz].*[Ss]tack|[Ss]tack.*locali[sz]`: zero hits.
- LeanSearch: `Stacks on a slice site are equivalent to stacks mapping to the
  representable sheaf`: eight hits including `GrothendieckTopology.yonedaEquiv`,
  fixed-pseudofunctor descent, and dense-subsite equivalences for set/category
  valued sheaves. No exact declaration of this CFG localization.
- Project `rg` on `lean/WeilConjectures` and `lean/Sheaf` for localization/stack
  combinations and the node id: downstream
  `AlgebraicStackChangeBaseToIntegers` and `StackSmoothAtlasBaseChange` cite this
  node but do not state the unrestricted theorem. The former's helpers are not
  duplicated or imported (doing so would invert the intended dependency).
  `ModuliSchemeBaseChange` was also read; it constructs an iso-comma restriction,
  not the same-total-category localization equivalence stated here.
- The upstream-name index has no `etaleStack_localization` declaration.

Validation: the module passed the prescribed scompile server check in both
sandbox and library module contexts. No errors or unexpected warnings remain.
Only the one named theorem has `sorry`. No disputed statement or node fault found.

## Second reading by Q109

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
