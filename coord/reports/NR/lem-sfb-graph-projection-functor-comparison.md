## Worker report

The module `Sheaf.AlgebraicGeometry.GraphProjectionFunctorComparison` states
`AlgebraicGeometry.graph_projection_functor_comparison`, with its whole proof `sorry`.
It also defines the two composites `RelativeGraphComparison.first` and `.second`, the
node's restricted projections k_D and l_D. Both definitions contain actual data. They
are helpers for this node, using the existing graph projection maps, rather than a new
notion of closed subscheme, graph, morphism presheaf, or representability.

Read the assigned node, all seven statement-dependency nodes and their recorded source
signatures/docstrings, the Yoneda proof dependency, and Stacks `quot.tex`, Tags 0D1A and
0D1B, labels `lemma-Mor-into-Hilb` and `lemma-Mor-into-Hilb-open`, lines 3139–3196.
The theorem is the node's conditional formal comparison. The source's geometric
hypotheses establish its graph and open-locus inputs in the parent; they are not
additional assumptions in this formal comparison.

Hypotheses, individually:

- `Z X S : Scheme.{u}`, `z : Z ⟶ S`, `x : X ⟶ S` introduce exactly the schemes and
  structure morphisms. No properness, flatness, finite presentation, or separatedness
  is added.
- `relativeMorphismsPresheaf z x` is the recorded morphism presheaf. Its convention
  uses `T ×_S Z` for Z_T, and describes a T-map Z_T → X_T by its component to X over S.
  This is the equivalent convention explicitly supplied by the dependency node.
- `F : (Over S)ᵒᵖ ⥤ Type u` is the set-valued presheaf on S-schemes. `I T` encodes
  each of its elements as Mathlib `IdealSheafData` on `(Z ×_S X)_T`. `hinj` expresses
  that these elements are a collection of closed subschemes, with no additional labels.
  The closed inclusion j_D is `(I T D).subschemeι`. Ideal sheaves retain the entire
  scheme structure, including nilpotents, and are not merely closed subsets.
- `hI` is exactly restriction by pullback: `I T' (F.map h.op D)` equals the comap of
  the ideal along the existing `baseChangeMap`. It uses the canonical map, not an
  arbitrary morphism. Since each F(T) is a collection of ideals in a Type u set,
  the same small-set convention as the recorded relative morphism presheaf applies.
- `γ` is a natural transformation from the recorded morphism presheaf to F.
  `hγ` states, for every test scheme and morphism, that the actual recorded graph map
  is a closed immersion and its kernel ideal is precisely the family encoded by γ.
  Closedness is explicitly included so that taking the kernel cannot replace a
  nonclosed graph by its closure.
- The last conjunct is conditional on `U T D : T.left.Opens` and the universal
  test-map equivalence in the node. The equivalence is stated for every S-scheme T'
  and every h : T' → T. Factorization is `∃ a, a ≫ (U T D).ι = h.left`, with no
  restriction on h. Quantifying over all assignments U expresses the supplied
  universally characterized open loci without choosing them from a sorry theorem.

Conclusions, individually and in file order:

1. `∀ T, Function.Injective (γ.app (op T))` is injectivity on every test scheme.
2. `(∃ f, γ.app (op T) f = D) ↔ IsIso (first z x T (I T D))` is precisely the
   graph/image criterion for every closed family.
3. For every isomorphism `e` whose hom is k_D, `∃! f` states the unique inverse image,
   with `f.left = e.inv ≫ second ...`. This is l_D composed with k_D inverse, in
   Lean's diagrammatic composition order. Its component to X, together with its
   inherited map to T, is the claimed T-morphism into X_T.
4. For every D, `L : Subfunctor (yoneda.obj T)` has membership exactly the condition
   that the first projection of `F.map h.op D` is invertible. The isomorphism from
   `pullback (yonedaEquiv.symm D) γ` to `L.toFunctor`, with its hom composed with L's
   inclusion equal to `pullback.fst`, is the natural comparison over h_T. Thus its
   map is specifically the map forgetting the recovered f, not a bare cardinality
   assertion. The Yoneda transformation is δ_D(h) = h*D.
5. For any e as in (3), any T₀ and any h, the existential e₀ has hom equal to the
   pulled-back first projection. The map d between the two closed families is
   specified by its composite with j_D being j_D₀ followed by the canonical ambient
   base-change map. This equation uniquely determines d because j_D is a closed
   immersion and hence mono. The equation `e₀.inv ≫ d = bc_Z ≫ e.inv` is exactly
   equality of the pullback inverse and the inverse of the pullback under the
   canonical identifications. The following equation states the corresponding
   base-change identity for l composed with inverse k. No flatness is assumed.
6. Under the universal open-locus condition, the first conjunct gives the natural
   isomorphism `h_T ×_F Mor ≅ h_(U T D)`. Its hom composed with the Yoneda inclusion
   equals the pullback first projection, so this is explicitly over h_T.
7. `((@IsOpenImmersion).over (X := S)).presheaf γ` states that γ is representable by
   open immersions, using the same categorical notion as the recorded dependency.
8. For every representing object H and `eH : F.RepresentableBy H`, the theorem supplies
   M, i : M → H, and `eM : Mor.RepresentableBy M`. `IsOpenImmersion i.left` and
   `Set.range i.left = (U H (eH.homEquiv (𝟙 H)) : Set H.left)` say that M is exactly
   U of the universal family as an open subscheme of H (with its restricted structure
   sheaf), allowing its canonically isomorphic presentation. The equality involving
   `eH.homEquiv (a ≫ i)` and `γ (eM.homEquiv a)` says that i represents γ on every
   test scheme, including identity maps. The universal family is `eH.homEquiv (𝟙 H)`;
   its pullback D_M is `F.map i.op (eH.homEquiv (𝟙 H))`.
9. The existential e for D_M identifies its first projection with an isomorphism.
   The equality for `(eM.homEquiv (𝟙 M)).left` specifies universal evaluation by
   inverse first projection followed by second projection. The final equality for
   every a : T → M states that its pullback is precisely the classified morphism.
10. `U T₀ (F.map h.op D) = h.left ⁻¹ᵁ U T D` is equality of the open subschemes after
    arbitrary base change. For open subschemes the inverse-image open is canonically
    the fibre product T₀ ×_T U_D. Together with the inverse/evaluation equations (5)
    and the natural isomorphisms over h_T, this gives the stated compatibility of the
    identifications and evaluation under arbitrary and iterated base change. All
    comparison maps are fixed over their monomorphisms, so are unique and coherent.

Dependency declarations used (read from the recorded modules):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the pullback universal property; schemes have
  pullbacks through `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf`: `relativeMorphismsPresheaf`,
  `relativeMorphismGraph`, `graphFirstProjection`, `graphSecondProjection`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, open inclusions.
- `Mathlib.CategoryTheory.Yoneda`: `yoneda`, `yonedaEquiv`,
  `Functor.RepresentableBy`, `Functor.IsRepresentable`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability`:
  `exists_opens_of_relative_isOpenImmersion` and
  `relative_isOpenImmersion_of_exists_opens`, using the shared categorical relative
  representability notion. No specialized replacement definition is introduced.
- Proof import `WeilConjectures.Mathlib.CategoryTheory.Yoneda` provides the recorded
  `bijective_yoneda_app_id` proof dependency.
- The existing `baseChangeMap` from `WeilConjectures.AlgebraicGeometry.PicardFunctor`
  and `IdealSheafData.comap` from `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`
  express the assumed canonical pullback action. `Subfunctor`, `.toFunctor`, `.ι`
  and Mathlib's `MorphismProperty.presheaf` express the comparison without a new
  definition of locus presheaf or open representability.

Edge cases checked mathematically: empty test schemes; Z empty, when the unique
morphism has empty graph and the first projection is invertible; X empty with Z_T
nonempty, when there are no graphs and the image criterion correctly excludes the
empty family; empty closed D with Z_T nonempty; D equal to the ambient product;
nonreduced families (scheme-theoretic ideals are essential); identity and arbitrary
nonflat base changes; and U equal to bottom or top. There are no nonemptiness,
reducedness, dimension, field, or characteristic assumptions. All universes and
variables are explicitly bound, with `autoImplicit false`.

Searches actually run:

- msearch leanfinder: “A closed subscheme of a product is a graph precisely when its
  first projection is invertible, and a universal open isomorphism locus represents
  the relative morphism functor”. Eight hits, including diagonal/closed-immersion
  lemmas and `Proj.pullbackAwayιIso`; none is this functor comparison.
- msearch loogle: `"relative", "isOpenImmersion"`. Three hits about relative
  dimension and relative gluing; no matching theorem.
- msearch grep: `graph|relative.*[Rr]epresent`, restricted to AlgebraicGeometry.
  Five hits in Mathlib Sites/Representability describe generic local representability,
  not this graph recovery and universal evaluation theorem.
- Direct rg in the upstream project and Sheaf for graph/closed-family recovery and
  comparison. The existing `GraphsOpenInHilbert` theorem is the stronger-geometric-input
  parent specialized to `properHilbertPresheaf`; its signature was read in full and
  it cannot give this statement for an arbitrary pullback-stable collection F.
  `RelativeMorphismsPresheaf` supplies the exact definitions used here.
- Direct rg of `RelativeGraphComparison|graph_projection_functor_comparison|graph.*projection.*functor`
  in `dag/lean_names_upstream.json`, Mathlib, WeilConjectures, and Sheaf found no
  existing declarations. Search by the assigned node id in WeilConjectures found none.
- Read `IdealSheafData.comap`, `comapIso`, `Subfunctor.toFunctor`, `Subfunctor.ι`,
  Yoneda representability and the upstream open-subfunctor recognition signatures
  to reuse their exact objects and notions.

No statement correction, new node, dependency repair, or disputed statement was needed.
The first compile caught a typeclass requirement of the `opensRange` notation inside
an existential conjunction; the final statement expresses the same open-subscheme
identity by `Set.range`, alongside `IsOpenImmersion`. The final scompile run compiled
both the sandbox probe and the named library module cleanly within the 60-second limit.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
