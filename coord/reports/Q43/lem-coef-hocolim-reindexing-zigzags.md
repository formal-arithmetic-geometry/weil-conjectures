## Worker report

The module `Sheaf.CategoryTheory.HocolimReindexingZigzags` states
`HomotopicalAlgebra.hocolim_reindexing_zigzags` and the preliminary clauses of the
same node. All four theorem proofs are `sorry`; all definitions have real data.
The item's natural-language statement and its dependencies are unchanged.

The recorded repair note is resolved and belongs to stage 1: it required splitting
an overlong proof step while retaining this statement. This delivery uses the
current nine-step proof and does not revive an archived Lean interface.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed universes, enlarged if necessary; small indexing categories | Explicit universes `u v w u' v'`, `M : Type u`, `Category.{v} M`, and `I J K : Type v` with `SmallCategory`; target localization `H` has independent object and morphism universes. The small-index universe is exactly the `v` used by the recorded model-colimit dependency. There is no equality imposed on `u` and `v`. |
| Complete and cocomplete model category | `[ModelCategory M] [HasLimits M] [HasColimits M]`; the model-category terminology is the Mathlib structure used by the recorded Reedy dependency, imported directly. |
| Combinatorial, with locally presentable underlying category and two set-generated systems | `hM : CombinatorialModelCategory.{u, v, w} M`, using the recorded definition from `ModelColimitLocalizationComparison`; its fields are local presentability, the two generating families, and the two functorial factorizations. No new combinatorial or presentability predicate is defined. |
| Projective diagram model structure has objectwise weak equivalences and fibrations | `ProjectiveHocolimReplacement.model`, `weakEquivalences_eq`, and `fibrations_eq`. These refer to `MorphismProperty.functorCategory`, not a duplicate pointwise predicate. |
| Functorial projectively cofibrant replacement `Q_I V → V` | Fields `replacement`, `augmentation`, `cofibrant`, and `augmentation_weakEquivalence`. The augmentation is a natural transformation of endofunctors; its components are natural transformations of diagrams. The chosen cofibrant replacement may have any objectwise weak-equivalence augmentation, as allowed by the recorded colimit-comparison theorem. |
| Such replacements exist for every small shape | `projectiveHocolimReplacement_exists`, stated from the projective existence result and its small-object/functorial-factorization construction. Definitions below take specified replacement data and never choose them from this postponed existence theorem. |
| `hocolim_I V := colim_I Q_I V` and functorial maps | `ProjectiveHocolimReplacement.hocolim := R.replacement ⋙ colim`; thus its object is precisely the stated colimit and its map is `colimMap (replacement.map a)`. |
| Preserve objectwise weak equivalences | `hocolim_map_weakEquivalence` takes `ha : ∀ i, weakEquivalences M (a.app i)` and concludes both `weakEquivalences M (R.hocolim.map a)` and `IsIso (L.map (R.hocolim.map a))`. This states the actual-map assertion and its homotopy-category interpretation. |
| Ordinary homotopy category, localization at weak equivalences | Any `L : M ⥤ H` with `[L.IsLocalization (weakEquivalences M)]`; choosing the strict localization is included, and equivalent ordinary homotopy categories are allowed. |
| Canonical reindexing map `g_*` | `hocolimReindex hM RI RJ L g V`. Its source is `L.obj (RJ.hocolim.obj (g ⋙ V))` and target is `L.obj (RI.hocolim.obj V)`. It is defined by a specific replacement roof, described below, not an unconstrained map or choice of a witness. |
| Identity and composition | First and second conjuncts of `hocolim_reindexing_calculus`. The left unitor and associator identify the restricted diagrams; they do not impose strict equalities on functor data. |
| Naturality in the value diagram | Third conjunct of `hocolim_reindexing_calculus`, for an arbitrary natural transformation `t : V ⟶ V'`. |
| For `a : g → g'`, the reindexing triangle commutes with `V(a)` | Fourth conjunct of `hocolim_reindexing_calculus`: `hocolimReindex ... g V = L.map (RJ.hocolim.map (Functor.whiskerRight a V)) ≫ hocolimReindex ... g' V`. |
| A reverse indexing functor `f : I → J` | Binders `g : J ⥤ I` and `f : I ⥤ J` in the main theorem. |
| Finite zigzag from `gf` to `id_I`, weak equivalences after `V` | `hI : DiagramwiseWeakEquivalenceZigzag V (f ⋙ g) (𝟭 I)`. Mathlib composition is written in traversal order. The helper uses `Relation.ReflTransGen` of the disjunction of forward and reverse natural-transformation links, with the component condition `weakEquivalences M (V.map (a.app i))`. |
| Finite zigzag from `fg` to `id_J`, weak equivalences after `Vg` | `hJ : DiagramwiseWeakEquivalenceZigzag (g ⋙ V) (g ⋙ f) (𝟭 J)`. This uses the second value diagram exactly, and makes no compatibility demand between zigzags. |
| Comparison is an isomorphism | First conjunct of `hocolim_reindexing_zigzags`: `IsIso (hocolimReindex hM RI RJ L g V)`. |
| Any actual representative is a weak equivalence | Second conjunct quantifies over every actual map `m` between these two model-category homotopy-colimit objects and assumes precisely `L.map m = hocolimReindex ...`; it concludes `weakEquivalences M m`. No endpoint cofibrancy or fibrancy is assumed. |
| Natural isomorphisms and strict identities are included | The link predicate includes a natural isomorphism's forward or reverse transformation because its image under any functor is an isomorphism and therefore a model weak equivalence. Reflexivity of `ReflTransGen` admits strict identity composites with zero links. |

Canonical roof: let `QI = RI.replacement.obj V`. Its inverted left leg is
`L(H_J(g*QI) → H_J(g*V))`, induced by `g*` of the augmentation of `QI`.
The right leg is `L(H_J(g*QI) → colim_J(g*QI) → colim_I(QI))`, first the
`RJ` augmentation and then Mathlib's `colimit.pre QI g`. The left leg is invertible
by the node's homotopy-invariance clause. The augmentation identities identify this
roof with the map of localized colimit cocones. This specifies the canonical map
without depending on a downstream reindexing theorem. The `letI` occurs only inside
a definition, introduces a proved-proposition instance from the named postponed
homotopy-invariance theorem, and supplies no postponed data.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`,
  `SSet.Enhanced.Algebroid.completeCategory`: imported for the stipulated shared
  universe context; none of its algebroid constructions is copied or specialized.
- `Sheaf.CategoryTheory.ReedyModelStructure`,
  `HomotopicalAlgebra.Reedy.model_structure`: uses Mathlib model-category classes,
  initial/terminal-map cofibrancy, and functor-category morphism properties.
- `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`,
  `HomotopicalAlgebra.CombinatorialModelCategory` and
  `HomotopicalAlgebra.modelColimitLocalizationComparison`: the exact combinatorial
  predicate and the projective/coherent ordinary-colimit cocone comparison.
- All recorded proof modules are imported: `EnhancedDiagramsCones`,
  `EnhancedFunctorConeCalculus`, `LocalizationHomotopyCategory`, and
  `ModelLocalizationDetectsWeakEquivalences`. Their recorded declarations are
  `SSet.Enhanced.coneCategory`,
  `SSet.Enhanced.enhanced_functor_cone_calculus`,
  `SSet.Enhanced.localization_homotopy_category`, and
  `HomotopicalAlgebra.modelLocalization_weakEquivalence_iff_isIso`.
- The Mathlib leaf `lem-weil-pbc-localization-universal-property` is imported
  through `Mathlib.CategoryTheory.Localization.Predicate`, with its recorded
  `CategoryTheory.Localization.lift`, `fac`, `liftNatTrans`, `liftNatIso`,
  `fullyFaithfulWhiskeringLeft`, and `natTrans_ext` interface.

Edge cases checked before writing: empty indexing categories (no Nonempty
hypothesis); zero-link zigzags (`ReflTransGen.refl`); mixed and reverse link
orientations; arbitrary lengths of the two zigzags with no common-length
assumption; noncofibrant original diagrams; arbitrary, possibly noncofibrant and
nonfibrant endpoints of an actual representative; natural-isomorphism links;
strict identity composites; independent model-category object/morphism and
localization universes. The `K` parameter in the calculus theorem is arbitrary,
so its composition clause covers the repeated-index cases used in the proof.

Searches made in this session:

- `msearch.py ... leanfinder "Homotopy colimits reindexing functor inverse finite
  natural transformation zigzags weak equivalences"`: eight hits, all
  `HomotopicalAlgebra.AttachCells.reindex*`; these concern reindexing cell families,
  not homotopy colimits of model-category diagrams.
- `msearch.py ... loogle '"cofibrantReplacement"'`: no hits.
- `msearch.py ... grep 'hocolim|homotopyColimit|cofibrantReplacement'
  AlgebraicTopology`: no hits.
- `rg` for `hocolim|homotopyColimit|lem-coef-hocolim-reindexing-zigzags` in the
  upstream `WeilConjectures` and shared `lean/Sheaf` sources: the upstream has no
  matches; project hits concern enhanced cocone apices, enriched Grothendieck
  constructions, and additive/complex telescopes. None provides this model-category
  projective replacement and ordinary-localization reindexing statement.
- `rg` for every proposed top-level name in Mathlib, upstream `WeilConjectures`,
  and shared `lean/Sheaf`: no matches.
- Read Mathlib `Limits.HasLimits`: `colim`, `colimMap`, `colimit.pre`,
  `colimit.pre_pre`, and `colimit.pre_map'` supply the existing ordinary operations.
  The presentability terminology comes from the dependency's Mathlib
  `IsLocallyPresentable`, rather than a second definition.

Source checked directly: the PDF at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dugger-comb.pdf,
Remark A.3(i)--(iv), Proposition A.4, and Remark A.5. The source explicitly allows
zigzags instead of single transformations and distinguishes the two occurrences
of the `g` comparison in the inverse argument. The module's theorem docstrings
carry the current nine proof steps and explain the replacement roof.

Validation: `scompile.py Q43 lem-coef-hocolim-reindexing-zigzags` compiled the
single delivered module cleanly, including its public library view. No compiler
warnings or errors were emitted. No statement correction, dependency repair,
new independent definition node, or STATEMENT-DISPUTED issue is needed. All helper
declarations implement clauses or constructions of this same owning node and
are listed in its `lean.declarations`.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
