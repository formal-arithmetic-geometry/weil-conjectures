## Worker report

Repair of returned immutable head `2ef6b4127130`, points H3, H4 and H8. The saved
packet was inspected first and its initial `deliver2.py --no-push` passed
mechanically (commit `a924f7a2cc`), but the requested mathematical self-check
confirmed the reported free-choice defect. The replacement retains the owning
module and node, replacing that defect rather than re-pushing unchanged work.
The node's mathematical statement and five proof steps are unchanged.

The module is `Sheaf.TraceFormula.SimplicialPhEtaleSquare`, namespace
`AlgebraicGeometry.SimplicialPhEtale`. It constructs the actual total inclusion,
both augmentations, and normalized comparison transformations. Its main theorem
asserts their invertibility and the exact component normalization. There is no
`Nonempty (SquareData a)` and no free geometric-morphism field.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| Arbitrary simplicial scheme | `U : SimplicialObject Scheme.{u}`. |
| Target and augmentation | `X : Scheme.{u}` and `a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X`. Naturality includes every face and degeneracy. |
| Small étale sites | Existing `Scheme.Etale`, `smallEtaleTopology`, `TotalEtaleSite`, `totalEtaleTopology`, `TotalEtaleTopos` and `totalEtaleRestriction`. |
| Big ph sites and common containing universe | Existing `Scheme.phSiteModel.{u,u}`, `Scheme.phModelTopology.{u,u}` and `Scheme.PhSheaf.{u,u}`; all set values are `Type (u+1)`. |
| The ph total site | `modelObject a` is `Over.lift U a` followed by the existing presentation equivalence; `PhTotalTopos a` uses `SimplicialSliceSite.topology`. |
| Identification of its components with big ph sites | `flatten` and `unflatten` are the actual `Over.iteratedSliceForward` and `Over.iteratedSliceBackward`, transported through `AsSmall`. `sliceTransport` uses their restrictions on sheaves. Its adjunction is uniquely normalized to identity on sections in `flatten_adjunction`. |
| The inclusion-induced `h_T` | The existing `Scheme.phEtaleGeometricMorphism T`; `componentComparison f` only transports its source through the canonical slice identification. `h_X` is the existing declaration directly. |
| The induced total `h` | `totalInclusion a` maps each `(n,V/U_n)` to the same scheme and degree in the total ph site, retaining both components of every arrow. `totalDirect` is literal restriction along this functor; `totalComparison` uses its determined left adjoint and the named left-exactness clause. |
| Compatibility with simplicial operators | The total inclusion is a functor on the full comma category, not a collection of degreewise choices. Its arrow-square proof uses `f.hom.w` and `a.naturality`. Passing between these squares and maps into fibre products uses the existing `totalEtaleHomToPullback` and `SimplicialSliceSite.transitionHomEquiv`; uniqueness of the two projections supplies the canonical iterated-fibre-product identifications. Identities and compositions are the inherited category and functor laws. |
| Direct-image component formula | `directComponentIso a n` is constructed as identity on sections at every étale object and includes its restriction maps. |
| Inverse-image component formula | `inverseComponentMap a n` is its specified adjunction mate, using the total unit. The first conjunct of the main theorem states that this map is invertible. `inverseComponentIso` exposes the isomorphism in the node's direction. |
| Sheaves as families with transitions | Both total topoi are sheaves on the existing full total-site categories. A presheaf supplies components and maps for every commuting square, and its functor laws are the identity/composition transition rules; the existing pullback hom-equivalences convert these to inverse-image transitions. Coverings are generated in a fixed degree, so the sheaf condition is degreewise. No replacement category of unconstrained families is introduced. |
| Actual ph augmentation `b` | `phAugmentedObject a` augments in the single fixed ph presentation to the identity of `X/X`. `phAugmentation a` is `SimplicialSliceSite.geometricMorphism` followed by the canonical terminal-slice transport `sliceTransport (𝟙 X)`. |
| Actual étale augmentation `a` | `etaleProjection` sends `(n,V/U_n)` to `V/X`. `etaleInverse` is the canonical presheaf Kan extension along the existing inclusion at `X`, restriction along this projection, and total étale sheafification. `etaleAugmentation` uses this specified inverse image and its determined right adjoint. |
| Its ordinary component inverse image | `componentKanExtension` names the intermediate degreewise expression of this construction. It is not a replacement definition of ordinary inverse image: `componentKanExtension_comparison` identifies it uniquely with the existing `Functor.sheafPullbackConstruction.sheafPullback` along `MorphismProperty.Over.pullback @Etale ⊤ f`. The normalization uses the ordinary adjunction unit, the actual projection `V ×_X T → V`, the inclusion Kan unit and the sheafification unit. `componentKanIso` chooses this uniquely determined isomorphism. `ordinaryAugmentationComponentMap`, whose source is precisely the existing ordinary inverse image, is invertible by the second conjunct. |
| Canonical component comparison `θ_n` | `extensionToPh` is the transpose of the published inclusion's unit under the Kan adjunction. `componentSquareUnit` restricts it and transposes under sheafification; `componentSquareMap` transposes under the actual component comparison. `ordinaryComponentSquareMap` incorporates the uniquely normalized comparison with ordinary étale pullback. The third conjunct states that this specified `θ_n` is invertible. |
| Canonical total square | `squareUnit` uses that same `extensionToPh`, the total projection, and the total sheafification adjunction. `squareMap` is its transpose under the actual total comparison. The fourth conjunct states its invertibility, and `inverseSquareIso` exposes `h⁻¹a⁻¹ ≅ b⁻¹h_X⁻¹`. |
| Component normalization and transition compatibility | The final conjunct equates the restriction of `squareMap`, after the actual augmentation and inverse-component identifications, with `ordinaryComponentSquareMap (a.app n)`. The maps being restricted are natural transformations on sheaves on the full total site, so their underlying naturality includes all cross-degree arrows. Thus this equality fixes the component maps and their face/degeneracy compatibility, not only the component objects. |
| `a ∘ h ≅ h_X ∘ b` | `geometricSquareIso` is the direct-image mate of `inverseSquareIso`, using `conjugateIsoEquiv` and the actual composite adjunctions. |
| No properness, surjectivity or hypercover assumption | None occurs in the binders, auxiliary properties or main conclusion. |

Dependency declarations used and read:

- `Sheaf.AlgebraicGeometry.PhSchemeSite`: `Scheme.phTopology`, `phSiteModel`,
  `phModelTopology`, `PhSheaf`.
- `Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison` (Q135):
  `Scheme.phEtaleInclusion`, `phEtaleGeometricMorphism`, and its actual adjunction.
  Only its geometric-morphism clause is used, not its derived torsion theorem.
- `Sheaf.CategoryTheory.SliceSiteSimplicialAugmentation`:
  `SimplicialSliceSite.Total`, `topology`, `componentRestriction`, `projection`,
  `geometricMorphism`, `inverseComponentIso`, `transitionHomEquiv`.
- `Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite`:
  `TotalEtaleSite`, `totalEtaleTopology`, `TotalEtaleTopos`,
  `totalEtaleComponent`, `totalEtaleRestriction`, `totalEtaleHomToPullback`.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact`:
  `etaleSetInverseImage_exact`, with the standard base-change site functor and
  sheafified-Kan-extension inverse image; current source read through
  `scompile.py --source` because the older checkout lacks this module.
- `Sheaf.CategoryTheory.SiteMorphismComposition`: proof-only import of
  `siteMorphism_composition`; the published Sheaf owner avoids the documented
  upstream duplicate.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`, `comp`.
- Mathlib: `Scheme`, `Scheme.Hom`, `Scheme.Etale`, `smallEtaleTopology`,
  `SimplicialObject`, `Over.lift`, `Over.post`, `Over.iteratedSliceForward`,
  `Over.iteratedSliceBackward`, `Over.map`, `MorphismProperty.Over.pullback`,
  `AsSmall.up/down`, `Functor.sheafPullbackConstruction.sheafPullback`,
  `sheafPushforwardContinuous`, `lanAdjunction`, `sheafificationAdjunction`,
  `Adjunction.whiskerRight`, and `conjugateIsoEquiv`.

The item gains only the statement dependencies of the four published interfaces
now used directly: Q135's inclusion comparison, the slice-site construction,
the total étale site and the set-valued étale inverse-image interface. No
new node or dependency repair is required, and no statement correction is made.

Edge cases: empty schemes and their empty covering families are retained by the
existing sites; degree zero is included by `n : ℕ`; constant simplicial objects
and identity augmentations use exactly the same constructions. Both unit
normalizations are identities/projections in the identity case. Arbitrary
augmentation maps, non-surjective maps and arbitrary degeneracies are admitted.
The use of one `phSiteModel` does not discard objects or arrows: `AsSmall` is an
equivalence, with the containing universe also used for all sets of sections.
There is no `STATEMENT-DISPUTED` or remaining node fault.

Searches performed in the repair: `msearch.py leanfinder` for “An inclusion of
etale objects induces a morphism of total simplicial ph topoi compatible with
augmentation” returned eight unrelated simplicial/Kan-extension hits;
`msearch.py loogle '"SimplicialObject", "Sheaf"'` returned no hits;
`msearch.py grep 'phEtale|simplicial.*[Tt]opos'` returned no Mathlib hits.
`rg` in the prescribed upstream and project source directories found the
published Q135 comparison, the existing total étale and slice-site APIs, and
no existing declaration of this item. The retained earlier report's searches
are also recorded in the node's unchanged `mathlib_searches`.

All postponed theorems belong to clauses of this node: `flatten_continuous` and
`flatten_adjunction` give the canonical component-site identification;
`totalInclusion_continuous`, `totalDirect_properties` and
`totalInverse_leftExact` give the induced total geometric morphism;
`etaleInverse_properties` gives the augmentation morphism;
`componentKanExtension_comparison` identifies its component construction with
the existing ordinary inverse image; `simplicial_ph_etale_square` states the
component formulas and canonical normalized square. Each has a source/blueprint
docstring and a complete natural-language proof. Definitions have real data;
choices are adjoints of specified functors or uniquely normalized objects.

## Second reading by Q138

This is the required self-check under the dispatcher's instruction not to start
other agents; the maintainer performs the independent review. I reread the node,
its five proof steps, Stacks `spaces-simplicial.tex` at the labels for 0DHJ and
0D99, the recorded dependency declarations, and the repaired file together.

H3: removed `SquareData` and all five unconstrained morphism fields. The actual
`h_T`, `h`, `a` and `b` are now constructed as specified above. Component
comparisons and the square are actual unit-normalized maps whose invertibility
is asserted; the final equality fixes their component normalization and the
full total-site naturality retains transitions. I also checked that the
component augmentation uses the existing ordinary étale inverse image through
a uniquely normalized comparison, rather than silently choosing another one.

H4: removed `EtaleTotalTopos`, `EtaleComponentTopos`,
`EtaleComponentRestriction`, `smallOver`, `smallPhTopology`, `smallOverObject`
and `PhBaseTopos`. The module uses `TotalEtaleTopos` and the existing restriction
functor directly. Every ph construction uses `Scheme.phSiteModel` and
`phModelTopology`; the terminal-slice and component transports are explicit.
The old explicit `overObject` construction is also replaced by existing
`Over.lift`, with no duplicate declaration.

H8: every declaration has a source/blueprint docstring; the main theorem's
docstring follows all five DAG proof steps. `lean.declarations` is regenerated
from every top-level declaration, including transport, canonical-map and
instance helpers. The obsolete missing `smallOver` declaration is gone.

No hypothesis was added and no clause removed. The node copy changes only
`lean` and the permitted additions to `stmt_deps`. The sandbox is the only
edited directory; compilation and delivery use the authorized wrappers.
