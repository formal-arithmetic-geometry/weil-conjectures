## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.SpaceEtalePullbackChartComparison`.
The main theorem is `AlgebraicGeometry.AlgebraicSpace.spaceEtale_pullback_chart_comparison`;
the other public declarations give the remaining clauses and the canonical maps it uses.
All theorem proofs are `sorry`. Definitions contain actual constructions or choices from
unique formula-normalized universal properties. No natural-language statement is changed.

Hypotheses and clauses:

* The size convention is `universe u w`, with schemes in `u` and set sheaves in
  `max (u+1) w`. Site objects may live in `u+1`, while scheme-site morphisms live in `u`.
  No equality of these universes is imposed. The theorem is valid over any base `S`,
  so specializes to the node's Spec Z without extra hypotheses.
* `X Y : AlgebraicSpace S` uses the recorded fppf-sheaf definition. `f : X ⟶ Y` is
  arbitrary. Neither representability nor étaleness of f is assumed.
* `etaleSite_subcanonical` states scheme-site subcanonicality;
  `enlargedEtaleSite_subcanonical` is the required enlarged-site counterpart.
* `spaceEtaleInverse` uses the existing `enlargedBaseChange f` and the recorded
  restriction equivalences; `spaceEtaleAdjunction` identifies its right adjoint with
  `enlargedSmallDirectImage f`, not an unspecified geometric morphism.
* `spaceEtaleRepresentables X` is enlarged Yoneda followed by literal scheme restriction,
  so its sections are Hom_X(W,T), also when T is a non-scheme étale space.
  `spaceEtaleRepresentablePullbackIso` uses `Adjunction.uliftYonedaCompIso` and the
  comparison-equivalence unit. `spaceEtaleRepresentablePullback_naturality` gives
  naturality on every enlarged arrow. `spaceSchemeRepresentableMap` is induced by
  scheme inclusion, with its isomorphism theorem, retaining the ordinary h_U.
* `etaleSetStalk` and `etaleSetGerm` are the actual pointed-neighbourhood section colimit
  and its coprojections over the landed `X.PointedEtale x`, owned by the new
  `def-sfb-space-geometric-set-stalk`. `spaceEtaleStalkIso_existsUnique` quantifies an algebraically
  closed field Ω, its map s to S, and x over s. It states the natural stalk isomorphism
  with target point `x ≫ f.hom.hom`, uniquely fixed by `SpaceEtaleStalkFormula` on
  every compatible pair of pointed charts and every section.
* A chart `U : X.EtaleSite` includes its scheme, map to X and representable étaleness.
  `spaceChartFibreFunctor U` takes the literal fibre over a chart arrow; its section
  set is the subtype defined by `spaceChartFibre`. It acts on maps by the original
  map of section sets. `spaceChartSite` preserves the actual schemes and scheme maps.
  Its equivalence and topology comparison identify X_et/U with the usual scheme U_et.
  `spaceChartEquivalences` and `spaceChartEquivalence` give E_X/h_U ≌ Sh(U_et).
* `spaceChartProjection` is uniquely fixed as projection to the second coordinate,
  and is invertible. This is the slice-restriction comparison on every sheaf.
  `spaceChartLocalizedRingIso_existsUnique` fixes the structural-ring identification
  on every regular-function section via the recorded extension counit;
  `spaceChartRingIso` transports it to the ordinary scheme site. The sectionwise
  identification preserves zero, one, addition and multiplication because it is
  the ring counit on the forced second coordinate.
* `a : U.obj.left ⟶ V.obj.left` is exactly the map of chart schemes over S;
  `ha : yoneda.map a ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom` is commutativity.
  The chart maps U→X,V→Y are already étale in U,V. No covering or surjectivity is added.
* `spaceChartSquareMap` is s:h_U→f⁻¹h_V, using the given pair of maps into X×_YV
  and the normalized representable isomorphism.
  `spaceChartRelocalization` is literally `Over.post (spaceEtaleInverse f)` followed
  by `Over.pullback s`, hence (H→h_V) ↦ (f⁻¹H ×[f⁻¹h_V] h_U→h_U).
* `spaceEtaleStructuralMap` is the mate of the existing unique chart-normalized
  pullback-of-functions map, with faithful coefficient ULift and the restriction units.
  `spaceSchemeEtaleInverse` is the standard scheme base-change inverse image;
  `spaceSchemeStructuralMap` is the mate of the sectionwise pullback of regular functions.
  `spaceChartSliceRingMap` is uniquely fixed by its projection equation using f-sharp.
* The main theorem gives the UNIQUE natural isomorphism between chart transport of
  the ordinary scheme inverse image and the displayed relocalization, satisfying
  `SpaceChartComparisonFormula` on unit-generated sections. Its second conjunct
  is the explicit structural ring-map commutativity equation. This states an
  isomorphism of ringed morphisms, rather than only an equivalence of set functors.
* `spaceChartSquareMap_restriction` is the commuting s-square for any further chart
  maps r,t with `r ≫ a = a' ≫ t`. `spaceChartRelocalization_restriction` supplies the
  unique restriction isomorphism preserving the first pullback coordinate. The
  h_U' coordinate is fixed by its being an arrow of the slice. Thus it respects
  structure maps, and identities and successive restrictions follow by uniqueness.
  The main comparison's normalization identifies its restriction with this map:
  both send every unit-generated section to the same first coordinate.

Dependency declarations read and reused:

* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `IsEtale`, actual scheme-section restrictions.
* `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap` (recorded enlarged-site model),
  including its public `AtlasEtaleRestriction` and `EnlargedEtaleRingedSite` interfaces:
  `enlargedBaseChange`, `enlargedChartLift`, `enlargedSetEquivalence`,
  `enlargedSmallDirectImage`, `enlargedCotangentStructure`,
  `enlargedCotangentRestriction`, `cotangentStructuralMap_existsUnique`.
* `Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism`:
  `chartNormalizedLiftedRing`, `chartNormalizedUnderlyingMap`, owned by the existing
  definition node `def-trf-enlarged-chart-normalized-ring-data` (`existing: true`).
  The item cites that definition node; the ringed-morphism theorem stays proof-only.
* `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda`:
  `Adjunction.uliftYonedaCompIso`; `Sheaf.CategoryTheory.SiteRepresentableAlgebraicPullback`
  is retained as a proof import with its normalized representable theorem.
* Mathlib `GrothendieckTopology.uliftYoneda`, `uliftYonedaEquiv`, `Over.post`,
  `Over.pullback`, `Over.star`, `Subfunctor`, `StructuredArrow`, `colim`, `colimit.ι`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`:
  `Scheme.isContinuous_overPullback` for the ordinary scheme inverse/direct images.
* Existing `SheafOfModules.CochainUniverseTransport.ring` is used for faithful
  coefficient lifting, as in the recorded enlarged ringed-morphism interface.
* Stated proof-dependency modules are imported privately, including
  `AlgebraicSpaceFppfCoveringCalculus`, `AlgebraicSpaceRepresentableEtaleSchemeTests`,
  `EnlargedRingedCompositionLocalization`, and `RingedToposSliceFunctoriality`.
  The recorded proof-only module `Sheaf.CategoryTheory.Sites.RepresentableSliceLocalizedRingedMorphism`
  is absent locally and `scompile.py --source` reports its source unavailable;
  its intended slice argument is included in the main theorem's proof docstring.

Edge cases: empty spaces, empty charts and maps between them; a chart need not cover;
f need not be étale, representable, separated, finite type or quasi-compact; identity f,
identity/further chart restrictions, arbitrary non-scheme enlarged objects; arbitrary
set sheaves and nonconstant coefficients; independent sheaf and scheme universes.
Fibre constructions include empty fibres. On the empty space the empty cover forces
singleton section sets, so the conservative point tests are valid vacuously.

Searches (2026-10-24):

* msearch leanfinder: “Inverse image of representable sheaves and geometric stalks and
  ringed chart localization for algebraic spaces”: eight hits on ordinary topological
  stalk restrictions and locally ringed spaces, none the requested theorem.
* msearch loogle: “AlgebraicSpace, sheafPullback, Over”: zero hits, unknown identifier
  AlgebraicSpace in the Mathlib index.
* msearch grep: “AlgebraicSpace|relocalize|stalk.*pullback”: eleven hits on scheme
  Zariski stalks and topological presheaf stalks, none algebraic-space étale comparison.
* msearch leansearch: “Algebraic space sheaves geometric stalk inverse image chart
  localization”: eight scheme/stalk localization hits, none the requested interface.
* rg in WeilConjectures, Sheaf and Mathlib for the item id, `etaleSetStalk`,
  `SetGeometricNeighbourhood`, `spaceChartFibre` and the comparison name: no existing
  declaration. Existing module-valued `SingleComplex.StalkModel` is a different
  interface (varying-ring modules on the affine model), not a set-sheaf stalk.
* The repair searches distinguish the conservativity theorem from the stalk definition.
  The landed `PointedEtale` and `pointedEtaleForget` already own the neighbourhood
  category. The new set-stalk definition owns only the set-valued colimit and germ;
  it does not duplicate the abelian-valued stalk or its neighbourhood category.

Validation: every file compiled separately in dependency order through scompile.py.
Expected theorem sorries only; dry-run and final delivery results are reported by deliver2.py.
No STATEMENT-DISPUTED flag or statement correction.

## Dependency modules

`lem-sfb-space-etale-conservative-geometric-points` had no usable Lean theorem record.
Its complete statement is supplied in
`Sheaf.AlgebraicGeometry.SpaceEtaleConservativeGeometricPoints`, importing the new
set-stalk definition module. The single theorem states finite-limit and all-small-colimit
preservation, mono/epi/iso detection and faithfulness on maps. It uses the original
scheme etale site and fields in the scheme universe. Only this dependency's lean field
changes. It remains a proof dependency and private proof import of the item; the item
no longer cites it in stmt_deps. No dependency statement has been changed.

## New nodes

`def-sfb-space-geometric-set-stalk` owns
`Sheaf.AlgebraicGeometry.SpaceGeometricSetStalk` and its two definitions,
`AlgebraicGeometry.AlgebraicSpace.etaleSetStalk` and `etaleSetGerm`.
For any S-scheme G and point x, the former restricts the sheaf section diagram using
`X.pointedEtaleForget x` and takes its colimit; the latter is the colimit coprojection
at `U : X.PointedEtale x`. These are actual constructions without sorry.
The input and output coefficient universe is `Type (max (u+1) w)`.
For G = Spec Ω with Ω algebraically closed these are the geometric set stalk and germ.
The new node cites the size convention, algebraic spaces and the existing
`def-sfb-space-pointed-etale-abelian-stalk`; its module imports the latter's
`AlgebraicSpaceAbelianStalk` module and reuses both `PointedEtale` and
`pointedEtaleForget`. The item cites the new definition node directly.

Searches for this new node (2026-10-24), recorded with their actual outputs in its
mathlib_searches: msearch LeanSearch for set-valued algebraic-space colimit stalks,
Loogle for colim and colimit.ι, and grep in Mathlib/AlgebraicGeometry;
rg in WeilConjectures, Sheaf and dag/nodes;
blueprint_refs search for geometric set stalk. No existing algebraic-space set-stalk
definition was found. Mathlib's topological stalk uses a different index category;
the landed abelian stalk has different coefficients. Both generic colimits and
the existing pointed etale neighbourhood category are reused. Stacks 04JY defines
this colimit, and 04K0 identifies its geometric specialization with a topos stalk.

Edge cases for the new definitions: the general scheme-valued point needs no
algebraic-closure hypothesis; geometric specialization adds it only where required.
The diagram and germs retain the actual lifts, and maps use the induced colimit
maps. Empty charts and empty diagrams still have the ordinary set colimit.
The coefficient universe contains the neighbourhood object universe u+1 even
when w is smaller. No equation between u and w is introduced.

## Repair of returned delivery

The retained sandbox was compared with current read-clone nodes: the item's only
non-lean change is its two added stmt_deps, and the conservativity node differs
only in lean. Delivery tooling rebases the repair onto current live main.
The returned immutable delivery was db1bdaef5b19. Both return points are repaired:

1. H2/H4 set-stalk ownership: removed SetGeometricNeighbourhood entirely. Both the
   item and the conservative theorem import SpaceGeometricSetStalk. The item's
   stalk formula uses `X.PointedEtale x` and `Y.PointedEtale (x ≫ f.hom.hom)`.
   Its stmt_deps now cites def-sfb-space-geometric-set-stalk in place of the
   conservativity theorem node. The conservativity record lists only its theorem;
   the new definition record lists the stalk and germ. The colimit and germ use
   the landed pointedEtaleForget, without a copied neighbourhood-category alias.
2. H2 normalized-ring-data ownership: the item's stmt_deps cites the landed
   def-trf-enlarged-chart-normalized-ring-data in place of
   lem-trf-space-enlarged-chart-ringed-morphism. The owning module remains the
   recorded EnlargedChartRingedMorphism; the two constructions used in the item
   are already listed by that existing definition node.

The mathematical statements, germ normalization, chart formulas, uniqueness,
structure-ring compatibility and restriction naturality are retained.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
