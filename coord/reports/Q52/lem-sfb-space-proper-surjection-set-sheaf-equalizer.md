## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperSurjectionSetSheafEqualizer` states
`AlgebraicGeometry.AlgebraicSpace.properSurjection_setSheaf_equalizer`, with `sorry`
as its only theorem proof. All five helper definitions have actual data and now live
in `Sheaf.AlgebraicGeometry.SpaceSetSheafOverlapArrows`, owned by a definition node.
Two existing-declaration definition nodes own the published geometric morphism and
composition comparison. No dependency repair or statement correction is needed.

Hypothesis and clause correspondence:

- The base is the explicitly bound `{S : Scheme.{u}}`; `{V U : AlgebraicSpace S}`
  and `(h : V ⟶ U)` are the prescribed algebraic spaces and their morphism.
- The universe convention is expressed by explicit `universe u w` and sheaves in
  `Type (max (u + 1) w)`. This retains the published small-site coefficient bound
  while allowing an arbitrarily larger set universe. `autoImplicit` is false.
- Properness is exactly `(hp : MapIsProper h)`, the recorded separated, finite-type,
  universally-closed predicate. Surjectivity is exactly
  `(hs : Function.Surjective (mapPoint h.hom.hom))` on field-valued point classes.
  This avoids the representable-only predicate `AlgebraicSpace.IsSurjective`.
- `(A : Sheaf U.etaleTopology (Type (max (u + 1) w)))` is an arbitrary sheaf of
  sets on the published small scheme-object étale site of U.
- R is the actual sheaf pullback `enlargedFibreProduct h h`. Its first projection
  is `enlargedFibreProductFst h h`; `properDescentSecondProjection h` bundles
  `Limits.pullback.snd h.hom h.hom` as the other space morphism. The common a is
  `enlargedFibreProductFst h h ≫ h`. The second composite is identified with it
  by `Limits.pullback.condition`, lifted through `ObjectProperty.hom_ext`.
- The first arrow is literally `(smallEtaleMorphism h).adj.unit.app A`, from A
  to the object obtained by applying the existing inverse image and direct image.
- `properDescentOverlapMap r h a e A` first applies the direct image for h to
  the adjunction unit for r at h-inverse-image A. It then applies the canonical
  direct comparison and the direct image of the canonical inverse comparison.
  The latter is `Adjunction.leftAdjointCompIso`, so it is the mate of precisely
  the former direct comparison, including equality transport to a.
- `properDescentDirectCompositionIso` uses the equality identifying each published
  `smallEtaleMorphism.direct` with `enlargedSmallDirectImage`, cancels the middle
  scheme-restriction equivalence with its `unitIso.symm`, and uses
  `enlargedDirectCompositionIso`. That is the sheaf comparison induced by the
  projection-preserving fibre-product comparison, with no arbitrary arrows or
  independently chosen composition isomorphism.
- `∃ c : unit ≫ arrow₁ = unit ≫ arrow₂, ...` asserts the diagram commutes.
  `Nonempty (IsLimit (Fork.ofι unit c))` is the categorical sheaf equalizer,
  including universal factorization and uniqueness against every sheaf.
- `Mono unit` explicitly records the in-particular monomorphism assertion.
  For every `T : U.EtaleSite`, `Function.Injective (unit.hom.app (op T))`
  records sectionwise injectivity; for every middle section b, the displayed
  equality of the two component maps is equivalent to `∃ s, unit_T s = b`.
  This is precisely the stated image of the unit, on every small-site object.
- There is no representability, finite-presentation, Noetherianity, group,
  torsion, constructibility, nonemptiness, or separation assumption beyond the
  separatedness already contained in properness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`; `Sheaf.CategoryTheory.SiteCoveringAxioms` retains the Mathlib
  `Sheaf` encoding used by the sites-and-cohomology dependency.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap` is the current recorded module
  of `lem-trf-space-enlarged-etale-ringed-site-model`. Its public ancestor
  `EnlargedEtaleRingedSite` supplies `enlargedSetEquivalence`,
  `enlargedSmallDirectImage`, `enlargedSmallDirectImage_geometric`,
  `enlargedFibreProduct`, and `enlargedFibreProductFst`.
- `Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism`:
  `enlarged_chart_ringed_morphism` and its canonical small/enlarged-site interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, used by the existing bundled fibre product.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`.
  Its imported `ProperCurveModuli.mapPoint` is the point-class map used in hs.
- `def-sfb-space-small-etale-geometric-morphism` records the existing
  `Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative.smallEtaleMorphism`
  (declaration namespace `AlgebraicGeometry.AlgebraicSpace`).
- `def-sfb-space-enlarged-etale-composition-comparison` records the existing
  `enlargedCompositionIso` and `enlargedDirectCompositionIso` from
  `Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization`.
- `def-sfb-space-set-sheaf-overlap-arrows` owns the five concrete helper definitions
  in `Sheaf.AlgebraicGeometry.SpaceSetSheafOverlapArrows`; the item cites that node.
  The two theorem nodes remain in `proof_deps` only; their statements are unchanged.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `Adjunction.leftAdjointCompIso`; Mathlib `Functor.isoWhiskerLeft/Right`,
  `eqToIso`, `Fork.ofι`, `IsLimit`, and `Mono` give the standard categorical encoding.

The other already-stated proof dependencies are plain imports:
`WeilConjectures.AlgebraicGeometry.GeometricPointMorphismStalkBijection`,
`Sheaf.AlgebraicGeometry.EtaleSetSectionsPhSheaf`, and
`Sheaf.AlgebraicGeometry.PhSchemeSite`. Joint-surjectivity definitions already
arrive through the public fibre-product interface. Proper base change, smooth/
surjective locality, weak Chow, and proper composition have no recorded modules
in this checkout, so no imaginary imports are introduced. The theorem docstring
retains all six DAG proof steps and their cited node identifiers.

Source and edge checks: I read `literature/stacks-project/spaces-more-cohomology.tex`,
`lemma-surjective-proper` (Tag 0DFX). Its statement is exactly the arbitrary set-sheaf
assertion here. The DAG already repairs the proof's affine-source typo by working
locally on the target, so no further correction is needed. For the empty target,
all site sheaf sections on the empty scheme are singleton and the empty point-map
surjectivity hypothesis is valid; the limit and image assertions retain that case.
For a nonempty target an empty source does not satisfy hs. For an identity or
isomorphism h, the unit is an isomorphism and the two overlap maps coincide under
the prescribed comparisons. Empty and singleton stalk sets are allowed; the
existence-of-preimage assertion does not presume that any section exists. All
scheme and space objects stay in u, and the independent w has no artificial equality.

Searches made before writing:

- `msearch.py ... leanfinder`: “A proper surjective morphism of algebraic spaces
  gives an equalizer of etale sheaves of sets by its inverse image direct image unit”.
  Eight hits: scheme étale pullbacks, equalizer immersions, affine-transition-limit
  lemmas and jointly-surjective open-immersion stability; none states this result.
- `msearch.py ... loogle '"IsProper", "equalizer"'`: zero hits.
- `msearch.py ... grep 'proper.*equaliz|equaliz.*proper'`: 24 hits in abstract
  categorical equalizers, condensed objects, scheme separated equalizers, and
  ring-theoretic equalizers; no proper-surjective étale set-sheaf statement.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and pinned Mathlib with the same
  proper/equalizer patterns and with the proposed declaration names; upstream
  node-id grep and `dag/lean_names_upstream.json` checks: no duplicate.
  The nearby `ProperSurjectionEtaleSectionEqualizer` is for schemes and abelian
  sheaves, only terminal sections. It does not match this node's algebraic-space,
  arbitrary-set-coefficient, sheaf-equalizer statement. The existing small-site
  adjunction, sheaf pullback, point map and composition comparison are reused.

Validation of the returned version: the prescribed `scompile.py Q52 ...` compiled
the module in sandbox and library modes in 3.8 and 3.7 seconds with exit 0 and no
errors or warnings. The repaired modules and existing-definition probes are compiled
again separately by the prescribed tools before redelivery. The only postponed theorem is the main theorem, whose
full natural-language proof appears in its docstring. All helper definitions are
compositions of existing concrete maps and isomorphisms.


## Repair of H2

The immutable returned head was `b2d721952f31`. Current main has no Lean attachment
for this item and retains its original eight statement dependencies. I rebuilt the
item JSON from that current node, copied its unchanged theorem signature, and added
only `def-sfb-space-set-sheaf-overlap-arrows` to the original `stmt_deps`. I removed
both added theorem nodes `lem-sfb-space-geometric-points-conservative` and
`lem-trf-space-enlarged-ringed-composition-localization` from that field. Both remain
in the unchanged `proof_deps`, with plain proof imports in the theorem module.

The return correctly identified that the theorem results themselves are not used
in the statement. Their modules house concrete definitions that lacked definition
node ownership. The two existing-definition records below give those definitions
explicit ownership without introducing any duplicate declaration. A third definition
node owns the five overlap helpers, moved from the theorem module to its own module.
Every moved helper retains exactly its previous signature and body; only its
blueprint docstring points to its new owner. Thus the theorem's mathematical
statement is byte-for-byte unchanged. No new axiom or additional hypothesis occurs.

## New nodes

`def-sfb-space-small-etale-geometric-morphism` records the already-landed
`AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphism` with `existing: true`, from
`Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative`. Its body is exactly
`(enlargedSmallDirectImage_geometric f).choose`. The base theorem fixes the direct
image; its inverse image is identified by the adjunction, not chosen as an arbitrary
unconstrained object. This node introduces no second definition and no new module.
The source is Tags 03G2, 03G8 and the adjunction used in 0DFX. The node's geometric
morphism, sites, universes, spaces and schemes have their recorded dependencies.
It assumes no properness or surjectivity, covers all space maps, and retains
`Type (max (u + 1) w)` exactly.

`def-sfb-space-enlarged-etale-composition-comparison` records the already-landed
`AlgebraicGeometry.AlgebraicSpace.enlargedDirectCompositionIso`, together with
`enlargedCompositionIso`, as existing definitions in
`Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization`. Its source is
Tags 03G2 and 03G8. The site comparison is literally the projection-preserving
pullback pasting isomorphism; direct image evaluates sheaves contravariantly on it.
The record claims no composition or localization coherence theorem and has empty
proof dependencies. It works for arbitrary coefficient categories and all
composable space maps, including identities and empty spaces. No module is written
for an exact existing definition, as required by the one-definition rule.

`def-sfb-space-set-sheaf-overlap-arrows` owns the new module
`Sheaf.AlgebraicGeometry.SpaceSetSheafOverlapArrows` and its five concrete
definitions, moved unchanged from the returned theorem module. It states precisely
the direct comparison, its equality transport to a common composite, its inverse
adjunction mate, the composite overlap map, and the second sheaf projection.
`properDescentDirectCompositionIso` cancels the middle equivalence with its unit;
`properDescentDirectComparison` inserts the equality transport;
`properDescentInverseComparison` is `Adjunction.leftAdjointCompIso`;
`properDescentOverlapMap` is h-direct-image of the r-unit followed by these two
comparisons; `properDescentSecondProjection` is the bundled actual second pullback
projection. Each component of the new definition node has its concrete counterpart
here and every declaration has a source/blueprint docstring. There are no theorems,
`sorry`s, private definitions, or file-local notation in this definition module.
The source is precisely the adjunction-unit arrows of 0DFX with 03G2/03G8 normalization.
The common composite may be specified by any equality e; no special surjection or
properness is assumed in constructing the arrows. Empty spaces and arbitrary set
coefficients are retained as in the main theorem.

Searches for all three nodes are recorded verbatim from `msearch.py` in their
`mathlib_searches`: LeanSearch for the canonical small-étale sheaf adjunction and
composition returned eight abstract sheaf adjunction/composition hits; Loogle
`"leftAdjointCompIso"` returned the standard mate and its compatibility lemmas;
grep `smallEtaleMorphism|enlargedDirectCompositionIso|sheafPushforwardContinuousComp`
returned ten generic Mathlib direct-image composition hits. Source and DAG rg found
the concrete definitions in the two theorem modules, with no definition node owning
either; no upstream or Mathlib exact algebraic-space declaration was found.
`blueprint_refs.py search 'sheaf adjunction'` returned two different notions
(supported exterior product and pro-étale operations). `blueprint_refs.py ancestor`
returned None for this item, used literally in every new node. The new nodes' via
chains prepend this item to its inherited chain. No blueprint unit is altered.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
