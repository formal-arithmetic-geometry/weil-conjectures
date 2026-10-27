## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperSetSheafBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.space_proper_set_sheaf_base_change` with proof
`sorry`. It constructs its canonical natural exchange transformation and the two
composition helpers with real data. There are no other postponed proofs.

Clause-by-clause correspondence:

- “S a scheme; algebraic spaces over S”: `universe u w`, `{S : Scheme.{u}}`,
  `{Y Z Y' Z' : AlgebraicSpace S}`. The existing fppf-sheaf full-subcategory
  definition is used literally.
- The size convention and arbitrary set sheaves: `F : Sheaf Y.etaleTopology
  (Type (max (u + 1) w))`. This is the existing enlarged/small equivalence's
  coefficient universe. The independent `w` permits arbitrarily large sheaf
  universes without identifying the site object and morphism universes.
- “f proper”: `(f : Y ⟶ Z)` and `(hf : MapIsProper f)`, the recorded separated,
  finite-type, universally-closed predicate, without replacing it by properness
  of an atlas or representability.
- “g any morphism”: `(g : Z' ⟶ Z)` has no property hypothesis.
- “Y' = Y ×_Z Z', with projections f', g'”: the four maps and
  `(sq : IsPullback g' f' f g)` specify the universal cartesian square. This is
  invariant under the unique isomorphism with the chosen sheaf fibre product;
  it introduces no extra restriction on the node's fibre product.
- The four functors are the inverse and direct images of
  `(enlargedSmallDirectImage_geometric.{u, w} f).choose` (and likewise for the
  other three maps), directly from the recorded enlarged-site dependency.
  Their direct images are identified by the published `choose_spec`
  with `enlargedSmallDirectImage`, actual evaluation on fibre products transported
  through `enlargedSetEquivalence`.
- The displayed canonical map is `(properSetBaseChangeTransformation f g f' g'
  sq.w).app F`. Its type is `f.direct ⋙ g.inverse ⟶ g'.inverse ⋙ f'.direct`,
  hence its component has source g⁻¹ f_* F and target f'_* g'⁻¹ F.
- The specified counit normalization is supplied by `mateEquiv f.adj f'.adj`.
  Its input is `properSetInverseImageSquare`, from g⁻¹ then f'⁻¹ to f⁻¹ then
  g'⁻¹. The mate formula is the transpose under f'⁻¹ ⊣ f'_* of that comparison
  on f_* F followed by g'⁻¹ applied to f's counit. The definition of `mateEquiv`
  in Mathlib/CategoryTheory/Adjunction/Mates.lean:84 gives this formula by
  naturality of the comparison and the two triangle identities. No unspecified
  comparison or map is a theorem hypothesis.
- The composition comparison comes from `enlargedBaseChange_composition`:
  its two projection equations uniquely determine its chosen isomorphism.
  `Functor.sheafPushforwardContinuousComp'` induces the direct-image comparison;
  the middle scheme-restriction equivalence cancels by its unit isomorphism.
  `conjugateIsoEquiv` of the composite adjunctions gives the specified
  adjunction-compatible inverse-image comparison.
- “is an isomorphism”: `IsIso` of this component, for every `F`.
- “natural in F”: the components belong to the actual `NatTrans`
  `properSetBaseChangeTransformation`, so naturality is part of the map's data;
  componentwise invertibility gives its natural inverse.
- No surjectivity, finite presentation, Noetherianity, representability, group,
  torsion, nonemptiness, or other geometric hypothesis is added.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `etaleTopology`;
  algebraic spaces are the recorded sheaves with representable diagonal and atlas.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`,
  inherited through the existing algebraic-space site construction; ordinary
  Mathlib `Sheaf` supplies the actual sheaf category. The metatheoretic size
  node has no declaration, as its record expressly states.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`, the recorded enlarged-site
  dependency module, publicly retains `AtlasEtaleRestriction` and
  `EnlargedEtaleRingedSite`: `enlargedBaseChange_composition`,
  `enlargedDirectImage`, `enlargedSetEquivalence`, `enlargedSmallDirectImage`,
  `enlargedSmallDirectImage_geometric`. The ring-map declaration itself is not
  needed for this set-sheaf specialization.
- `Sheaf.AlgebraicGeometry.EnlargedChartRingedMorphism`:
  `enlarged_chart_ringed_morphism`, the canonical geometric/chartwise interface;
  imported publicly as the node's recorded statement dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, retained by the enlarged-site module. Its
  fibre-product universal property is represented by Mathlib `IsPullback` here.
- Proof-only imports: `Sheaf.AlgebraicGeometry.SpaceChangeBase`
  (`exists_spaceChangeBase`) and `Mathlib.CategoryTheory.Sites.Limits`
  (`Sheaf.createsLimitsOfShape` and the sectionwise limit interface of
  `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`). The remaining proper
  permanence, weak Chow, scheme set-sheaf base change and proper-surjection
  equalizer proof nodes currently have no recorded Lean modules, so no imports
  for them can yet be written. Their full proof plan is in the theorem docstring.

Source and edge cases: read Stacks spaces-more-cohomology.tex,
`lemma-proper-base-change-f-star` (Tag 0DG0), statement and full proof. Checked
empty Y and empty Z': their sheaf topoi and the same mate definition still apply,
with no nonempty binder. Identity f and identity g reduce to the adjunction and
composition identities. A proper closed immersion is allowed without
surjectivity. General proper morphisms of spaces need not be representable and
are allowed by `MapIsProper`. Arbitrary set sheaves, including those with empty
sections or without any algebraic structure, have exactly the same type.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Proper base change for arbitrary sheaves of sets on
  the small etale sites of algebraic spaces"`: 8 hits, including
  `IsProper.isStableUnderBaseChange` and scheme étale/pullback property instances;
  no set-sheaf proper base-change theorem for algebraic spaces.
- `msearch.py ... loogle '"baseChange", "Sheaf"'`: 2 hits, both
  `Precoverage.isSheaf_toGrothendieck_iff...`, not this statement.
- `msearch.py ... grep 'proper.*base.?change|base.?change.*proper'
  AlgebraicGeometry`: 25 hits, scheme morphism property stability, no matching
  theorem on algebraic-space set sheaves.
- `rg` in `lean/WeilConjectures` for the item id: no hit. Broader proper/base-change
  searches find scheme and derived module/torsion results, not this statement.
- `rg` in `lean/Sheaf` for set-sheaf/base-change and the exact Stacks tag finds
  scheme `Etale.setBaseChangeArrow` and many module variants, not this result.
  Searching `smallEtaleMorphism` and `enlargedSmallDirectImage` located the
  already-landed geometric-points module. In the repaired delivery its alias
  is expanded directly to the existing enlarged-site theorem's `.choose`, so
  neither the geometric-points module nor its node is a dependency.
- Read Mathlib `Sites/Continuous.lean` composition APIs and
  `Adjunction/Mates.lean` mate/conjugation APIs. These provide the canonical
  map machinery, not the geometric invertibility assertion.

Validation: the delivered module passed `scompile.py` in sandbox and library
module mode, with no errors or non-sorry warnings. An initial inverse comparison
had its conjugation orientation reversed; the two adjunctions and direct-image
comparison were reversed to give exactly the direction in the node. No statement
correction, new definition node, dependency replacement, or disputed statement.


## Repair of return at 56d162de7044

H2: Removed `lem-sfb-space-geometric-points-conservative` from `stmt_deps` and
removed the `SpaceGeometricPointsConservative` public import. Each former
`smallEtaleMorphism f` occurrence is now the direct expression
`(enlargedSmallDirectImage_geometric.{u, w} f).choose`, including inverse images,
direct images, composite adjunctions, and the commuting-square equality
transport. This uses the already-cited enlarged-site node exactly as requested.
No replacement definition of `smallEtaleMorphism` or additional node is introduced.
The chosen expression is definitionally the former alias; the four maps,
projection-normalized comparison, counit mate, theorem signature, coefficient
universes, and edge cases retain their checked meanings. Updated `lean.note` to
record this repair. Compared the retained packet with current main: the only
node field changed is now `lean`; its original eight statement dependencies and
all other fields are taken from current main.

Advisory on proof imports: `SpaceChangeBase` and `Sites.Limits` are retained as
plain proof-only imports because stages/2-statements.md §3(7) expressly requires
imports of recorded proof dependencies even while the proof is `sorry`. They
supply the Spec Z reduction and sectionwise-limit steps of this node's proof
plan; neither enlarges the public statement dependency list.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
