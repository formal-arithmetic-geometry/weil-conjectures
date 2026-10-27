## Worker report

The delivery states `lem-sfb-space-strict-local-flatness` in
`Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness`, using the existing normalized
geometric stalks and maps. Four theorem proofs are `sorry`; the only helper definition
in that module is an actual colimit leg. The separate definition module
`Sheaf.AlgebraicGeometry.SpaceFlatAtPoint` supplies the missing existential chart
predicate. The item's natural-language statement, proof and proof dependencies are
unchanged. Its statement dependencies gain this definition and three already landed
nodes supplying the canonical stalks and strict-henselization interfaces.

The node and Stacks sources were read together. Clause-by-clause correspondence:

- The base scheme and algebraic spaces are `S : Scheme.{u}` and
  `X Y : AlgebraicSpace S`. This is the recorded fppf-sheaf definition, not scheme-only
  replacements or representable space morphisms.
- A geometric point is `Ω : Type u`, `[Field Ω] [IsAlgClosed Ω]`, its base map
  `s : Spec (.of Ω) ⟶ S`, and `x : yoneda.obj (Over.mk s) ⟶ X.obj.obj`.
  The original section universe is the universe of the recorded space framework.
- The space structure-sheaf stalk is `SingleComplex.stalkRing s x`, the previously
  recorded colimit of actual regular-function rings on a small affine etale basis.
  It is not a newly selected ring or a replacement strict-local model.
- An etale scheme chart is `T : Over S`, `e : yoneda.obj T ⟶ X.obj.obj`,
  `he : IsEtale e`. It need not be surjective. Its fixed geometric lift is
  `t : Over.mk s ⟶ T`, with `ht : yoneda.map t ≫ e = x`.
- `strictLocalChartComparison` gives a unique ring equivalence from
  `Scheme.strictHenselizationRing t.left` to `stalkRing s x`. The scheme ring is the
  existing coordinate-ring colimit computing the scheme's geometric stalk. Its germ
  maps are `strictLocalSchemeGerm`, which is exactly an affine-neighbourhood colimit
  coprojection followed by `Scheme.smallStrictHenselizationColimitIso.inv`. For every
  compatible pointed scheme refinement, the comparison sends a scheme germ to the
  germ of the pulled-back regular function. This specifies the canonical chart
  isomorphism, not just an unspecified ring isomorphism.
- The second identification, with the strict henselization of the ordinary chart
  local ring, is `schemeStrictLocal_presentation`. The center is
  `(Scheme.SpecToEquivOfField Ω T t).1`. The base is its actual scheme stalk,
  `T.presheaf.stalk ...`. The conclusion supplies a separable residue closure `K`,
  its embedding `η : K →+* Ω`, and the recorded
  `Algebra.StrictHenselizationPresentationIn.{u,u}` on the existing scheme stalk
  colimit ring. The first equation identifies the residue embedding with the one
  induced by the fixed geometric point. The equation for every open `W`, every
  affine pointed neighbourhood lying above `W`, and every section of `W` identifies
  the ordinary-stalk algebra map with the germ map. The last equation identifies
  the presentation's residue map on every affine germ with geometric evaluation.
  Thus neither the algebra structure nor the chosen residue pointing is forgotten.
- For arbitrary `g : X ⟶ Y`, the image point is literally `x ≫ g.hom.hom`.
  Its induced ring map is the already recorded `SingleComplex.stalkMap g s x`,
  characterized by pullback of regular functions on compatible pointed charts.
- `geometricStalk_flat_iff` supplies local-ring structures on both stalk rings and
  `IsLocalHom (stalkMap g s x)`. Mathlib's local-hom predicate is equivalent to
  mapping the maximal ideal into the maximal ideal for these local rings.
- The same theorem states `(stalkMap g s x).Flat ↔ MapIsFlatAt g p`, with
  `p = Quot.mk _ ⟨Ω, s, yonedaEquiv x⟩`, the actual field-valued image point class.
  `RingHom.Flat` is the recorded flat-ring-map predicate. No global flatness,
  representability, Noetherian, finite-presentation, or other extra assumption is used.
- The existential definition `MapIsFlatAt` quantifies over `U,V,a,b,h,u`, requires
  `IsEtale a`, `IsEtale b`, the commuting chart square, `schemePointMap a u = p`,
  and `(h.left.stalkMap u).hom.Flat`. This is precisely the final chart criterion
  in the node. `flatAt_iff_chart_stalk` states independence of every choice of such
  a compatible chart and every point above `p`, rather than just one chosen lift.

The declarations used from statement dependencies are:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `EtaleSite`, `etaleForget` and its structure presheaf.
- `WeilConjectures.RingTheory.StrictHenselizationTriples`:
  `AlgebraicGeometry.Scheme.strictHenselization_triples`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with `Module.Flat` underneath.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and the
  `Flat.iff_flat_stalkMap` interpretation; individual flatness is the actual stalk map.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used by
  the recorded representable `IsEtale` predicate on every scheme test.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.Neighbourhood`, `neighbourhoodChart`, `stalkModel`, `stalkRing`,
  and `stalkMap`.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization` and its existing extension:
  `Scheme.strictHenselizationRing`, `strictHenselizationDiagram`,
  `AffinePointedEtaleNeighborhood` and `smallStrictHenselizationColimitIso`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`:
  `Algebra.StrictHenselizationPresentationIn` and its canonical `residueMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`,
  `PointRepresentative`, `schemePointMap`; these are used by the new definition.

All recorded modules of stated proof dependencies are imported. The affine-cofinality
module is exported by `StrictHenselizationExtension`; the scheme-stalk localization
Mathlib files and module-flat-transitivity file are also imported. The two proof
prerequisites `lem-sfb-unramified-etale-compatible-charts` and
`lem-sfb-etale-geometric-point-specified-lift` have no recorded declarations at this
reading, so there are no modules for them to import. Each postponed theorem has its
source, matching node tag, and a complete natural-language proof in its docstring.

Edge cases checked before writing:

- Empty schemes have no geometric point or ordinary point to instantiate these
  assertions; no nonemptiness hypothesis is added. An empty chart cannot carry `t`
  or a point `u`, exactly as in the source.
- Identity and open-immersion charts are admitted; no atlas-surjectivity assumption
  was added to the comparison theorem or the pointwise chart test.
- `Spec k → Spec k[ε]/(ε²)` at its point, for algebraically closed `k`, is nonflat;
  neither side of the flatness equivalence becomes automatically true.
- For an identity map both the ordinary and strict local maps are flat.
- In positive characteristic, `Ω` can be larger than the separable residue closure.
  The presentation uses a separate `K` and its specified embedding in `Ω`; it does
  not incorrectly identify the residue field with all of `Ω`.
- No finite type, finite presentation, Noetherian, separatedness, or perfection
  assumption on the schemes or spaces is introduced. All index/ring universes are
  the ones in the existing recorded stalk and pointed-algebra constructions.

Searches actually run:

- `msearch.py leanfinder`, query “Etale local rings of algebraic spaces agree with
  strict henselizations on scheme charts and detect flatness”; eight related hits,
  including `Flat.iff_flat_stalkMap`, all for schemes or ring maps, no exact match.
- `msearch.py leanfinder`, query “A flat morphism of algebraic spaces is flat on
  geometric local rings”; eight scheme-flatness hits, no space assertion.
- `msearch.py loogle`, query `RingHom.Flat`; twelve ring-flatness API hits.
- `msearch.py grep`, query `AlgebraicSpace|pointSmallEtale` in AlgebraicGeometry;
  five scheme-etale-point hits, no algebraic-space strict-local theorem.
- For the new definition, LeanSearch, LeanFinder, Loogle, and Mathlib grep were
  run with the exact queries and complete returned outputs in its
  `mathlib_searches`. They found only scheme/ring flatness, or zero matches.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id, `MapIsFlatAt`, and the proposed comparison names found no
  duplicates. The broader searches for geometric-stalk and pointed-neighbourhood
  terms found the recorded `SingleComplex` framework, which is reused.
- `rg` over the DAG and a parsed scan of all definition-node statements found no
  definition of pointwise algebraic-space flatness. The module-deformation node
  concerns flat modules over split square-zero bases, not this notion.
- `tools/blueprint_refs.py search 'flat at a point'` returned zero blueprint nodes.
  `ancestor` reports the existing null ancestor of this item's created-node chain;
  the new node preserves that null ancestor and prepends the item to its via chain.

No statement dispute or correction. The first compile exposed only the distinction
between the bundled scheme residue field and the canonical local-ring residue-field
interface, and the center chosen by `SpecToEquivOfField`. The final statement uses
that center and the canonical local-ring residue field explicitly. Both modules
compile cleanly using the prescribed server wrapper.

## New nodes

`def-sfb-space-flat-at-point`, in the item's chapter and unit, defines pointwise
flatness by the exact existential compatible-etale-chart criterion appearing in
the item and in Stacks 03ML(2), 04NC and 04NG. The point classes and chart notions
are the already recorded ones. Its four statement dependencies are exactly the
notions cited in its TeX statement. Searches of all DAG definitions, the blueprint,
Mathlib, and both Lean libraries found no existing definition of this predicate.
The full remote search outputs are recorded in the node. The definition has real
logical data and no proof obligations or `sorry`. Choice independence is stated
in the item's module, not assumed or built into the new definition.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
