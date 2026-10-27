## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeEtaleSquareZeroChartConstruction` states
`AlgebraicGeometry.scheme_etale_square_zero_chart_construction`, with one postponed proof.
The node statement and accepted eight-step proof are unchanged. Four helpers construct
only the literal open-chart functor, its top-open identification, the prescribed
presheafed space, and its quotient arrow. Their data are fully written; no scheme is
selected from a sorried existence theorem. The proof docstring follows all eight DAG
steps and names their inputs.

Source read: `literature/stacks-project/more-morphisms.tex`,
lemma-first-order-thickening (05YV), including its affine section model;
`spaces-more-morphisms.tex`, lemma-first-order-thickening (05ZT), especially the two
paragraphs preceding the algebraic-space presentation; and the recorded 05YT criterion.
The scheme case has no extra base assumption: the first part of 05ZT takes the base
to be Spec Z, and every unital ring sheaf has the unique integer action.

Hypotheses match as follows:

- `T : Scheme.{u}` is an arbitrary scheme. Site objects have universe `u+1` and
  morphisms universe `u`; actual rings and kernel modules have section universe `u`.
  Covering families use an independent universe `v`, so no cardinality restriction
  on the family is imposed.
- `A : Sheaf T.smallEtaleTopology CommRingCat.{u}` gives the entire sheaf of commutative
  unital rings, and `p : A.obj ⟶ T.etaleStructurePresheaf` is a natural unital ring map.
- `M : ringedSiteModules (Scheme.Modules.smallEtaleModuleRing T)` is the specified
  kernel as an O_T-module, using the existing general module-sheaf category.
  `[M.IsQuasicoherent]` is Mathlib's local-presentation predicate used by the dependency
  `def-trf-space-quasi-coherent-module`, with the existing small-site slice instances.
  Its algebraic-space full-subcategory abbreviation is not needed for a scheme site.
- `j`, `hj`, `hinj`, `hker` express the additive inclusion, its restriction naturality,
  injectivity, and equality of its image with the kernel on every chart.
- `hsurj` expresses surjectivity as a sheaf map, by lifts on a covering sieve; it does
  not assume surjectivity on arbitrary sections.
- `hsq` expresses square-zero multiplication on the actual included kernel;
  `hscalar` expresses exactly its prescribed quotient O_T-action. No O_T-module
  structure on A and no split extension are assumed.

Conclusions match as follows:

- `Tplus`, `i`, `IsFirstOrderThickening i` give a scheme and a closed immersion whose
  defining ideal sheaf squares to zero. `IsHomeomorph i.base` identifies the spaces.
  The marked presheafed-space isomorphism `eT` identifies Tplus with exactly
  `(|T|, A restricted to Zariski opens)`. Its reduction equation says the closed
  immersion is induced by p, with identity point map after this identification.
- `IsAffine T → ...` asserts surjectivity on A(T) and that the canonical map
  `Tplus.toSpecΓ` followed by Spec of the prescribed global-section isomorphism
  is an isomorphism. Thus Tplus is canonically Spec A(T), not an arbitrary affine
  scheme abstractly isomorphic to it. `etaleSquareZeroChartTopIso` supplies the
  necessary canonical identification of the top open with the identity chart.
- `E : T.Etale ≌ Tplus.Etale` supplies all lifted charts and all lifted arrows.
  Every object and arrow in its target is étale; its functor laws state identities
  and composition. The natural transformation `r` is the family of reductions.
- For every chart U, `IsFirstOrderThickening (r.app U)` and the marked isomorphism
  `e` identify its lift with exactly the same construction on U's Zariski opens,
  with quotient given by p. Restriction to U_et is equivalently restriction of
  the original sheaf to all objects lying over U; the open-chart functor writes
  its Zariski restriction without introducing a second restricted-extension notion.
- `IsPullback U.hom (r.app U) i (E.functor.obj U).hom` is the requested cartesian
  square with its actual four arrows.
- `ε : E.functor ⋙ i.Etale ≅ 𝟭 T.Etale`, with both projection equations, identifies
  this equivalence specifically with the inverse of base change along i.
- `γ : A.obj ≅ E.functor.op ⋙ Tplus.etaleStructurePresheaf` identifies the entire
  transported ring sheaf, naturally on every étale object and arrow. Its component
  followed by pullback along r is exactly p. Consequently it identifies the kernel
  inclusion with `γ_U ∘ j_U`, which is injective, has the same image kernel, and
  has the same quotient action. No independent kernel choice is made. The marked
  chart isomorphism's global-section equation normalizes γ to that same realization.
- The next affine clause gives both canonical Spec A(U) identification and section
  surjectivity for every affine étale U, not just the identity object.
- Continuity of E and its inverse matches the topologies, and the last displayed
  clause explicitly preserves every jointly surjective étale family, including
  empty families where permitted. `PreservesFiniteLimits E.functor` preserves the
  finite fibre-product diagrams and terminal objects, with their universal maps.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`, through
  `WeilConjectures.AlgebraicGeometry.Thickening.IsFirstOrderThickening` (declaration
  namespace `AlgebraicGeometry`).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: pullbacks/projections,
  used through `IsPullback` and the actual base-change functor `i.Etale`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: supplies the dependency's
  existing `SheafOfModules.IsQuasicoherent` local-presentation API; for this scheme
  site the predicate is used directly, not the space-specific `QCoh` abbreviation.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.smallEtaleModulePresheaf` and `smallEtaleModuleRing` are owned by
  the landed definition node `def-sfb-scheme-zariski-etale-module-constructions`,
  which is cited in stmt_deps. The slice sheafification instances and
  `scheme_zariski_etale_quasiCoherent_equivalence` remain proof inputs, with the
  theorem node retained in proof_deps only.
- `def-sbc-first-order-thickening` records the first-order thickening predicate.
  The chart functor is constructed directly as `restrictFunctor ⋙ Over.map U.hom`;
  it does not use `gabberOpenEtale` and has no Gabber construction statement dependency.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `Etale.isEquivalence_upperStar_of_thickening` and its general-coefficient/site
  implementation `Scheme.Hom.etaleEquivalence` and `i.Etale`. The additive theorem
  alone is not used to define ring transport: the statement uses the actual site
  equivalence with its canonical pullback normalization.

Every recorded proof dependency with a module is imported, including the 05YT ring
criterion, affine quasi-coherent vanishing, long exact sequence, H/Ext comparison,
degree-zero comparison and affine pullback section formula. Mathlib proof leaves are
imported by their source modules: ResidueField, GammaSpecAdjunction, Pullbacks,
LocalizedModule.Exact, ShortComplex.ShortExact and Limits.MorphismProperty.
No new DAG nodes or dependency repairs were needed.

Edge cases checked before and after writing: T empty (zero section rings and only
empty charts); M=0 (identity extension); arbitrary nonsplit square-zero extensions;
nonaffine schemes, without affine intersections; zero rings; zero-rank kernel;
identity arrows and all compositions; empty covering families of empty objects;
arbitrary covering index universes. Local surjectivity was deliberately retained as
an input, with affine section surjectivity only in the conclusion. The canonical
projection equations were checked with Mathlib's pullback convention: base change
is the lifted chart times T, with first projection the reduction and second the
original structural arrow.

Searches made:

- msearch leanfinder: “A square zero extension of the structure sheaf on the small
  etale site is represented by a scheme thickening with functorial etale charts”.
  Eight results, including Scheme.Etale, its forgetful functor and formal
  unramifiedness; no matching realization theorem.
- msearch loogle: `AlgebraicGeometry.Scheme.Etale, SheafOfModules.IsQuasicoherent`.
  Zero hits.
- msearch grep: `SquareZero|squareZero|first.order.thickening` in AlgebraicGeometry.
  Zero hits from the service. Direct rg in Mathlib located the site, scheme,
  closed-immersion, étale and quasi-coherent definitions used above.
- msearch leansearch: “square zero extension sheaf rings etale scheme”. Eight hits,
  on TrivSqZeroExt and Algebra.Extension.infinitesimal; no sheaf realization theorem.
- Direct rg in both project source roots for square-zero/first-order constructions
  found SpaceSquareZeroExtensionData and ZariskiSquareZeroExtension, which have
  different sites/base data, and their realization theorems. Neither states the
  present scheme small-etale-site chart theorem; the space realization actually
  cites this item as a proof dependency, so it must not be used circularly here.
- Direct rg for this exact node id in WeilConjectures returned no declaration;
  Sheaf returned only the downstream space theorem's proof citation.
- DAG and blueprint searches found the already existing space and Zariski notions,
  and no definition that must be copied or added. `blueprint_refs.py search
  'scheme etale square zero'` returned zero blueprint-node matches. Its ancestor
  command confirms the inherited null ancestor on this node; this base metadata
  fault is already recorded by the stage-1 reviewer and is unchanged.

There is no statement correction and no disputed mathematical claim. Server scompile
passes both the sandbox module and its final library name, with no errors or warnings.

## Returned delivery repair

Repaired both H2 points in the independent review of immutable head 6d1b08bea29f.

1. Replaced the statement dependency
   `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence` with its landed definition
   owner `def-sfb-scheme-zariski-etale-module-constructions` (Q128, existing:true).
   Read its statement and Lean record, then checked the actual
   `smallEtaleModulePresheaf` and `smallEtaleModuleRing` definitions. The equivalence
   theorem remains in proof_deps and in the unchanged proof plan/imports.
2. Removed `def-weil-pbc-gabber-h0-zariski-constructions` from stmt_deps and corrected
   the dependency explanation above. The chart helper uses `restrictFunctor` and
   `Over.map` directly, so the previous pattern-based justification was incorrect.

Compared the retained packet with current main: the only original differences were
lean and stmt_deps. Rebased the node metadata on current main, preserving its other
fields. The Lean module and theorem signature are unchanged from the returned delivery;
its clause-by-clause mathematical review therefore still applies. This repair changes
actual dependency metadata and report text, rather than only rebasing the delivery.

## Second reading by NE

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
