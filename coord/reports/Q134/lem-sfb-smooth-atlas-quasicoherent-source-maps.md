## Worker report

Item: lem-sfb-smooth-atlas-quasicoherent-source-maps. The delivery states
`CategoryTheory.smoothAtlas_quasicoherent_source_maps` in
`Sheaf.AlgebraicGeometry.SmoothAtlasQuasiCoherentSourceMaps`. Its proof is `sorry`;
all three helper definitions have explicit data. There are no new DAG nodes,
dependency repairs, or statement corrections.

Source read: Stacks stacks-sheaves.tex, lemma-map-from-quasi-coherent (076S),
including the comparison diagram and proof; algebraic.tex,
lemma-stack-presentation (04T5) and remark-flat-fp-presentation (04WY).
Read the latest blueprint's sk-thm-sf-ctf-stability unit statement. This is an
internal atlas-Hom prerequisite, not that unit's own statement.

Hypothesis and clause correspondence:

* Size convention: explicit universes `u v w`; `Scheme.{u}`, arbitrary
  `BasedCategory.{v,w}`, and section/ring universe `max (u+1) v w`. Neither site
  universe is equated to the scheme universe. The `ULift` rings are precisely
  the dependency's rings, not new coefficient rings.
* Base scheme and algebraic stack: `{S : Scheme.{u}}`, `C`, and
  `hC : IsAlgebraicModuliStack C`. The big fppf module ring is the existing
  `moduliModuleRings C hC.1.1`; fibredness is taken from the stack predicate.
* Smooth surjective scheme atlas: `U : Over S`, the based functor `a`, and
  `ha : IsSmoothModuliAtlas C U a`, with exactly the chart-test convention of
  the recorded dependency. There is no etaleness or quasi-compactness condition.
* Actual overlap R: `R : AlgebraicSpace S`, `e` mapping its discrete fibred
  groupoid into `moduliTwoFiberProduct a a`, and `he : e.toFunctor.IsEquivalence`.
  These bind an arbitrary presentation of the actual self-relation, which
  exists by the atlas hypotheses. They do not impose representability of R by
  a scheme or triviality of stabilizers. The first and second projections are
  the `.obj.left` and `.obj.right` of the existing comma object; `.obj.hom` is
  its specified invertible comparison over the identity of the base.
* G and H: both belong to `ringedSiteModules` over the existing fppf ring sheaf;
  only `hG : G.IsQuasicoherent` is required. This is Mathlib's local-presentation
  predicate. In particular H has no quasi-coherence, comparison-isomorphism,
  cartesian, flatness, finiteness, or section-surjectivity hypothesis.
* Small-etale restrictions: `moduliEtaleChartRestriction` is exactly forgetting
  the sheaf condition followed by `PresheafOfModules.pushforward₀` along the
  existing inclusion of etale scheme charts and the based functor. Thus values
  and maps are literally those of G or H on the chart object; no sheafification
  replaces H. Precomposition is already a sheaf here: an etale chart cover
  maps to an fppf cover of the same underlying schemes. Its ring presheaf is
  the same lifted regular-function ring. Hom sets in these underlying module
  presheaves equal Hom sets of the module sheaves because forgetting the sheaf
  condition is fully faithful. For U, `schemeSpace U` retains the representable
  sheaf, and its etale scheme-chart site is the small-etale site of U, including
  all U-morphisms between charts. No larger big-site Hom is substituted.
* R restrictions: `moduliAtlasRelationObject a R e` is the first projection
  composed with a. The comma isomorphism identifies the second projection with
  it. The same `moduliEtaleChartRestriction` gives G_R and H_R on all etale
  scheme charts of R.
* Canonical comparisons: `ModuliAtlasMapCompatible` uses the comparison squares
  on local generators, rather than choosing comparison maps. A local tensor
  `1 tensor s`, for any etale W of U and any map of the chart V of R to W over
  projection i, is sent by the comparison to `M.val.map arrow.op s`. For p1
  this arrow is `a.toFunctor.map f`; for p2 it is the comma comparison followed
  by `a.toFunctor.map f`. These are literal restrictions of the given module.
  The predicates quantify over ALL V, W, f, s, including every factorization,
  exactly the chart-index adjunction of the module-functor dependency. The
  underlying common map d is a morphism of modules on R, so linearity extends
  the equations from `1 tensor s` to arbitrary `r tensor s`, and naturality
  extends them across chart refinements. The adjunction identifies these
  equations with `c_i^G ≫ d = p_i^*b ≫ c_i^H` for i=1,2. This uses actual
  comparison maps and does not postulate an arbitrary map in their place.
* Source comparison and delta: the scheme-restriction dependency gives
  invertible canonical comparisons for G on every chart. Therefore the first
  square uniquely forces `d = inverse(c1G) ≫ p1*b ≫ c1H`. Substitution into the
  second, or composing with c1G and inverse c2G, is exactly the node's
  `c1H o p1*b = c2H o p2*b o deltaG`, with
  `deltaG = inverse(c2G) o c1G`. Thus the existential common-map predicate is
  precisely the specified subset, with no extra compatibility requirement.
  This is also the commutative diagram explicitly specified by source 076S.
* Bijection and unique extension: `Function.Injective restriction.map` is the
  uniqueness clause, and for every b the equivalence between existence of f
  with `restriction.map f = b` and `ModuliAtlasMapCompatible ... b` is exactly
  the image assertion. Together they give a bijection onto the indicated set.
  No separately chosen equivalence or arbitrary bijection changes that map.
* The theorem makes no quasi-compactness, finiteness, or Deligne--Mumford
  assumption. In particular all etale charts of the algebraic space R remain
  available, rather than replacing R by a single scheme chart.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
* `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`.
* `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (publicly imported by the
  stack definition): `BasedCategory`, `BasedFunctor`, `IsFibredInGroupoids`,
  `discreteModuli`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`.
* `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra` (publicly imported by
  scheme restriction): `moduliModuleRings`, its `moduliFppfTopology` and
  `moduliStructureSheaf`, and the slice sheafification instances.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  publicly available from the above; its objects and morphisms are Mathlib's.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.EtaleSite`, `IsEtale`. The recorded QCoh module publicly
  exposes this dependency and the original `SheafOfModules.IsQuasicoherent`.
* `Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction`:
  `exists_moduliSchemeRestriction` and `ModuliSchemeRestriction.comparison`,
  `comparison_sections`, `tensorPullback_agreement`; these explain invertibility
  and the normalized tensor interpretation of the source comparisons.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  `Scheme.Modules.tensorPullbackSectionAdjunction` and `tensorPullbackSection`,
  publicly exposed by scheme restriction; ordinary pullback is unchanged.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleChart`, `moduleChartDiagram`, `ModuleDirectImageModel`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection`.
  Their chart-index adjunction is precisely the sectionwise rendering of the
  comparison squares. No alternate tensor-pullback functor is defined here.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, used
  through the existing algebraic-space etale chart site.
* `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`:
  `AlgebraicSpace.schemeSpace`. Added its already-landed owner node
  `def-trf-scheme-algebraic-space` to stmt_deps; no copy of this construction.
* Proof-only `Mathlib.AlgebraicGeometry.Morphisms.Smooth` supplies the recorded
  instances for `lem-pc-smooth-flat`. The groupoid presentation and groupoid-Hom
  proof dependencies have no Lean module yet, so no fictional imports are added.

Edge cases checked before writing: empty atlas (surjectivity forces the stack
empty); empty overlap charts (module presheaf maps still impose naturality,
including the empty cover); zero G or H; identity atlas; non-scheme R;
non-quasi-coherent H and noninvertible target comparisons; no finite atlas or
finite presentation of the module. The section equations never invert H maps.
The common-map formulation includes both projections and the actual two-isomorphism;
it is invariant under changing the presentation e. Independent stack object and
morphism universes are retained, with coefficient carriers in their common bound.

Searches (2026-10-24):

* msearch leanfinder: "Maps from a quasi coherent module on an algebraic stack to
  an arbitrary module descend from compatible maps on a smooth atlas". Eight
  presentation/quasi-coherence hits, including `QuasicoherentData.presentation`;
  no atlas descent Hom theorem.
* msearch loogle: `"SheafOfModules", "homEquiv"`. Twelve hits about unit/free
  module presheaves and module colimits; none states this atlas-Hom theorem.
* msearch grep: `atlas.*[Mm]odule|map.from.quasi.coherent|AlgebraicStack`,
  Mathlib AlgebraicGeometry: zero hits.
* msearch leansearch: "Morphisms from a quasi coherent module to an arbitrary
  module descend uniquely from a smooth atlas of an algebraic stack". Eight
  hits, mainly `SheafOfModules.IsQuasicoherent`, its constructors, and scheme
  module Hom; no match.
* rg over both live Lean roots for atlas/module, smoothAtlas, the item id and
  moduli restriction Hom: only unrelated algebraic-space atlas equalizers and
  references in StackQcohAbelian. Exact names of the four new declarations have
  no source or Mathlib matches. The requested grep for the item id in
  WeilConjectures also has no hit. The upstream-name JSON has no item match.

Validation: the whole delivered module compiled separately as sandbox and as its
real module name through scompile.py, clean (4.2 s and 4.4 s); expected `sorry`
is the only postponed theorem. Final delivery preflight/compile is run below.
No STATEMENT-DISPUTED flag or node fault is asserted.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
