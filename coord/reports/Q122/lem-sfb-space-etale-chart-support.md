## Worker report

Stated `AlgebraicGeometry.AlgebraicSpace.etale_chart_moduleSupport` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport`. Its proof is `sorry`;
no definition or proof is introduced. The unchanged mathematical statement agrees
with Stacks 07TY, `spaces-morphisms.tex`, lemma-support-covering (lines 2800–2828).
Also read 05VP, `spaces-properties.tex`, lemma-stalk-quasi-coherent (lines
5287–5328), and the support definition 04KA and its preceding paragraph.

Hypothesis and clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, using Mathlib's scheme, with arbitrary u.
- An algebraic space over S: `{X : AlgebraicSpace S}`, the existing full
  subcategory of fppf sheaves with representable diagonal and an étale atlas.
- A quasi-coherent module on its small étale ringed site: `(M : X.QCoh)`.
  Its underlying module is `M.obj`; quasi-coherence is `M.property`, namely
  Mathlib's `SheafOfModules.IsQuasicoherent`, not a finite-presentation predicate.
- Geometric-stalk support on X: `moduleSupport M.obj`, the already-landed
  def-sfb-space-module-support. Its definition is the nonzero-germ criterion
  in actual étale neighbourhoods, written with ordinary chart points and all
  refinements. It is representative independent and does not choose a geometric
  lift. Thus the introductory support convention, including independence, is
  reused from its owning definition rather than redefined or assumed here.
- Any étale scheme map e: `(T : X.EtaleSite)`. The bundled datum `T.obj.left`
  is the scheme over S, `T.obj.hom` is its map h_U → X, and `T.property` is
  representable étaleness. Every scheme-source étale map has this form.
- The quasi-coherent Zariski module M_U is
  `(X.schemeRestriction T).obj M.obj`. The existing functor restricts M to open
  subschemes of U, transporting scalars through the canonical regular-functions
  isomorphism. This is exactly the inverse, restriction-to-opens direction of
  lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, not an arbitrary
  module supplied as extra data. Its recorded module is publicly imported.
- Its ordinary support is the left set
  `{x : X.etaleForget.obj T | ¬ Subsingleton
  (((X.schemeRestriction T).obj M.obj).presheaf.stalk x)}`.
  Here `presheaf.stalk` is Mathlib's ordinary additive module-stalk carrier,
  also used by `PresheafOfModules.moduleStalkFunctor`; its zero object is
  equivalent to a subsingleton carrier. This is not vanishing of the fibre.
- The induced point map is `schemePointMap T.obj.hom`; by its actual definition
  it sends u to the class of e composed with Spec κ(u) → U.
- The conclusion is literal set equality with
  `schemePointMap T.obj.hom ⁻¹' moduleSupport M.obj`.
- There are no finite type, Noetherian, finite-generation, or surjectivity
  hypotheses. In particular the chart can be empty or have proper open image.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (transitively public via AlgebraicSpace).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `EtaleSite`, `etaleForget`, `Modules`, `structureSheaf`, `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, whose
  full-subcategory predicate is Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.zariskiEtaleModuleRestriction` and
  `scheme_zariski_etale_quasiCoherent_equivalence`. Its inverse on
  quasi-coherent modules is restriction to opens, agreeing with schemeRestriction.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`. The displayed stalk has
  their Mathlib carrier, without a private construction of germs.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`,
  with `Point` and `schemePointMap` from AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`: `moduleSupport`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.

The last two owning definition nodes are added to stmt_deps under the rule
allowing added dependencies that already have landed Lean records. No new node
or dependency module is necessary. No statement correction is necessary.

Proof imports include the stated strict-henselization faithful-flatness result,
Mathlib's faithfully-flat definition, and tensor product. The currently unrecorded
lem-sfb-space-quasicoherent-geometric-stalk-tensor,
lem-sfb-space-strict-local-flatness, and
lem-sfb-etale-geometric-point-specified-lift cannot yet be imported by recorded
module; their roles are retained explicitly in the four-step proof docstring.
The item does not need them as statement dependencies.

Edge cases checked mathematically before writing:

- Empty chart: both subsets of its empty point type are empty.
- Zero M: every ordinary or geometric stalk is zero; both supports are empty.
- Nonsurjective chart, including an open immersion: the assertion tests only
  inverse-image points and makes no assertion that the chart meets every point.
- No finite generation: faithful flatness detects zero for arbitrary modules;
  using residue-field fibres or Nakayama would wrongly need extra hypotheses.
- A scheme regarded as an algebraic space and its identity chart recovers the
  ordinary support equality.
- Arbitrary characteristic and non-Noetherian schemes are retained. All
  schemes, module section carriers, and chart points use the common project
  universe u, while the existing Point type remains in u+1.

Searches actually performed with msearch.py:

- leanfinder, `Support of quasi coherent module on algebraic space pulls back
  to support of ordinary module stalk on etale scheme chart`: eight hits,
  chiefly Scheme.IdealSheafData.support_comap/support_map and ring-spectrum
  Module.support_subset_preimage_comap. None states the algebraic-space
  quasi-coherent module stalk assertion.
- loogle, `AlgebraicGeometry.AlgebraicSpace.moduleSupport`: zero hits;
  unknown identifier (this service indexes Mathlib, not the project's declaration).
- grep, `support.*etale|etale.*support|schemeRestriction`, Mathlib
  AlgebraicGeometry: zero hits.
- leansearch, `support quasi coherent module etale scheme chart algebraic
  space`: eight hits, all generic quasi-coherence definitions or witness
  fields, including SheafOfModules.IsQuasicoherent; no matching theorem.
- Direct rg in lean/WeilConjectures and lean/Sheaf for support, moduleSupport,
  schemeRestriction, and chart/stalk combinations found the existing support
  and restriction definitions above, and downstream uses in coherent-support
  statements, but no existing theorem asserting this equality.
- `grep -rn 'lem-sfb-space-etale-chart-support' lean/WeilConjectures` found no
  declaration. A matching-name search also found no etale_chart_moduleSupport.
- DAG records of def-sfb-space-module-support and
  def-trf-space-module-scheme-restriction were read together with their complete
  definitions and docstrings. Reusing them avoids duplicating either notion.

No STATEMENT-DISPUTED issue was found. `scompile.py Q122
lem-sfb-space-etale-chart-support <module>` compiled both its sandbox probe and
its library module cleanly (14.3 s and 4.5 s, within the default 60 s limit).

## Second reading by Q122

Performed a separate second pass over the node, the source 07TY, and the finished
signature in this worker. The dispatcher explicitly forbids starting another
agent; the maintainer's delivery review supplies the independent reader.

Rechecked that X is an algebraic space over the bound S, that X.QCoh is exactly
quasi-coherence on the small étale ringed site, and that T includes a scheme
source and étaleness without surjectivity. Read schemeRestriction's full
implementation: it is precomposition along open subschemes with the canonical
ring comparison, so M_U is the inverse equivalence image specified in the node.
Read moduleSupport's full implementation: it is geometric nonzero-germ support,
with no choice of representative, so the independence convention is preserved.
The left set uses ordinary stalks, and the point preimage uses the residue-field
class map, as required. Equality has exactly the source's direction and scope.
No added clause, hypothesis, finiteness restriction, fibre-stalk substitution,
unbound variable, or local notation was found. No change was needed in this pass.
