## Worker report

The delivery states `AlgebraicGeometry.strict_fan_chart_local_comparison` in
`Sheaf.AlgebraicGeometry.StrictFanChartLocalComparison`. Its sole postponed theorem
has proof `sorry`; its docstring reproduces the node's five-step proof. No node
statement, dependencies, proof, or other existing field changes: only `lean` is added.

Source read: ILO, Exposé VIII, printed p.109, proof of 3.3.15 (PDF page 115),
paragraph beginning “Choose a point”. The statement is its strict specialization:
the smooth characteristic homomorphism in that paragraph is an isomorphism.
The point-local affine models are those of VIII 3.1.8(ii), 3.1.10(ii).

Hypotheses and clauses, individually:

- The source and target are fs log schemes: `{Y X : FineSaturatedLogScheme.{u}}`.
  This reuses the recorded fs structures and the source's standing locally Noetherian
  convention already carried by that structure; no extra scheme condition is imposed.
- The log morphism is `(f : EtaleLogHom Y X)`, and strictness is `(hf : f.IsStrict)`.
  The recorded definition fixes the canonical characteristic map by its graph, rather
  than accepting an arbitrary characteristic isomorphism.
- The two fine fans are `{G F : FineFan.Fan.{u}}`. The charts are
  `(d : LogFanChart Y G)` and `(c : LogFanChart X F)`. Each chart carries the
  Zariski-log condition and bijective stalk maps. Thus neither Zariski hypothesis
  is omitted, and neither chart is replaced by a global monoid chart.
- Every point is covered: the last parameter is `(y : Y.scheme)`, an ordinary point,
  with no geometric-lift hypothesis or choice of residue field.
- The fan localizations are `L : FineFan.PointLocalization F (c.map.hom.base (f.base y))`
  and `K : FineFan.PointLocalization G (d.map.hom.base y)`. Their `generalizations`
  fields say `t ∈ openSet ↔ t ⤳ z`. The direction is deliberate: `t` specializes
  to `z`, so `t` is a generalization of `z`. Their `mem` fields place the points
  in these opens. Their inherited affine isomorphisms have coordinate monoid
  exactly `FineFan.stalk F.space.presheaf z` (respectively the stalk of `G`).
- Those monoids are fine by `PointLocalization.fine`, and sharp by the existing
  fan structure. `PointLocalization.normalization` identifies every coordinate
  element's germ with its original fan stalk element, using the restriction's
  canonical stalk map. Consequently these are the canonical stalk coordinates,
  rather than arbitrary coordinates differing by an automorphism. This renders
  the node's assertion about the sharp monoid of sections of the localization.
- The Zariski neighbourhood is `(U : Y.scheme.Opens)` with `y ∈ U`.
  The next two conjuncts require its images under `c ∘ f` and `d` to belong to
  `L.openSet` and `K.openSet`, respectively.
- The isomorphism of localized fans is
  `e : G.space.restrict K.openSet.isOpenEmbedding ≅
       F.space.restrict L.openSet.isOpenEmbedding`.
  An isomorphism of these sharp sheafed spaces is automatically local on stalks,
  and hence an isomorphism of the localized fans in the recorded sense.
- The morphisms `a` and `b` are restrictions into these localized targets.
  Their first two equations, after composing with the canonical open inclusions,
  identify them with `(c ∘ f)|_U` and `d|_U`. The equation `a = b ≫ e.hom`
  is equality of the entire sheafed-space morphisms, including their sheaf maps.
- The equivalence `α` has domain the actual stalk of `F` at `c(f(y))` and codomain
  the actual stalk of `G` at `d(y)`. The equation
  `(stalkMap d.map y).hom.comp α.toMonoidHom =
   (stalkMap g.map y).hom.comp (stalkMap c.map (f.base y)).hom`
  fixes it as the prescribed composite `b⁻¹ t a` of chart and log stalk maps.
- Finally, the equation involving `SheafedSpace.Γ.map e.hom.op` and the two
  `FineFan.affinePullback` maps says that the induced homomorphism on sections
  is precisely `α`, in the normalized stalk coordinates. This separately retains
  the last sentence of the node; it is not left implicit in the commuting square.

The helper `EtaleLogHom.SharpSpaceMap` supplies the otherwise missing notation for
the given log morphism's canonical Zariski characteristic map. Its data are a natural
transformation on the already defined sharp sheaves, with the underlying continuous
map fixed definitionally to `f.base.base`. Its `onLogSections` field is the equality
on EVERY actual log section on EVERY relative pair of Zariski opens, using the given
`f.sectionMap`. Quotienting by units determines the map on raw characteristic sections;
sheafification then determines it on the sharp sheaves. Thus this interface specifies
the actual canonical map, rather than an arbitrary arrow. Its existential occurrence
asserts that this specified interface is inhabited, and does not add a hypothesis.
`SharpSpaceMap.map` bundles those data without any choice or postponed proof.
`FineFan.PointLocalization` similarly packages exactly the localization already
mentioned in this node. Both are helpers belonging to the item's comparison notion,
listed in `lean.declarations`, with source and blueprint docstrings. There is no
independent missing notion or dependency-module replacement.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `FineSaturatedLogScheme`,
  `EtaleLogStructure`, `EtaleLogHom`, its `sectionMap`, and the real characteristic
  quotient underlying the sharp-space construction.
- `Sheaf.AlgebraicGeometry.FineFanBlowup`: `FineFan.Fan`, `FineFan.IsFine`,
  `FineFan.AffineOpen`, `FineFan.affine`, `FineFan.stalk`, `FineFan.germ`,
  `FineFan.stalkMap`. No duplicate notion of fan, spectrum, stalk, or chart is defined.
- `Sheaf.AlgebraicGeometry.LogFanChartBlowup`: `EtaleLogHom.IsStrict`,
  `LogFanChart`, `logOpenEtale`, `EtaleLogStructure.sharpSpace`,
  `EtaleLogStructure.sharpSection`. This is the recorded chart interface used unchanged.
- `Sheaf.AlgebraicGeometry.AffineFanHomUniversal` (recorded proof dependency):
  `FineFan.affinePullback` supplies the actual coordinate-section map;
  `FineFan.affine_hom_universal` is imported for the future proof.
- Mathlib: `SheafedSpace.restrict`, `SheafedSpace.ofRestrict`, `SheafedSpace.Γ`,
  `Opens.map`, and the topological specialization relation.

Searches performed before writing (the wrapper log is `searches.jsonl` in the sandbox):

- `msearch.py leanfinder`, query “Strict morphisms of fine saturated Zariski log schemes
  locally identify fan charts by isomorphisms of localized fans”: eight hits about
  ordinary scheme local isomorphisms, spreading out, and ring stalks; no log/fan statement.
- `msearch.py loogle`, query `"FanChart"`: zero hits.
- `msearch.py grep`, query `FanChart|KatoFan|MonoidalSpace|LogStructure`: zero Mathlib hits.
- `msearch.py leansearch`, query “Strict log morphisms identify the characteristic sheaves
  and locally compare fan charts”: eight hits about locally ringed spaces, sheaf
  injectivity, and morphism-property strictMap; no characteristic-monoid fan result.
- `rg` in the upstream `WeilConjectures` source for the preceding notion names and for
  the exact item id: zero hits. The requested upstream-id search therefore supplies
  no existing declaration to attach.
- `rg` in the project's `lean/Sheaf`: the existing fan and log-chart declarations above
  supply the dependency notions, but not this local comparison or these normalized
  helper interfaces. Exact-name searches for `SharpSpaceMap`, `PointLocalization`,
  and `strict_fan_chart_local_comparison` found no competing declarations (unrelated
  `graphPointLocalizationLift` is a six-functor point construction).

Edge cases checked: empty source has no point and hence introduces no point obligation;
empty target admits no point image from a nonempty source. The zero/rank-zero monoid
is retained (multiplicative identity `1`, corresponding to additive `0`); the initial
neighbourhood is used when there are no generators. The generic prime and primes with
no generators outside them are covered, since the empty product is `1`. No finiteness
or quasi-compactness of the whole fans or schemes is imposed. Strict identity morphisms,
identical charts, and charts related by a coordinate automorphism are included; germ
normalization is what fixes the coordinate map in the last case. The single universe
`u` is the existing schemes/fans/coefficient-monoids universe of the dependencies; all
variables and universes are explicitly bound and `autoImplicit` is false.

Validation: `scompile.py` compiled both the sandbox view and the declared library module
cleanly, within the prescribed 60-second per-file limit. The initial module-system header
could not import the already published non-module chart dependency; the file therefore
uses the same ordinary import form as that dependency. A noncomputability diagnostic on
bundling the sharp map was repaired with `noncomputable def`. No axiom, opaque data,
choice of an unspecified map, hollow definition, extra theorem, or proved theorem is added.
No statement dispute or node fault was found.

## Second reading by Q154

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
