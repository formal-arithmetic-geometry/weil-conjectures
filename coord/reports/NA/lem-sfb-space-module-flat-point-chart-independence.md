## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceModuleFlatPointChartIndependence` states
`AlgebraicGeometry.AlgebraicSpace.module_flat_point_chart_independence`, with `sorry`
as its entire proof. The fully defined helper `ModuleIsFlatAtChartPoint` expands the
ordinary relative stalk-flatness condition; it constructs no replacement stalk,
restriction functor, point, or scalar map.

The source was read directly in `literature/stacks-project/spaces-morphisms.tex`,
Tag 05VU, lemma-flat-at-point and its proof (lines 6114–6177). Its arbitrary
chart diagram specializes to the identity target chart of the scheme T.
The natural-language statement and accepted proof split are unchanged.

Hypothesis and clause correspondence:

- S is a scheme: `{S : Scheme.{u}}`.
- X is an algebraic space over S: `{X : AlgebraicSpace S}`, the existing full
  subcategory of fppf sheaves with representable diagonal and an etale atlas.
- T is an S-scheme: `{T : Over S}`; its underlying scheme is `T.left`.
- f is the morphism X to T: `(f : X ⟶ schemeSpace T)`. `schemeSpace` is the
  existing Yoneda algebraic-space presentation of an S-scheme.
- M is a quasi-coherent small-etale O_X-module: `(M : X.Modules)` and
  `(hM : M.IsQuasicoherent)`, using the Mathlib predicate on the existing site.
- The size convention is explicit: `universe u`, `Scheme.{u}`, `Ω : Type u`.
  The existing etale site has object universe u+1, with u-small coefficients;
  no equality of site object and morphism universes is imposed.
- x is an ordinary space point: `(x : Point X.obj.obj)`, using the recorded
  field-valued point quotient, not a chosen geometric point as the point type.
- A representable etale scheme chart e:U→X is precisely `U : X.EtaleSite`.
  No surjectivity is required of individual charts. Its ordinary point is
  `u : X.etaleForget.obj U`. The condition that u lies above x is exactly
  `schemePointMap U.obj.hom u = x`.
- The quasi-coherent Zariski module M_U is `(X.schemeRestriction U).obj M`.
  This is restriction to actual open subschemes, the specified inverse of the
  Zariski/etale comparison. Etale tensor pullback is restriction on the localized
  etale sites, so the values are exactly M on the composites of these opens
  with U→X. This uses the already-defined restriction, not arbitrary comparison
  data and not a second definition of e^*M.
- The helper takes its ordinary stalk by `RingedSpace.moduleStalkFunctor`.
  Write a for `(yoneda.preimage (U.obj.hom ≫ f.hom.hom)).left`; full faithfulness
  of Yoneda recovers the actual scheme composite U→T. The helper is precisely
  `Module.Flat (T.left.presheaf.stalk (a u))` of that stalk after applying
  `ModuleCat.restrictScalars (a.stalkMap u).hom`. For a point u above x, a(u)
  is f(x); no arbitrary ring action is supplied.
- Clause (a) is `∃ (U : X.EtaleSite) (u : X.etaleForget.obj U),
  schemePointMap U.obj.hom u = x ∧ ModuleIsFlatAtChartPoint f M U u`.
- Clause (b) is `∀ (U : X.EtaleSite) (u : X.etaleForget.obj U),
  schemePointMap U.obj.hom u = x → ModuleIsFlatAtChartPoint f M U u`.
  The first conjunct of the theorem is exactly (a) iff (b).
- Every geometric representative is quantified by `Ω : Type u`, `[Field Ω]`,
  `[IsAlgClosed Ω]`, the structural map `s : Spec (.of Ω) ⟶ S`, and
  `xbar : yoneda.obj (Over.mk s) ⟶ X.obj.obj`. The explicit quotient equality
  `Quot.mk _ (PointRepresentative.mk Ω s (yonedaEquiv xbar)) = x` expresses
  that it represents the specified x. These are all such representatives.
- Its target is literally `xbar ≫ f.hom.hom`. Its etale local ring is
  `SingleComplex.stalkRing s (xbar ≫ f.hom.hom)` for the scheme represented by T.
  The source module is `(SingleComplex.stalkModel s xbar).modules.obj M`.
  `ModuleCat.restrictScalars (SingleComplex.stalkMap f s xbar)` supplies the
  canonical target action. The second conjunct asserts (a) iff this geometric
  module is flat, separately for every representative above x.
- These geometric ring and additive module stalks have the actual pointed-affine-
  etale-neighbourhood colimit universal properties in `StalkModel`; they are
  the established small-basis version of the pointed-neighbourhood colimits.
- No finiteness, Noetherian, separation, or flatness assumption on f is present.

Dependency declarations used (all source signatures and relevant docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, the full
  subcategory of the unchanged Mathlib `SheafOfModules.IsQuasicoherent` predicate.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`, whose inverse
  is restriction to Zariski opens and whose forward functor is tensor extension.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback` and `moduleTensorAdjunction`, the specified tensor
  pullback; etale restriction and the inverse equivalence give the chart module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology` (and its public
  PointClasses import): `Point`, `PointRepresentative`, `schemePointMap`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, the general presheaf-stalk interface
  of the recorded dependency. On ringed-space sheaves use its same ordinary
  stalks via `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`, as the dependency note directs.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`; the item uses its pointwise ordinary-stalk
  formulation and does not assume global flatness of the module.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and the publicly imported
  `Module.Flat` predicate used explicitly for both ordinary and geometric stalks.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.StalkModel`, `stalkModel`, `stalkRing`, `stalkMap`.

The last two definition nodes and `def-pc-module-stalk-functor` were added to
stmt_deps because their already-landed constructions are used explicitly.
No new node, dependency repair, or correction of the item is needed.

The stated proof dependencies are imported without `public`:
`SpaceStrictLocalFlatness`, `StrictHenselizationFaithfullyFlat`,
`FlatnessFaithfullyFlatExtension`, `StrictHenselizationModuleFlatness`, and
Mathlib's algebraic closure. The specified geometric-point lift and
quasi-coherent geometric-stalk tensor nodes currently have no recorded Lean
module, so there is no module to import for them. Their precise roles remain
in the four-step theorem proof docstring, with the complete accepted proof route.

Edge cases checked before writing:

- Empty X: there is no x, so no unwanted nonempty-X hypothesis is introduced.
- A chart missing x contributes no point to the universal clause; the existential
  clause still needs an actual chart point. An atlas supplies one for every x.
- The zero module satisfies both kinds of stalk flatness over every local ring.
- The identity scheme chart gives ordinary relative stalk flatness without any
  restriction on f. In particular the structure map need not be flat.
- For Z/2 on Spec Z at (2), both ordinary and strict-henselian stalk modules
  are nonflat; away from (2) both are zero. Thus pointwise dependence is retained,
  and no clause is silently globalized.
- Noetherian and separated hypotheses play no role in Tag 05VU and are absent.
- All geometric representatives are quantified, including different fields
  representing the same class; no chosen representative replaces that quantifier.

Searches for an existing statement:

1. `msearch.py leanfinder` with query "Relative flatness of a quasi coherent module
   at an algebraic space point is independent of the etale scheme chart and
   equivalent to flatness of its geometric stalk": eight scheme-morphism-flatness
   hits (`Flat.iff_flat_stalkMap`, `Flat.of_stalkMap`, `Flat.stalkMap`, `flat_iff`,
   and related definitions). They concern the structure sheaf of schemes, not
   an arbitrary module on a space at a specified point.
2. `msearch.py loogle` with query `"Flat", "stalk"`: six hits, including the
   three scheme flatness declarations and rank/free-locus statements for finite
   flat modules. None states this criterion.
3. `msearch.py grep` with query
   `flat.*(stalk|etale)|flatness.*(stalk|chart)` in Mathlib/AlgebraicGeometry:
   six hits in Morphisms/LocalFlatDescent and Morphisms/Flat, again scheme maps.
4. `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for this node ID and the names/concepts `ModuleIsFlatAtChartPoint`,
   `module_flat_point_chart_independence`, `flat.*point.*chart`,
   `chart.*point.*flat`: only the parent adic-flatness proof cites the item;
   no existing declaration states it. The explicit requested `grep -rn` for
   the item ID in `lean/WeilConjectures` returned no matches.
5. Broader chart/flat/geometric searches found `SpaceStrictLocalFlatness`, which
   concerns flat morphisms of spaces (their structure sheaves), and
   `AlgebraicSpaceFlatProperCoefficient`, whose predicate is global module
   flatness. Neither replaces the present pointwise arbitrary-module theorem.

Validation: `scompile.py NA lem-sfb-space-module-flat-point-chart-independence`
compiled this file in both sandbox and library module modes successfully (2.4 s
and 2.2 s). No errors or unexpected warnings. The helper has real data and the
only postponed proof is the named theorem. No STATEMENT-DISPUTED issue was found.

## Second reading by NA

A second pass by this worker reread the node and module together; no other agent
was started, as the dispatcher brief prohibits that. The maintainer supplies
the independent review. The checks focused on retaining the arbitrary specified
point x, the existential/universal chart quantifiers, the ordinary target local
ring (not the chart's own local ring), and a separate equivalence for every
geometric representative. The concrete scalar restrictions and the quotient
condition were checked against their source declarations. No mismatch or
statement correction was found. The ordinary chart restriction and geometric
stalk nodes, and the ringed-space stalk-functor node, were made explicit
statement dependencies; no definitions were duplicated.
