## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceMeromorphicGenericChartModel` states
`AlgebraicGeometry.AlgebraicSpace.space_meromorphic_generic_chart_model` with `sorry`.
The other nine declarations are explicit constructions belonging to the maps, restriction
and generic-factor interfaces in this node. There is no other postponed theorem, no new
DAG node, no dependency replacement, and no statement correction. The original statement,
seven-step proof and proof-dependency list are unchanged.

Sources read: `literature/stacks-project/spaces-divisors.tex`, definition
`definition-sheaf-meromorphic-functions` (0EN3), `lemma-describe-S`,
`lemma-meromorphic-quasi-coherent` (0EN6), `lemma-meromorphic-quasi-coherent-agree`
(0EN7), and `lemma-compute-meromorphic` (0ENA), including the displayed formulas and proofs.
The current blueprint files under `literature/blueprint/latest/blueprint/` for
`sk-thm-sf-ctf-stability-direct-images` and its proof were also read; clause (3) is the
proper-direct-image branch recorded in the node's inherited provenance. This supporting
meromorphic lemma does not change that unit's statement.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Regular Noetherian separated algebraic space | `X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))`, `hX : IsRegularNoetherianSeparated X`. The existing predicate is compactness of the point space, `IsRegularScheme` on every étale scheme chart, and the closed-immersion absolute diagonal. `IsRegularScheme` includes local Noetherianity. Separatedness gives quasi-separatedness. No connectedness, integrality, chosen atlas, or nonemptiness is assumed for X. |
| K is the sheafification of fractions; K(L) is tensor localization | `spaceTotalFractionSheaf`, `spaceToTotalFractions` and `spaceMeromorphicLocalization` from the already landed definition node. `meromorphicSmallModule` forgets the localized scalar action using the identity-site pushforward; `meromorphicSpaceModule` transports that object by the inverse of the existing restriction equivalence. These are the same fraction sheaf and scalar extension, on the original site. K applied to the unit is canonically K itself, by extension of scalars of the unit. |
| Natural maps O to K and L to K(L) | The actual `spaceToTotalFractions` and `toMeromorphicSpaceModule`. The latter is the fixed equivalence unit followed by the inverse-equivalence image of the scalar-extension adjunction unit. All data are constructed; no object or map is selected from a bare existence statement. |
| X reduced and normal in the specified chart sense | First conjunct: every `T : X.EtaleSite` has `IsReduced` underlying scheme, and every chart stalk satisfies `IsDomain` and `IsIntegrallyClosed`. This tests every scheme chart, not only one atlas. |
| Finite disjoint decomposition of a Noetherian chart | Second conjunct, conditional on `IsNoetherian` of that chart: `Fin n` opens whose range is precisely `irreducibleComponents`, which are closed, pairwise disjoint and cover top. Their open subschemes are `IsIntegral`, `IsRegularScheme`, and have integrally closed domain stalks. `IsColimit (Cofan.mk ... inclusions)` is the actual scheme coproduct assertion. |
| Nonempty connected affine chart ring is Noetherian normal domain | Third conjunct: `IsAffine`, `Nonempty`, `PreconnectedSpace` imply `IsNoetherianRing`, `IsDomain`, `IsIntegrallyClosed` of the top section ring. Nonempty plus preconnected is connected. |
| Finitely many generic points of components | `(genericPoints (Point X.obj.obj)).Finite`, plus unique `IsGenericPoint` for every irreducible component. `genericPoints` is Mathlib's set of points whose singleton closure is an irreducible component. |
| All generic points belong to the schematic locus | The last existential supplies an actual scheme chart `T` whose Yoneda map is representable by open immersions, with open embedding and dense image. Its image on scheme generic points is exactly all generic points of X. This introduces a witness inside the conclusion, rather than assuming X is a scheme. |
| Generic local rings are fields | `IsField ((X.etaleForget.obj T).presheaf.stalk x)` at each scheme generic point. The open embedding identifies these ordinary local rings with O_(X,eta). `meromorphicLocalSpectrum` is literally `Over.mk (fromSpecStalk x ≫ base)`, and `meromorphicGenericInclusion` composes its Yoneda map with the open chart map. No arbitrary field-valued representative is used. |
| K is the product of generic field direct images | The scalar `e` identifies `meromorphicSpaceModule X (unit X.structureSheaf)` with the categorical product of `moduleDirectImage j` applied to each field spectrum's structure module. Composing the localization, `e.hom`, and each `Pi.π` is the existing canonical `moduleStructureMap j`. The O-linear normalization preserves 1 and fractions, so this is the natural scalar identification. |
| K(L) is the product of generic line direct images | For every `L` satisfying the recorded `X.IsLineModule L`, the next `e` is an isomorphism to the product of `meromorphicGenericFactor`. This is exactly `j_* j^* L` using the fixed module direct-image and tensor-pullback functors. The equation with every product projection is the specified `moduleTensorAdjunction j` unit; it fixes the maps on sections and on fractions. On Spec of the generic local field this tensor pullback is the line's generic fibre. |
| Generic line fibres have dimension one | `Module.finrank` of the ordinary chart line stalk over the actual chart local ring is 1, for every generic point. The preceding `IsField` assertion makes these exactly one-dimensional field vector spaces. No arbitrary scalar field or algebra action is bound. |
| Global meromorphic sections equal the product of L_eta | The equivalence `g` has source `(meromorphicSpaceModule X L).sections` and target the dependent product of the ordinary generic line stalks. For regular global sections it is the ordinary germ map `meromorphicRegularGerm`. The final implication also normalizes every meromorphic section: whenever `m = a*s` on any chart open through eta after localization, its generic coordinate satisfies `germ(m) = germ(a) • g(s)(eta)`. Every meromorphic germ admits such a denominator, so this fixes the intended fraction value, including nonregular sections. |
| Both natural maps are injective | `Mono (spaceToTotalFractions X)` and `Mono (toMeromorphicSpaceModule X L)` for every line module. Monomorphisms of these module/ring sheaves express injectivity on sections. |
| Every dense open gives bijective meromorphic restriction and injective line restriction | For every point subset `W` with `IsOpen W` and `Dense W`, `meromorphicOpenRestriction` is bijective on K(L) sections and injective on L sections. The target is compatible sections on the full category of charts contained in W, precisely the small étale site of the open subspace. This is the actual restriction map (`Functor.sectionsPrecomp`), not existence of an unrelated equivalence. |
| Every affine chart has K(U) = Q(A) | `IsIso` of every component of the actual `toSheafify` for `spaceTotalFractionPresheaf`. Its source is literally `Localization (nonZeroDivisors A)`. Quantification on the existing small skeleton covers every affine étale chart by the existing equivalence; sheaf sections transport along those chart isomorphisms. The maps and the fraction restrictions are those already fixed by `SpaceTotalFractions`. |
| Restriction to scheme charts is usual meromorphic localization | For every line L, the family `c T` compares the ordinary restriction of the space localization with `Scheme.Modules.meromorphicModule` of the ordinary chart restriction. Its equation with `Scheme.Modules.toMeromorphicModule` fixes the comparison on regular sections and hence on local fractions. This applies also to the unit line and hence to K. The recorded Zariski/étale comparison identifies these with the usual meromorphic sheaves on U_et. |
| Comparisons commute with further étale restrictions | The clause after the `c T` normalization tests every chart map `f : T ⟶ U`, every open W and its inverse image, and the actual restricted chart arrow `a` (specified by `etaleForget.map a = f ∣_ W`). Whenever d is the restricted denominator b, the two composites send m/b to `L.val.map a.op m / d`. Thus it asserts the same numerator/denominator formula under every further restriction. Identity and composition are included, and the sheaf comparisons already commute with restrictions inside each chart. |

The Zariski formulation in the final two rows does not replace the étale sheaves with
arbitrary ordinary sheaves. It uses restriction on every étale scheme chart, the actual
space-module restrictions between those charts, the existing ordinary meromorphic
construction, and the fraction formula. Evaluation at the top open on every chart,
with these restriction equations, reconstructs the desired small-étale identification.

Dependency declarations read and used (names are in `AlgebraicGeometry.AlgebraicSpace`
unless otherwise indicated):

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `structureSheaf`, `Modules`, `IsRepresentableWith`, `IsLineModule`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  (the class and its affine-section field); `Mathlib.AlgebraicGeometry.Properties`:
  `AlgebraicGeometry.IsIntegral`, `IsReduced`.
- `Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison`:
  `AlgebraicGeometry.Scheme.scheme_etale_invertible_comparison`, with its actual
  ordinary/étale line-module objects, associated section functor and restriction formulas.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoints`;
  `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `IsIrreducible`.
- `Sheaf.AlgebraicGeometry.MeromorphicModule`:
  `AlgebraicGeometry.Scheme.Modules.meromorphicModule`, `meromorphicDenominators`,
  `meromorphicFraction`, `toMeromorphicModule`; these retain the ordinary germ-regular
  denominators, localization and sheafification, not a private copy.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  `moduleTensorPullback`, `moduleTensorAdjunction`, and the chart-limit characterization
  read in `ModuleDirectImageModel`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.mk`, its equality relation and localization map.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  `SheafOfModules.cochainModulesMonoidal` interface, publicly imported as requested;
  K(L) uses the already fixed scalar-extension construction, not a new tensor.
- Added already-landed owners in `stmt_deps`: `def-sfb-space-divisors`
  (`IsRegularNoetherianSeparated` in `SpaceDivisorDefinitions`),
  `def-sfb-space-total-fractions` (`spaceTotalFractionSheaf`,
  `spaceMeromorphicLocalization`, `spaceToTotalFractions` in `SpaceTotalFractions`),
  `def-sfb-space-small-ringed-model` (`smallModuleRestriction`,
  `smallModuleEquivalence` in `AlgebraicSpaceSmallRingedModel`),
  `def-trf-space-module-scheme-restriction` (`schemeOpens`, `schemeOpensRingHom`,
  `schemeRestriction` in `AlgebraicSpaceSchemeRestriction`),
  `def-trf-scheme-algebraic-space` (`schemeSpace` in `EnlargedEtaleRingedSite`),
  `def-sfb-space-module-structure-map` (`moduleStructureMap` in
  `AlgebraicSpaceModuleStructureMap`), and `def-a1-space-point-topology`
  (`pointTopologicalSpace` in `AlgebraicSpacePointTopology`). Each declaration's
  full signature, construction and docstring were read. These additions are allowed
  by brief-stage2 §5 for landed notions. A graph traversal of both dependency kinds
  found no path from any added owner to this item.

The module also imports the already stated proof-dependency modules, including their
Mathlib matches. The seven-step theorem docstring follows the node's proof. The not-yet
stated topology, specialization, local-spectrum, total-fraction-base-change and cartesian
chart-family proof nodes have no module to import; they remain unchanged proof dependencies.

Edge cases checked mathematically before writing:

- Empty X: the dense schematic witness can be empty, generic products are empty products,
  the chart coproduct has n=0, and dense-open restriction is between singleton section types.
  No global Nonempty hypothesis is present.
- Empty affine chart: its ring is the zero ring. It occurs in the fraction-sheaf comparison;
  the normal-domain claim expressly requires Nonempty. No false assertion that Spec 0 is
  integral or a field is introduced.
- Disconnected X: all generic points are indexed, not one chosen point; products and line
  fibres cover every component. The line is not required to have one global regular frame.
- A field and a DVR: the scalar identification is the identity field or its fraction field,
  the line fibre has dimension one, and dense-open restriction is the expected generic map.
- A nonaffine chart and a rational function with a pole: local fractions are evaluated on
  arbitrary opens through eta, not only as quotients of global regular functions. The final
  germ equation applies to any meromorphic global section, not merely regular ones.
- Further étale maps can have empty source or extend generic fields. Restrictions use the
  actual chart ring maps, actual denominators and actual line restriction; no identity on
  residue fields is assumed.
- Universe u is explicit. Scheme charts and coefficients remain in the project's original
  universe, point classes can live in u+1, and no equality of site-object and morphism
  universes is imposed. `autoImplicit` is false throughout.

Searches performed, all on this item (remote search receipts in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder`: “For a regular Noetherian algebraic space the meromorphic
  sheaf is the product of generic field pushforwards and evaluates to total fractions on
  affine etale charts”. Eight hits, including `Scheme.functionField`, field and fraction-ring
  instances, and `StructureSheaf.IsFraction`; no algebraic-space theorem of this statement.
- `msearch.py ... loogle`: `IsFractionRing, IsLocalization`. Twelve localization/fraction-ring
  hits; none is this sheaf or generic-product theorem.
- `msearch.py ... grep`: `meromorphic|Meromorphic`, subdirectory `AlgebraicGeometry`.
  Zero Mathlib hits. Ordinary scheme meromorphic constructions are supplied by the project.
- `msearch.py ... leansearch`: “meromorphic sheaf algebraic space generic points total
  quotient ring”. Eight hits, primarily analytic meromorphic functions, plus the ordinary
  topological `TopCat.Presheaf.totalQuotientPresheaf`; no matching algebraic-space result.
- Read-only `rg` in `lean/WeilConjectures`, `lean/Sheaf` and the upstream-name index for the
  item id, meromorphic names and the proposed names. The id occurs in downstream
  `RegularSpaceDivisorLineDictionary` docstrings, not as an existing theorem. The existing
  scheme results (`MeromorphicGenericProduct`, `MeromorphicSheafGenericProduct`,
  `MeromorphicGenericAffine`) were read and do not state this algebraic-space theorem.
  The existing `SpaceTotalFractions` and small-model constructions were found and reused.
  No proposed declaration name already occurs in Mathlib or the project.
- `tools/blueprint_refs.py search 'meromorphic'` and `search 'total fraction'`: zero blueprint
  matches; the relevant supporting DAG definition nodes were found by `rg` on `dag/nodes`.

Validation: `scompile.py Q96 lem-sfb-space-meromorphic-generic-chart-model` compiled both
the sandbox module and the intended library module cleanly, with no warnings or errors.
The initial transported-unit elaboration issue was repaired by explicitly supplying the
source and target ring sheaves; the temporary heartbeat override was removed. A global
section coercion was repaired with explicit `@id` of the existing module type. These are
elaboration repairs only. Delivery dry-run and final delivery are run after this report.

No STATEMENT-DISPUTED issue remains, and no source or node fault was found.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
