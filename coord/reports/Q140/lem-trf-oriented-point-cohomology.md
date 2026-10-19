## Worker report

Q140 repairs the substantive return on immutable head fe7690cee3c7. The previous
arbitrary-functor theorem has been replaced in
`Sheaf.TraceFormula.OrientedPointCohomology` by
`CategoryTheory.OrientedPointCohomology.orientedPointCohomology`.
The mathematical node statement and its proof are unchanged. Its statement
prerequisites gain three already-landed interfaces used below, as permitted by
brief-stage2 §5. No dependency record is overwritten.

Source read: Illusie, *Around the Thom--Sebastiani theorem*, §§1.1--1.3,
especially formula (1.3.1) and the affine-neighbourhood paragraph, printed p. 7,
https://www.imo.universite-paris-saclay.fr/~luc.illusie/Illusie-nearby-cycles28.pdf .
This gives the oriented-product convention, the inverse image `U ×_V W`, and the
Milnor tube with the indicated specialization, without extra finiteness or
coefficient assumptions.

All names in the following table are in `CategoryTheory.OrientedPointCohomology`
unless qualified. Every hypothesis and clause of the node is represented:

| Node text | Lean rendering |
| --- | --- |
| Morphisms of schemes `f : X → S`, `g : Y → S` | Explicit `{X Y S : Scheme.{u}}`, `(f : X ⟶ S)`, `(g : Y ⟶ S)` in the main theorem. |
| Commutative coefficient ring Λ | `(Λ : Type v) [CommRing Λ]`, independently of scheme universe `u`. |
| Small étale topoi | The landed `OrientedNearbyCycles.EtaleSite`, `etaleTopology`, and `etaleBaseChange`, obtained from `Scheme.smallEtaleTopology` by the `AsSmall` equivalence. |
| Left oriented product P | `Triples f g` is the recorded `OrientedProduct.Triples` for the two étale base-change functors. `topology f g` is exactly `OrientedProduct.topology` with its three generating cover types. `datum` packages this actual site. P is its sheaf topos, not an independently supplied category. |
| Z is X ×_S Y | Every occurrence is `pullback f g`; no arbitrary Z parameter. |
| ψ from projections and equality over S, with inverse image U ×_V W | `a`, `b` extract the arrows of a triple; `D T := pullback (a T) (b T)`, and `t T : D T ⟶ pullback f g` is the projection-induced map. `psiSite` sends T to this étale Z-object and sends morphisms by the unique projection-compatible map. `psi` is `siteMorphism` of this continuous finite-limit functor. The direct image `pushFixed` is its actual `sheafPushforwardContinuous`, so evaluation on T is evaluation at D T. |
| Geometric points x,y | Explicit maps `Spec (.of Ωx) ⟶ X` and `Spec (.of Ωy) ⟶ Y`, with field and algebraic-closedness instances, matching the recorded geometric-point interface. |
| Specialization c over S | The theorem binds `c : strictHenselizationScheme (y ≫ g) ⟶ strictHenselizationScheme (x ≫ f)` and the necessary equation `hc : c ≫ strictHenselizationStructuralMap (x ≫ f) = strictHenselizationStructuralMap (y ≫ g)`. This equation renders the words “of S-schemes”; it adds no hypothesis to the node. |
| Resulting oriented point z | `Lift T` consists of strict-local lifts to U,W,V satisfying the over-base equations and compatibility with the fixed c. `fiber` transports these lifts along triple morphisms; `z` is the actual site point with this fibre. It is determined by x,y,c, with no free point parameter. |
| Milnor tube M | `M f g x y c := pullback (strictHenselizationMap f x) (strictHenselizationMap g y ≫ c)`, exactly the specified fibre product. |
| Natural r : M → Z | `r` is `pullback.lift` of the two strict-local structural maps. Its compatibility theorem `M_condition` uses precisely hc and the recorded strict-local map over-base laws. |
| Bounded-below K in constant Λ-module sheaves on Z | The source of the two functors in the main natural isomorphism is `DerivedCategory.Plus (Modules (etaleTopology (pullback f g)) (ULift Λ))`. `Modules J A` is the recorded `ringedSiteModules` of the actual constant ring sheaf. `fixed` is the landed, sectionwise-specified equivalence to `Sheaf J (ModuleCat A)`. The ring ULift and site AsSmall are universe transports, explained below. |
| Rψ is the total right derived direct image | `Rpsi := push.rightDerivedFunctorPlus`, with `push := fixed.functor ⋙ pushFixed`. This is the actual module direct image in the equivalent fixed-ring encoding. Enough injectives are obtained from the recorded sheaf-of-modules Grothendieck theorem and transported by `fixed`. The right-derived construction uses bounded-below injective resolutions, which are K-injective. |
| z* is exact point inverse image | `fiberFixed := z.sheafFiber ⋙ downCoefficients`; `zStar := fiberFixed.mapDerivedCategoryPlus`. The named properties assert additivity and finite-limit/finite-colimit preservation of this specified fibre functor. |
| r* is exact derived inverse image | `pullFixed` is the actual sheafified left Kan extension for `etaleBaseChange r`, namely `Functor.sheafPullbackConstruction.sheafPullback`, with its own adjunction. `pull := fixed.functor ⋙ pullFixed`; `rStar := pull.mapDerivedCategoryPlus`, using the recorded exact derived-functor construction, with no arbitrary comparison map. |
| RΓ(M,r*K) | `sectionsFixed Λ M` evaluates at `finalEtale M`, then returns coefficients to Λ. `RGamma := sectionsFixed.rightDerivedFunctorPlus`. Thus the target is `rStar ⋙ RGamma`. |
| Isomorphism in D+(Mod Λ), for every K | The conclusion gives `∃! e : Rpsi ⋙ zStar ≅ rStar ⋙ RGamma, ...`. Both codomains are literally `DerivedCategory.Plus (ModuleCat Λ)`. Evaluating `e` at any K gives the displayed isomorphism. |
| Restriction from affine pointed neighbourhoods to M | For every pointed triple, `q` is uniquely fixed by its U,W projections from M; `q_over` says `q ≫ t = r`. `qEtale` maps the final M-object to the base change of D T. `sectionRestriction` is the actual inverse-image adjunction unit followed by restriction along `qEtale`. `restrictionFixed_unique` fixes the map on every fibre-colimit generator to be this restriction, in particular on every affine pointed triple. |
| Canonical and natural in K | `restrictionFixed`, `restriction`, and `restrictionHomotopy` are natural transformations. `sourceUnit` and `targetUnit` use the actual right-derived units and exact-derived factorization isomorphisms. The equation in the main theorem says `Qh`-whiskered `e.hom` takes this ordinary restriction to the derived one. Existence gives the restriction comparison as a natural isomorphism; uniqueness removes any arbitrary choice of an isomorphism. |

Size and coefficient transport: let `s = max u v + 1`. The site is enlarged by
`AsSmall` to object and hom universe s, while retaining its induced original
small-étale topology. Its coefficient ring is `ULift.{s} Λ`, so the recorded
ringed module and sheafification constructions apply without equating u and v.
The lift is canonically ring-isomorphic to Λ. `downCoefficients` is the concrete
`ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom`, used on both the
point fibre and sections, including every generator-normalization equation.
Consequently the conclusion has coefficients literally Λ. On the source,
constant-ULift-Λ modules are the canonical scalar transport of constant-Λ
modules; no class of K is restricted. The fixed-ring encoding is identified by
the landed `constant_ring_module_sheaves`, whose functor is explicitly
`constantRingModuleRestriction`, rather than an arbitrary equivalence.

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-etale-site`: Mathlib `Scheme.smallEtaleTopology`, used through
  `Sheaf.Paper.OrientedNearbyCycles` declarations
  `AlgebraicGeometry.OrientedNearbyCycles.EtaleSite`, `etaleTopology`,
  `etaleBaseChange`, their finite-limit/continuity instances, and `siteMorphism`.
- `lem-trf-oriented-product-universal`:
  `Sheaf.CategoryTheory.Sites.OrientedProductUniversal`,
  `CategoryTheory.OrientedProduct.Triples` and `topology`, the concrete site in
  its recorded `universal` theorem. We use its site construction, not a copy of
  its universal-property proposition as a hypothesis.
- `def-pc-fibre-product`: Mathlib `CategoryTheory.Limits.pullback`, its projections,
  `pullback.lift`, and projection equations.
- `def-weil-geometric-point`: the recorded Mathlib field/Spec description.
- `def-weil-pbc-strict-henselization-limit`:
  `Sheaf.AlgebraicGeometry.StrictHenselization`,
  `AlgebraicGeometry.Scheme.strictHenselizationScheme` and
  `strictHenselizationStructuralMap`.
- Added landed prerequisite `lem-weil-pbc-strict-henselization-functoriality`:
  its public imports include `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`,
  whose `Scheme.strictHenselizationMap` and `strictHenselizationMap_over` give the
  actual pointed strict-local maps in M and r. Its current primary record is the
  later closed-lift factorization interface, so this module imports the smaller
  canonical-map module that owns the maps it needs.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  used directly by `Modules`.
- Added landed prerequisite `lem-cbc-constant-ring-module-sheaves`:
  `Sheaf.CategoryTheory.ConstantRingModuleSheaves`,
  `CategoryTheory.constant_ring_module_sheaves` and its specified restriction
  functor; reused by `fixed` without redefining its notion.
- `def-weil-abstract-derived-category`: Mathlib `DerivedCategory.Plus` and
  `HasDerivedCategory.standard`.
- `def-pur-kinjective-complex`: Mathlib `CochainComplex.IsKInjective`; the standard
  bounded-below right-derived construction computes by bounded-below injective,
  hence K-injective, representatives. No arbitrary resolution operation is bound.
- `def-weil-pbc-derived-inverse-image`: the recorded
  `CategoryTheory.Functor.mapDerivedCategoryPlus`, also its factorization
  `mapDerivedCategoryPlusFactorsh` in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`:
  `GrothendieckTopology.Point.sheafFiber` and `toPresheafFiber`; these are the
  actual fibre functor and colimit generator maps in the normalization.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`:
  `SheafOfModules.isGrothendieckAbelian`; with Mathlib's Grothendieck enough-
  injectives theorem this supplies the required injectives, not an extra hypothesis.
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
  `Functor.rightDerivedFunctorPlus` and `rightDerivedFunctorPlusUnit`.

The three additional prerequisites already have landed Lean records; the
recorded dependency graph has no path from any of them back to this item.
All other helpers are the owning node's constructions and laws, permitted by
the worker brief's helper-declaration rule; all are listed in `lean.declarations`
and have source/blueprint docstrings. They introduce no extra independent
mathematical notion requiring a new DAG node. Every postponed theorem has its
proof plan in its docstring. The main docstring follows all seven steps of this
node's recorded proof. Choices of Dmap, liftMap, q and the ordinary comparison
are from existence-and-uniqueness statements that fully fix the data. No object
is chosen from a bare existence or `Nonempty` theorem. Definitions have real data.

Edge cases checked against the statement and source:

- The zero ring and zero complex are allowed; no nonzero, torsion or invertibility
  hypothesis occurs. The module categories and the comparison still make sense.
- For identity maps and the identity specialization the strict-local construction
  gives the expected strict-local tube and usual restriction-to-stalk comparison.
  The unit normalization does not discard identity cases.
- For a nonidentity specialization, including cases where Z or M is empty, the
  definitions still use the actual pullback. The étale site of the empty scheme
  gives zero module sections, consistent with the source formula. There is no
  nonemptiness assumption on Z or M. The geometric-point hypotheses themselves
  exclude empty X or Y, as in the node.
- Nonseparated schemes are allowed: the proof of etaleness of D T → Z uses the
  open diagonal of an étale V → S, not separatedness of any of X,Y,S.
- Independent coefficient and scheme universes are retained through the explicit
  common lift and coefficient down map; no equality of universes is assumed.
- The return's counterexample choosing zero Rψ with identity zStar and RΓ is
  unavailable: none of these functors, sites, points, M, or r is a parameter.

Searches for reuse (repair session, prescribed msearch wrapper):

- LeanFinder: `oriented product etale topos derived stalk Milnor tube cohomology`:
  eight `smoothSheafCommRing.forgetStalk` and related stalk/forgetful declarations;
  no oriented-product derived Milnor-tube comparison.
- Loogle: `"Milnor", "sheaf"`: no hits.
- Mathlib grep: `orientedPoint|Milnor.?tube|oriented.?product`: no hits.
- LeanSearch: `constant ring module sheaves equivalence module valued sheaves`:
  eight generic `Scheme.Modules`, `SheafOfModules`, `ModuleCat.tilde`, and
  `PresheafOfModules.unitHomEquiv` hits. The exact already-landed project bridge
  `constant_ring_module_sheaves` was found and reused.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for oriented/Milnor
  constructions and the item id: no existing theorem equal to this node.
- `rg` in the project's `lean/Sheaf` found the concrete oriented framework,
  strict-local maps and constant-ring equivalence reused above. The old primary
  declaration attached to this item was the returned arbitrary-functor statement,
  not a reusable theorem for the specified geometry.
- The original packet's search log is retained in `searches.jsonl`; its additional
  generic site-point hits do not state this geometric comparison.

Return points addressed:

1. H3: all geometry, coefficients and functors are constructed from f,g,Λ,x,y,c
   with c over S. The result is the canonical natural restriction isomorphism,
   not `Nonempty` of an isomorphism between arbitrary functor values. No duplicate
   Category/SmallCategory instance is bound. Universes u,v are independent.
2. H4/H9: imports supply the actual triple topology, étale site, strict local maps,
   ringed constant modules, exact derived inverse image, point fibre and right
   derived functors. There are no unused abstract geometric parameters.
3. H8: the main theorem's docstring now gives the seven proof steps, including
   affine pointed triples, the inverse limit M, the fibre colimit, exactness,
   scalar-forgetting/localization, canonical restriction, continuity and descent.
   Each auxiliary postponed law has its own source and proof explanation.

No `STATEMENT-DISPUTED` issue was found. The node is unchanged mathematically;
only its Lean record and the three permitted landed prerequisites are changed.

## Second reading by Q140

This dispatcher forbids starting another agent, so this is a separate self-reading
of the source, node and final module, not a claim of an independent second worker.
The maintainer supplies the independent review.

The self-reading checked each table row against the Lean construction. It found
and corrected the saved packet's free functors/categories and free site/point,
the missing over-S equation, absence of coefficient modules, and unconnected tube.
It checked the orientation `c : S_(g(y)) → S_(f(x))`, the projection order in the
base-change functor, q's over-Z equation, the inverse-image unit in restriction,
and both derived-factorization arrows. It also replaced a coefficient-universe
identification by explicit ULift scalar restriction, so the final codomain is
literally D+(Mod Λ). Natural isomorphism quantifies over every K; its normalization
uses the already fixed restriction rather than a chosen abstract isomorphism.
