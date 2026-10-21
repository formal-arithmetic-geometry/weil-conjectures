## Worker report

The delivery states `lem-sfb-pointed-finite-etale-limit-cover` in
`Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`. The primary declaration is
`AlgebraicGeometry.Scheme.UniversalCover.nonempty_pointedLimitCechCoordinates`.
Its conclusion is existence of the explicitly specified structure
`PointedLimitCechCoordinates x G`. Every field is stated in full, including the finite-quotient
limit cone and the scheme isomorphisms. Four companion theorems state pointed naturality,
the coefficient-section cocycle, its label-only specialization, and identity/composition.
All five theorems have whole-proof `sorry`; every definition has actual data. This is stage 2.

The existing `UniversalCover.cover`, `proj`, `pt`, `toObj`, `transport`, and `map` are reused;
no replacement universal cover, fibre functor, fundamental group, topology, site or torsor
notion is introduced. The helper structure is a package of this node's conclusions, not
an assumed cover or an additional hypothesis. Its isomorphisms and quotient cone are
normalized by equations, not merely arbitrary equivalences.

Hypothesis and clause correspondence (unqualified helper names below are in
`AlgebraicGeometry.Scheme.UniversalCover`):

| Node text | Lean rendering |
| --- | --- |
| Scheme X | `{X : Scheme.{u}}` |
| Nonempty and connected | `[ConnectedSpace X]`; its `toNonempty` includes nonemptiness |
| Quasi-compact | `[CompactSpace X]`, without any Hausdorff condition |
| Quasi-separated | `[QuasiSeparatedSpace X]`, the scheme version of the recorded terminal-map condition |
| Algebraically closed geometric point | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)` |
| Π with its profinite evaluation topology | `(G : ProfiniteGrp.{u})`, its fibre actions, and `[IsFundamentalGroup (FiniteEtale.fiber x) G]`. This is Mathlib's standard interface for an arbitrary small model of Aut of the fibre functor; `toAutContinuousMulEquiv` identifies the topological groups. The recorded `exists_fiber_flc_equivalence` identifies it homeomorphically with `Aut (flcFiber x)`, not an unrelated group. |
| Pointed connected finite étale Galois covers and pointed transitions | Existing `Index x := SmallModel (PointedGaloisObject (FiniteEtale.fiber x))`, `obj`, `point`, and `diagram`. `IsGalois` extends categorical connectedness, equivalent here to connected total space; the fibre-functor criterion is transitivity of Aut, with freeness from determination by one fibre point. |
| Inverse limit exists over X | Existing `HasLimit (diagram x)`, `cover x := limit (diagram x)`, `π_p`, and `limit.isLimit`. The X-compatibility makes this the same limit in schemes over X. |
| Any small cofinal system | `cofinal` asserts `IsLimit` of the existing cone whiskered along every small initial functor into `Index x` (initial is the inverse-limit direction of cofinal). |
| Connected T | `connected : ConnectedSpace (cover x)` |
| Affine v | `affine : IsAffineHom (proj x)` |
| Faithfully flat | Separate `flat : Flat (proj x)` and `surjective : Surjective (proj x)` fields, exactly the node's definition |
| Weakly étale | `weaklyEtale : WeaklyEtale (proj x)` |
| Singleton pro-étale covering | `covering : Presieve.singleton (proj x) ∈ proetalePrecoverage X`; since v is a small-site object this is the singleton covering of its terminal object in the induced small pro-étale topology |
| Compatible marked point t above x | Existing `pt x`, with `point_over` and `point_stage` for every stage |
| Every finite étale Y splits | `splitting : ∀ Y : X.FiniteEtale, IsIso (finiteSplitMap x Y)`. The domain of `finiteSplitMap` is the coproduct of T indexed by the actual fibre, its codomain is the actual fibre product, and its s-th summand is `(id, toObj x Y s)`. An `IsIso` on this concrete map gives precisely the displayed canonical isomorphism. |
| Section s takes t to s | `splitting_point`, as equality of scheme morphisms, not just underlying points |
| Splitting natural in Y | `splitting_natural` on `toObj` for every finite-étale arrow and every fibre element; coproduct maps are thereby fixed |
| T × Π^q as inverse limit of finite coproducts | `profiniteProduct` uses the recorded `profiniteToProEtOf`. `finiteLabelDiagram T G q` is exactly `N ↦ ∐_(Fin q → G/N) T`, with quotient transition maps. `quotientProjections`, `quotient_limit`, `quotient_base`, and `quotient_labels` specify its limit and all quotient labels. |
| Compatible scheme Čech identifications in every q ≥ 0 | `iso q : profiniteProduct (cover x) (Profinite.of (Fin q → G)) ≅ cechTerm x q`, with the actual Mathlib Čech nerve and its wide-pullback projections |
| First vertex and consecutive labels | `first_vertex` and `vertices` fix all vertices as `(z, z·g₁, z·(g₁g₂), ...)`, as equalities of scheme morphisms on every constant-label copy of T |
| Faces and degeneracies | `simplicial`, for every simplex map φ, gives the new first vertex and the consecutive labels `(a_i)⁻¹ a_(i+1)`. For the middle face of a triple this yields g*h; outer faces delete an endpoint, degeneracies insert 1. |
| Component space with quotient topology | `components q : ConnectedComponents (cechTerm x q) ≃ₜ (Fin q → G)`. Mathlib `ConnectedComponents` uses its quotient topology. `component_labels` fixes this homeomorphism by the same consecutive labels. |
| Left-monodromy normalization on every Π/U cover | `monodromy : rightDeck(g).hom ≫ toObj s = toObj (g • s)`, for every finite cover, therefore in particular every coset cover. Together with the q=1 vertex formula this is pr₂*s = pr₁*(g s) at label g. It is an equality of SCHEME maps. |
| Right action | `rightDeck` is the existing transport along the inverse of `toAut g`; `deck_mul` and `deck_one` assert the right action law. |
| General right-torsor cocycle, coefficients pulled to triple overlap | `right_torsor_cech_cocycle` states `(A.map p₀₂.op).hom c = (A.map p₀₁.op).hom c * (A.map p₁₂.op).hom c`, with the three vertex-compatibility equations and a natural free associative RIGHT action. This is the sectionwise algebra for any group sheaf and any torsor with chosen e; no constancy or commutativity is assumed. The edge 12 starts at z·g, so the equation is exactly c(z,gh)=c(z,g)c(z·g,h). |
| Label-only specialization | `label_only_cocycle`, with explicit nonempty Z, gives `b (g*h)=b g*b h` from factorization `c z g=b g` |
| Pointed scheme naturality | `pointedLimitCechCoordinates_natural` uses the canonical `map f x'`, the actual `Arrow.mapCechNerve`, and the existing `fundamentalGroupMap (pullbackFiberIso f x') H G` with its proved continuity, in all degrees. The square is an equality of SCHEME maps; no arbitrary replacement for the induced homomorphism is supplied. Geometric points are written over the common algebraically closed Ω, with target point `x' ≫ f`. |
| Identity and composition | `pointedLimitMap_identity_composition`; HEq accounts solely for the codomain's point reassociation/identity, not a change of geometric construction |
| Compatible universes | Schemes, fields, finite fibres, profinite group models, coproduct indices, and inverse-system indices all use u. `Index x : Type u` is the existing small model, and the ambient site has its usual object universe u+1. The generic torsor equation allows independent object, morphism, coefficient and section universes u,v,w,z. No site object/morphism universe equality is imposed. |

The generic torsor lemma deliberately exposes only the algebraic laws it uses: naturality,
associativity and freeness. It does not define a new torsor predicate or replace a torsor
by an arbitrary map. Every right torsor with the specified section supplies these laws;
local sections and the sheaf condition play no role in this calculation. The formula is
valid for nonconstant coefficient sheaves, including the previously recorded correction's
G_m example. No statement correction is made in this delivery.

Dependency declarations used (read in the named sources):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including `toNonempty`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated` and its equivalence with the terminal map's `QuasiSeparatedSpace`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` and `Mathlib.AlgebraicGeometry.ResidueField`: `IsAlgClosed` and `Scheme.SpecToEquivOfField`; the point is expressed in the recorded inline form.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`: `Scheme.flcFiber`.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`: `Scheme.FiniteEtale`, `FiniteEtale.fiber`, `fiber_left_comp`, fibre maps. This is the published concrete full-subcategory implementation of the recorded finite-étale over-category.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`, `proetalePrecoverage`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `.Flat`, `.UnderlyingMap`, `.WeaklyEtale`: `IsAffineHom`, `Flat`, `Surjective`, `WeaklyEtale`.
- `Mathlib.AlgebraicGeometry.Pullbacks` and `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: schemes' pullbacks, `pullback`, `pullback.lift`, `pullback.map`, projections.
- `def-weil-size-convention` has no mathematical declaration; its small-model and compatible-universe convention is implemented as above.
- Newly cited LANDED dependency `def-sfb-profinite-test-objects`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.profiniteToProEtOf`, used without copying its definition. Only its id is added to this item's stmt_deps; its node is unchanged.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction`: `Index`, `diagram`, `cover`, `proj`, `pt`, `toObj`, `transport`, `map`, their compatibility equations and existing geometric instances.
- `WeilConjectures.Mathlib.CategoryTheory.Galois.IsFundamentalgroup` and Mathlib's `CategoryTheory.Galois.IsFundamentalgroup`: `IsFundamentalGroup`, `toAut`, `toAutContinuousMulEquiv`, `small_aut`, and `exists_isFundamentalGroup` explain the small profinite model interface.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`: `exists_fiber_flc_equivalence` gives the topological FLC-fibre identification.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality`/`.Restriction`: `pullbackFiberIso`, `fundamentalGroupMap`, `continuous_fundamentalGroupMap`.
- `Mathlib.AlgebraicTopology.CechNerve`: `Arrow.cechNerve`, `Arrow.mapCechNerve`.
- `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits`: `ProfiniteGrp.toFiniteQuotientFunctor`.
- `Mathlib.CategoryTheory.Limits.Final`: `Functor.Initial` and whiskered limit cones.

All recorded project proof dependencies with modules are imported, including
`OpenSubgroups`, `LimitAffineTransition`, `FiniteEtaleTraceDegree`, `LimitFibreProducts`,
`IndEtaleUniverseTransport`, `EtaleComparison`, `FiniteEtaleFiniteLimits`,
`FiberEquivalence`, and `AutProfinite` (the last via the public FLCFiber import).
The locally constant prime-spectrum result is already available through the existing
profinite test construction. None of these imports closes an import cycle.
The main docstring records all sixteen proof steps and the companion docstrings record
their sectionwise/naturality arguments.

Searches made, with actual wrapper results recorded in searches.jsonl:

- LeanFinder: `pointed connected finite etale universal profinite cover scheme inverse limit Cech nerve fundamental group` returned eight results: classifying-space Čech nerves, an infinite-Galois field inverse limit, the abstract finite fibre-functor fundamental group, and general affine limit material. None states this scheme result.
- Loogle: `AlgebraicGeometry.Scheme.UniversalCover, CechNerve` returned zero hits (unknown upstream namespace in the Mathlib-only service).
- Mathlib grep: `UniversalCover|cechNerve|CechNerve`, restricted to AlgebraicGeometry, returned zero hits. Separate direct grep located the general Mathlib `Arrow.cechNerve` in AlgebraicTopology; it is reused.
- LeanSearch: `universal profinite etale cover scheme Cech nerve connected components fundamental group` returned eight results, including general profinite/Čech constructions but no normalized scheme-coordinate result.
- Additional Loogle `CategoryTheory.Functor, (_ → _)` gave general functor operations, and Mathlib grep for power functors in CategoryTheory/Types found `ofTypeFunctor`, not this finite-label diagram.
- Direct rg on `lean/WeilConjectures` and `lean/Sheaf` for the item id returned no declaration. Direct searches for `UniversalCover`, `loopGraph`, Čech/component coordinates, and pointed limits found the existing cover, `bijective_fiber`, transport, map, continuous loop and graphs. Their full signatures/docstrings were read and reused; they do not supply the full stated scheme-level higher Čech isomorphisms, quotient-limit cone and normalized component homeomorphisms.
- Direct collision searches for every new helper/theorem name in both project roots returned no existing declaration.
- A DAG search for profinite test objects found the existing `def-sfb-profinite-test-objects`; it is cited instead of adding a duplicate node. `tools/blueprint_refs.py ancestor` confirms this is an agent-expansion node with ancestor `None`.

Edge cases checked before finalizing:

- Empty X is excluded by the node itself, exactly by ConnectedSpace; no extra Nonempty binder is added.
- Empty finite-étale Y has empty fibre and empty coproduct, so `finiteSplitMap` is still defined and the asserted isomorphism includes this case.
- q=0 has the unique empty label list, the singleton label space, `cumulativeLabel g 0=1`, and the one-vertex Čech term. No positive-degree assumption occurs.
- G=1 and a separably closed field base give the trivial cover, singleton label spaces and identity deck maps.
- Noncommutative g,h give `g*h`, not `h*g`: deck maps compose in right-action order, and cumulative products are ordered List.prod.
- The torsor formula retains the shifted coefficient on edge 12. For the Spec R/Spec C example with a G_m section 1+i, the unrestricted label-only law is not asserted.
- All index and coefficient universes were inspected; the geometric theorem uses the prescribed small model, and the generic torsor statement does not collapse site universes.

Validation: the final module was compiled by the prescribed scompile.py, separately in
sandbox and library-module modes, with no errors or warnings (about 6 seconds each,
inside the default 60-second limit). No local/global build or direct Git command was run.
No statement is disputed, no dependency record is repaired, and no new node is introduced.

## Second reading by NQ

This is the dispatcher's sole worker's second-pass audit; no independent worker was
started, in accordance with the explicit no-other-agents instruction. The maintainer's
independent review remains the independent reading.

With the source node and final module reopened, I checked each row above against the
actual structure field/signature. The first pass only reused the cover API; the audit
required adding the explicit finite-quotient cone, its base/label equations, all-degree
scheme vertices, the universal simplicial restriction formula, component normalization,
and the separate pointed-natural square. The torsor audit required keeping restrictions
of coefficient sections to the three edges and added the label-only specialization.
Finally identity/composition are stated explicitly rather than only described in prose.

The existing transport uses inverse monodromy, so `rightDeck` explicitly takes the inverse
of `toAut g`; this is needed for the node's left-monodromy normalization. Scheme maps,
not just geometric points, appear in both splitting and vertex equations. The component
homeomorphisms use Mathlib's quotient topology. The added stmt_dep names the existing
test-object construction rather than inventing a second model. Definitions contain no
sorry, and every postponed proof is a named theorem of this same DAG node with a complete
proof docstring. Recompilation after these additions was clean.
