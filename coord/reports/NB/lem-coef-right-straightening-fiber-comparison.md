## Worker report

The module `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison` constructs the
cone straightening in the item and states
`SSet.Straightening.right_straightening_fiber_comparison`. Every theorem proof is
`sorry`; all definition data are explicit. No statement was corrected, and no other
DAG node was stated. The earlier worker's stale-stage-1 diagnosis does not apply to
this stage-2 assignment: the current item is split, reviewed, and all three original
statement dependencies have Lean records.

### Hypotheses and clauses

- Fixed universes, enlarged when needed: explicit `universe u` and `SSet.{u}`;
  simplicial categories are the existing `CategoryTheory.CoherentNerve.SCat.{u}`.
  No equality between independent object and morphism universes is imposed.
- Objects 0,...,m of the standard coherent realization:
  `simplexRealization.obj n` is Mathlib's enriched `SimplicialThickening` on
  `ULift (Fin (n.len + 1))`. Its mapping sets are nerves of the endpoint subset
  posets, empty for reversed endpoints; composition is union. Its maps are
  `SimplicialThickening.functor a.toOrderHom.uliftMap`, hence images of subsets.
- Realization of a general simplicial set is exactly the required simplex colimit:
  `realization := stdSimplex.pointwiseLeftKanExtension simplexRealization` has object
  `colimit (CostructuredArrow.proj stdSimplex X ⋙ simplexRealization)`. This is the
  category of all maps from standard simplices, with their commuting triangles.
  `simplexInclusion` is its colimit leg and `vertex` its degree-zero object map.
  `sCatColimits` extracts the recorded cocompleteness interface, and
  `realizationPointwise` uses Mathlib's essentially-small indexing theorem. These
  choose objects only through colimit universal properties, which determine them
  up to the canonical isomorphism used throughout.
- The ordered cone and its pure factors: `cone` abbreviates the published
  `SSet.Enhanced.orderedJoinFunctor.obj (X, Δ[0])`; `coneMap` is its map `(f,id)`.
  This existing convolution construction uses terminal augmentations in degree -1
  and left Kan extension along ordinal concatenation. In degree r its normal forms
  are the pure `X_r`, the pure point, and the mixed copies `X_u` for 0 ≤ u < r.
  Its operators restrict the initial and final ordered blocks exactly as the node
  specifies. The inclusions are the existing `orderedJoinInl` and `orderedJoinInr`.
- For a map `a : X ⟶ S`, `conePushout a` is the actual categorical pushout of
  `realization.map (orderedJoinInl X Δ[0])` and `realization.map a` in the single
  existing category of simplicial categories. `coneVertex` is the image of the
  pure final vertex, not an arbitrary distinguished object.
- The value `St_S(X)(s) = M_a(s,v)` is `value a s`, definitionally
  `CoherentNerve.hom (conePushout a) ((baseInclusion a).obj (vertex s)) (coneVertex a)`.
  `valueAt` extends this to every object of the realized base. `precomposition`
  uses the base inclusion's enriched map followed by `eComp`; `enrichedAction`
  curries that explicit map. `straightening a` is an actual `EnrichedFunctor`
  out of the opposite of the realized base, with these object and action data.
  The named identity and composition theorems postpone only its laws.
- Functoriality in X over S: `conePushoutMap` is `pushout.map` for any commuting
  square, with no fibration assumptions. `valueMap` is its actual enriched map on
  the two specified endpoints, transported along the named endpoint equalities.
  `valueMap_id` and `valueMap_comp` give the laws; `valueFunctor S s : Over S ⥤ SSet`
  packages them. The third main conjunct says that these maps commute with
  simplicial precomposition. Thus the pointwise functorial maps are compatible with
  the displayed simplicial-functor structure, rather than just maps of bare values.
- Preservation of all small colimits is the first main conjunct,
  `∀ S s, PreservesColimitsOfSize.{u,u} (valueFunctor S s)`. Colimits of simplicial
  presheaves are computed objectwise, so these assertions are exactly preservation
  by straightening. This includes empty diagrams.
- The canonical representable isomorphism is expressed as
  `IsIso (representableMap s t)` in the second conjunct. The direction is from
  `C[S](s,t)` to `St_S({t})(s)`; its inverse gives the displayed direction in the
  node. This map is specifically composition with `t → v`: `intervalArrow` is the
  full two-endpoint path in `C[Δ[1]]`, `attachedInterval t` is its image under the
  mixed join generator, `coneArrow t` is that actual arrow with the canonical
  endpoint transports, and `representableMap` composes the old mapping simplex with
  `coneArrow t`. No isomorphism or arrow is chosen from an existence theorem.
- Right anodyne maps: the fourth conjunct binds arbitrary X,Y,S, maps a,b,j and
  the over-S square `w`, assumes precisely `rightAnodyneExtensions j` from the
  recorded dependency, and concludes the recorded realization-based
  `Enhanced.IsWeakHomotopyEquivalence (valueMap a b j (𝟙 S) w s)` for every vertex.
- Right fibration: in the fifth conjunct the only hypothesis is
  `∀ n (i : Fin (n+2)), 0 < i → HasLiftingProperty (horn (n+1) i).ι a`.
  This ranges over exactly the horns in all positive dimensions with 0 < i ≤ n;
  reindexing the dimension as n+1 excludes neither dimension one nor its final horn.
  It is the literal lifting condition introduced in the item, not a Kan or
  quasicategory hypothesis and not a substitute definition of another DAG node.
- Strict fiber: `fiber a s` is the actual `pullback a (SSet.const s)`;
  `pullback.snd` is its map to Δ[0]. `fiberComparison a s` is `valueMap` for its
  pullback square (`pullback.fst`, `SSet.const s`), followed only by the canonical
  equality identifying the image of the unique point vertex with s. The fifth
  conjunct states that this specified map is a weak homotopy equivalence.
- Naturality in right fibrations and base vertices: the sixth conjunct binds an
  arbitrary square a,g,f,b and the right-horn lifting conditions for a and b.
  Its equality compares `fiberComparison a s ≫ valueMap a b f g w s` with the
  point-straightening of `fiberMap a b f g w s` followed by
  `fiberComparison b (g.app _ s)`. `fiberMap` is the actual `pullback.map`, and its
  over-point equation is named `fiberMap_overPoint`. Choosing the target vertex
  as g(s) covers every pointed square with its specified equality to a named target
  vertex; g=id specializes to all maps over a fixed base.
- There is no quasicategory hypothesis on S or T, no Kan hypothesis on X or Y,
  and no nonemptiness hypothesis. These omissions are intentional and match HTT.

### Dependency declarations and imports

Read the full recorded signatures and source docstrings. The original dependencies
are used directly:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`
  (realization induces a bijection on components and bijections on positive based
  homotopy groups); its source contains the recorded `coneCategory` and nerve,
  simplicial-set, and universe conventions. No alternative weak equivalence was defined.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.simplicial_interval_lifting`, specifically its second conjunct
  `HasColimitsOfSize.{u,u} SCat.{u}`. The shared `SCat`, category, and `hom` are those
  of `Sheaf.CategoryTheory.CoherentNerveInfrastructure`, used by that dependency.
- `Sheaf.CategoryTheory.RightAnodyne`: `SSet.rightAnodyneExtensions`, literally the
  infimum of all morphism properties containing right horns and isomorphisms and
  closed under pushouts, transfinite composition, and retracts.

One already landed dependency is added to stmt_deps:
`lem-coef-infinity-slice-right-fibration`, module
`Sheaf.CategoryTheory.JoinSliceRightFibration`. Only its real-data helpers
`orderedJoinInl`, `orderedJoinInr`, and `joinPointTopSimplex` are used, along with
`orderedJoinFunctor` from its imported `Sheaf.AlgebraicTopology.PushoutJoinSaturation`.
The right-fibration theorem of that module is not used to assume any clause of this
item. This addition cites the established common join and avoids a second construction.
I checked the dependency closure: there is no path from this node back to the item.

Proof-only imports are `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
`Sheaf.AlgebraicTopology.SimplicialBoundaryCollapseTest`, and
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` for the recorded
`SSet.relativeCellComplexOfMono`. The other proof dependencies currently have no
Lean module, so there is no import to add for them. They are not used as definitions.
The seven-step proof plan in the main docstring names all those inputs.

Mathlib constructs reused: `SimplicialThickening`, `EnrichedCat`,
`Functor.pointwiseLeftKanExtension`, `CostructuredArrow`, `colimit.ι`,
`hasColimitsOfShape_of_essentiallySmall`, `pushout`, `pushout.map`, `pullback`,
`pullback.map`, `EnrichedFunctor`, `eComp`, `MonoidalClosed.curry`, and `IsIso`.

### Edge cases

- Empty S has no vertices; the value assertions quantify over the empty vertex type.
  Realization still uses its empty simplex colimit. No vertex is chosen globally.
- Empty X and empty fibers are allowed. Their cones still contain the pure cone
  point, while the incoming mapping values may be empty; no inhabitance is assumed.
- Empty diagrams are included in `PreservesColimitsOfSize`.
- Dimension zero is present in realization and in the point model. The right-horn
  condition starts at dimension one, as it must; dimension-one i=1 is included.
- Base S=Δ[0] is included. Identity squares are the actual identity maps by
  `valueMap_id`, and compositions retain the prescribed maps by `valueMap_comp`.
- Coincident s=t and identity edges are allowed; the adjoined interval endpoints
  remain distinct before the cone pushout. No inverse, path, filler, or point in a
  fiber is chosen to construct any map.
- Arbitrary non-Kan X and non-quasicategorical S are explicitly permitted.
- `autoImplicit false` and explicit universe u prevent accidental implicit binders.

### Searches and source check

Searches were performed before writing the construction:

- `msearch.py leanfinder`: query "Cone straightening of simplicial sets over S sends
  right anodyne maps to objectwise weak equivalences and compares the straightening
  of a right fibration fiber". Eight hits: the all-horn Kan generator/fibration
  declarations, StrictSegal pointwise right-Kan-extension lemmas, and related
  ordinary results. None constructs the required cone straightening or its fiber map.
- `msearch.py loogle`: query `SimplicialThickening, EnrichedCat, straightening`.
  Zero hits; the service also reported unknown identifier `SimplicialThickening`.
  Direct source inspection supplied the correct Mathlib primitive.
- `msearch.py grep`: query `[Ss]traightening|rigidification|[Uu]nstraightening`,
  subdirectory `AlgebraicTopology`: zero hits.
- `msearch.py leansearch`: query "Simplicial cone straightening preserves colimits
  sends right anodyne maps to weak equivalences and recovers fibers of right
  fibrations". Eight hits: all-horn fibrations, colimit functoriality, simplicial
  object colimits, and ordinary Kan-extension facts. None matches this statement.
- `rg` over upstream `WeilConjectures` for `rigidification|straightening|Straightening`:
  only unrelated Picard/Artin–Schreier rigidifications. Searching the item's exact
  ID there gives no match. Searching `dag/lean_names_upstream.json` gives no match.
- `rg` over `lean/Sheaf`: the coherent-nerve infrastructure supplies the existing
  category of simplicial categories; `CoherentNerveComparisonStatement` only has a
  rigidification field, and is downstream of this item, so no object was selected
  from its unproved existence. Join searches found the usable constructed join and
  inclusions, which are reused. There is no existing standalone realization or
  straightening map with this statement.
- DAG search by statement and names found the same realization described in the
  pinched-cube and rigidification-equivalence nodes, which have no recorded
  declaration, and in the downstream coherent-nerve interface. This module constructs
  only the definition explicitly introduced by this item's own statement; it does
  not state any of those independent theorems.

Opened the source HTT PDF at the node's exact URL. Its Proposition the project server says
precisely that the canonical map from point straightening of the strict fiber to
straightening at s is a weak homotopy equivalence for a right fibration; its proof
uses the projective replacement/adjunction/counit argument recorded in this node.
The cone definition and its contravariance agree with Section 2.2.1. No source-based
correction or STATEMENT-DISPUTED flag is needed.

### Validation

The module compiled cleanly through the prescribed `scompile.py` wrapper, both as
an isolated sandbox module and with its delivery module path, with no warning.
All postponed helper laws have source/blueprint and natural-language proof docstrings;
they concern only this node's functoriality, action laws, and canonical endpoint
identifications. The main theorem's docstring records every node proof step.
No theorem was proved and no definition data contain `sorry`.
The node's lean.statement is copied verbatim from the main signature. The node copy
changes only lean and adds the already landed common-join statement dependency.
The nine postponed theorem proofs, all belonging to this node, are:
`coneInclusion_naturality`, `enrichedAction_id`, `enrichedAction_comp`,
`conePushoutMap_vertices`, `valueMap_id`, `valueMap_comp`, `fiberMap_overPoint`,
`attachedInterval_endpoints`, and `right_straightening_fiber_comparison`.
All use the namespace `SSet.Straightening`; a full source search found no prior
namespace or conflicting declaration in Mathlib, upstream, or the side library.
The delivery dry run is the final validation step; its result is recorded below.

Dry run result: `OK (dry run)`, commit `dabcca61a9`; compilation and server preflight
passed except for the independent second-reading section, as expected for a worker
delivery. Nothing was pushed. The second reader must supply that reading and deliver.

## Second reading by NB

I independently read the item record, the HTT source place (Sections 2.2.1 and
Proposition the project server), the complete Lean module, and the recorded dependency
signatures. The item statement has these objects and clauses, matched below.

- The fixed universe `u`, simplicial sets `SSet.{u}`, the enriched coherent
  realization `simplexRealization`, its simplex colimit `realization`, the colimit
  legs `simplexInclusion`, and the vertex object `vertex` render the stated
  \(\mathfrak C[\Delta^m]\) and \(\mathfrak C[S]\). `simplexRealization` uses
  `SimplicialThickening` on `ULift (Fin (n.len + 1))`; `realization` is the
  pointwise left Kan extension and `simplexInclusion` is its colimit leg.
- The join cone is `cone X := Enhanced.orderedJoinFunctor.obj (X, Δ[0])`, with
  `coneMap`, `orderedJoinInl`, and `orderedJoinInr`; its maps are the published
  ordered join maps. This is the node's pure and mixed simplex join, including
  the terminal augmentation and its operators.
- For `a : X ⟶ S`, `conePushout a` is the categorical pushout of the realization
  of the cone inclusion and `realization.map a`. `baseInclusion`, `coneInclusion`,
  and `coneVertex` identify the base leg, cone leg, and image of the pure final
  vertex. `valueAt a c` and `value a s` are exactly the enriched mapping simplicial
  sets into that vertex.
- `precomposition` is the displayed enriched mapping action by the base
  inclusion, and `enrichedAction` curries it. The named identity and composition
  lemmas supply the laws for `straightening a`, an enriched functor out of the
  opposite realized base.
- `conePushoutMap` takes the item’s commuting square
  `a ≫ g = f ≫ b`; `conePushoutMap_vertices` records both endpoint images.
  `valueMap` is the induced enriched map with only those canonical endpoint
  transports. `valueMap_id` and `valueMap_comp` give identity and composition,
  and `valueFunctor S s : Over S ⥤ SSet` packages functoriality over a fixed base.
- The first conclusion conjunct is
  `∀ S s, PreservesColimitsOfSize.{u,u} (valueFunctor S s)`, hence includes empty
  diagrams and all small colimits. The second is
  `∀ S s t, IsIso (representableMap s t)`, where `representableMap` composes a
  coherent mapping simplex from `vertex s` to `vertex t` with the explicit
  adjoined interval arrow `coneArrow t`; its direction is the node’s
  \(\mathfrak C[S](s,t) \to \operatorname{St}_S(\{t\})(s)\).
- The third conjunct quantifies `a,b : X,Y ⟶ S`, `f : X ⟶ Y`, the commuting
  equation over `𝟙 S`, and vertices `s,t`; it states the displayed compatibility
  of `precomposition` with `valueMap`, with the tensor identity on the value.
- The fourth conjunct quantifies arbitrary `X,Y,S`, `a,b`, `j`, and its commuting
  square, assumes exactly `rightAnodyneExtensions j`, and concludes for every
  base vertex `s` that `valueMap` is
  `Enhanced.IsWeakHomotopyEquivalence`.
- The fifth conjunct quantifies `a : X ⟶ S` and assumes precisely
  `∀ n (i : Fin (n+2)), 0 < i → HasLiftingProperty (horn (n+1) i).ι a`.
  It concludes for every `s` that the explicit strict-fiber comparison
  `fiberComparison a s` is a weak homotopy equivalence. `fiber` is the actual
  pullback and `fiberComparison` is induced by `pullback.fst`, `pullback.snd`,
  and the constant point map.
- The sixth conjunct quantifies a square `a,b,f,g,w` between varying bases and
  assumes the same right-horn lifting condition for both `a` and `b`. For every
  `s`, it states the exact naturality equality between `fiberComparison` followed
  by `valueMap` and the point-fiber `valueMap` induced by `fiberMap`, followed by
  `fiberComparison` at `g.app _ s`. `fiberMap_overPoint` is the second pullback
  equation used as its specified proof.

The source assumes no quasicategory condition on the base and no Kan condition on
`X`; the Lean statement likewise has neither. No nonemptiness, finiteness,
Noetherian, characteristic, or extra universe equality is introduced. The source’s
right-fibration condition is represented verbatim by the positive outer horns,
with dimension `n+1`, so dimension one and its final horn are included while no
zero-dimensional condition is imposed.

Edge cases checked are the empty base and empty total space/fiber (all vertex
quantifiers then range over the available vertices, with no chosen inhabitant),
empty colimit diagrams, `n = 0` in the realization, the dimension-one right horn,
`S = Δ[0]`, identity squares, coincident base vertices, and arbitrary non-Kan
`X` and non-quasicategorical bases. The explicit pullbacks and colimit legs do not
exclude these cases.

I searched Mathlib and both the upstream `WeilConjectures` and project `lean/Sheaf`
source trees using LeanFinder, Loogle, LeanSearch, and `rg` for straightening,
rigidification, unstraightening, coherent realization, and the exact theorem name.
The hits were ordinary Kan/strict-Segal/right-fibration infrastructure only; none
states this cone straightening or fiber comparison. The existing
`JoinSliceRightFibration` module was read in full for the ordered-join helpers used
by this construction, and the three original statement dependencies were checked
against their recorded declarations. The HTT PDF was opened at Proposition
the project server and its displayed canonical fiber map agrees with `fiberComparison`.

No mismatch with the node or source was found, so no Lean definition, theorem
signature, hypothesis, conclusion, or dependency statement was changed. The module
compiled with `scompile.py` and contains only explicit definition data and `sorry`
proofs for the nine named helper/main theorems. The node’s `lean.statement` remains
verbatim equal to the theorem signature. The worker’s common ordered-join dependency
addition is retained because the module uses its published helper declarations;
there is no dependency cycle and no private duplicate construction.

## Maintainer review fix (NT-cc reviewer, 2026-10-17)

The mathematics of the delivery is right; one-definition-per-notion (H4) was not.
On the delivery's base, `lem-coef-pinched-cube-latching` (a recorded proof dependency of
this item) had already landed `SSet.PinchedCube.coherentSimplex` and
`SSet.PinchedCube.rigidification`, the same subset-poset coherent simplices and the same
colimit over simplices that this module defined again as `simplexRealization` and
`realization` (with a duplicate `sCatColimits` instance). The landed
`def-coef-infinity-fibrations` carries `SSet.Enhanced.rightFibration` (exactly the right
horns, `n ≥ 1`, `0 < i ≤ n`) and the strict fiber `SSet.Enhanced.fiber`, and the landed
`def-coef-infinity-relative-cone` carries `SSet.Enhanced.rightJoinCone`
(`orderedJoinFunctor.obj (K, Δ[0])`). The fix removes the private copies `simplexRealization`,
`sCatColimits`, `realizationPointwise`, `realization`, `cone`, `fiber` and the inline
right-horn predicate, and uses these landed declarations. `simplexInclusion` is now the
coherent-simplex unit followed by the rigidification of the simplex map; `vertex` is unchanged
in meaning. With `Enhanced.fiber a s = pullback (const s) a` the projections swap (`fst` to
the point, `snd` to `X`), and `fiberComparison`, `fiberMap`, `fiberMap_overPoint` and the sixth
conjunct follow that orientation; the square for `fiberComparison` is now `pullback.condition`
itself. No hypothesis, conclusion or quantifier changed in meaning. The fixed file compiles
clean with `tools/nt_compile.py` (no warning besides `sorry`, no line over 100 characters).
