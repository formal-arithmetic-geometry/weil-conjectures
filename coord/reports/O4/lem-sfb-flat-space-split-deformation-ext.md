## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.SplitSpace.flat_space_split_deformation_ext`
in `Sheaf.AlgebraicGeometry.FlatSpaceSplitDeformationExt`. The item is unchanged except
for its Lean binding and the added statement dependencies. There is no statement correction,
no disputed statement, and no repair note for this item. Every theorem proof is `sorry`.
The two new modules give actual geometric and tensor constructions; all data are explicit
or selected by a genuinely unique universal property, never an unconstrained existence.

Clause-by-clause rendering:

- Any field K: `{K : Type u} [Field K]`. Every characteristic is allowed.
- Algebraic space over Spec K: `X : AlgebraicSpace (Spec (.of K))`. The morphism to
  Spec K is `structureMap X`, the existing unique morphism to the representable terminal
  base, wrapped as an algebraic-space morphism. Flatness is the explicit hypothesis
  `hflat : MapIsFlat (structureMap X)`, using scheme Flat on every compatible etale chart.
- Every coefficient vector space: `M : ModuleCat.{u} K`. This bundles precisely an
  additive commutative group with a K-module structure; no dimension bound occurs.
  The explicit canonical opposite action and centrality instance derive the right action
  from the left action, adding no hypothesis.
- The ring K direct-sum M and its multiplication: reuse `TrivSqZeroExt K M` via
  `SplitModule.base`, `ProperCurveFamily.directionBase`, and `directionMap`.
  These use `Spec.map` on the actual ring maps, including `(b,m) -> (b,h(m))`.
- A flat marked algebraic-space deformation: `Marked X M` has its actual `space`,
  `projection` to `SplitModule.base M`, chartwise `flat`, `marking : X -> space`, and
  `cartesian` square over `SplitModule.baseZero M`. A cartesian marking is exactly an
  identification of the special fibre with X; it includes the marking, not its mere existence.
- Isomorphisms respect both structures: `Related X D E` asks for `e : D.space ≅ E.space`
  with `e.hom ≫ E.projection = D.projection` and `D.marking ≫ e.hom = E.marking`.
  `Classes X M := Quot (Related X)` is exactly the class set, since this relation is
  reflexive, symmetric and transitive. `classOf` is its quotient map.
- Infinitesimal automorphisms: `AutZero X M` is the subtype of automorphisms of the
  ACTUAL product `SplitModule.space X M` that fix the projection to Y_M and the fibre
  inclusion. It does not require fixing the projection back to X.
- The tensor coefficient: `coefficient X M` is module sheafification of
  `coefficientPresheaf X M`. At U the latter is
  `(ModuleCat.extendScalars (fieldMap X U)).obj M`, precisely O_X(U) tensor_K M.
  `fieldMap` pulls functions through the chart morphism and `Scheme.ΓSpecIso`.
  Restriction sends s tensor m to res(s) tensor m, by the unique specification in
  `coefficientRestriction_existsUnique`. This is sheafification, not a false assertion
  about arbitrary global sections commuting with tensor products.
- The cotangent and Ext definitions: `Ext X M n` uses the dependency's `derivedExt`,
  `naiveCotangent (structureMap X)`, and `cotangentCoefficient X (coefficient X M)`.
  Thus it is Hom from NL to the degree-zero coefficient shifted by n in the SAME
  small-model derived module category. The localization morphism universe w is arbitrary;
  `[HasDerivedCategory.{w} X.SmallModules]` is its size parameter, not a smaller-site
  restriction or an equality of localization and section universes.
- Both identifications: the existential families `deformation M : Classes X M ≃ Ext X M 1`
  and `automorphism M : AutZero X M ≃ Ext X M 0` are simultaneous across every M.
- Trivial origin: the first conjunct produces a marked trivial family for every M;
  the second says every `IsTrivial` representative maps to zero. `IsTrivial` uses a
  marked isomorphism to the existing product and its existing fibre inclusion.
- Arbitrary coefficient naturality: for every `h : M ⟶ N` and D, a target E with
  `PullsBack X h D E` exists, and EVERY such E has class
  `extMap X h 1 (deformation M (classOf X D))`.
  `PullsBack` is an actual cartesian square over the specified `Spec.map` and an equality
  of markings. `coefficientMap X h` sheafifies `1 tensor h`; `extMap` postcomposes with
  its shifted degree-zero image. Zero and noninjective maps are included.
- Scalars: `ModuleCat.ofHom (a • (LinearMap.id : M →ₗ[K] M))` is the prescribed ring-base
  operation. The explicit scalar clause is its coefficient action on Ext. Its existence
  also follows from the arbitrary-coefficient existence conjunct above.
- Addition: for D,E a `G : Marked X (ModuleCat.of K (M × M))` with `IsGluing X D E G`
  exists. This relation specifies `IsPushout D.marking E.marking i j`, the two coordinate
  base projections, and the common marking. It is the actual geometric gluing along X,
  not an arbitrary operation selected through the desired Ext equivalence. The theorem
  also asserts uniqueness up to marked isomorphism. Pullback by `fst + snd` exists and
  every such result maps to the sum of the two Ext classes.
- Automorphism zero: identity exists in the subtype and every such identity maps to zero.
  Composition: a subtype element with `t.val = g.val ≪≫ h.val` exists, and every such
  element maps to the sum. Thus the equivalence respects the given group law.
- Automorphism coefficient naturality: the actual product map `SplitModule.change X h.hom`
  intertwines g and t, as expressed by `AutPullsBack`; such t exists and maps to `extMap h 0`.
  Since the product map is the pullback projection and both automorphisms fix their bases,
  this equation specifies the base-changed automorphism uniquely. Scalars are the same
  construction for `a • id`, stated explicitly in the last conjunct.
- Vector-space operations: these pointed bijections preserve exactly the geometric
  operations and the usual coefficient-induced scalar and additive operations on derived
  Hom. Consequently the vector-space laws transfer along the bijections. No independent
  arbitrary vector-space structure or finite-dimensional assumption is supplied.
- No properness, dimension, finite-presentation, quasi-compactness, or Noetherian hypothesis
  occurs on X. There is no finite-generation assumption on M.

Dependencies used (module and declaration):

- Mathlib.Algebra.Field.Defs: `Field` (def-weil-field, mathlib match).
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicGeometry.AlgebraicSpace`, its Modules,
  chart categories, structure sheaf and presheaf (def-trf-algebraic-space).
- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`, through
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`'s `MapIsFlat`.
- Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex: `naiveCotangent`, `derivedExt`,
  `cotangentCoefficient`; these retain the actual ring inverse image and original section size.
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses: recorded tensor interface,
  with module sheafification and scalar extension from its public dependency chain.
  The coefficient uses the existing Mathlib `ModuleCat.extendScalars` and
  `PresheafOfModules.sheafification`; there is no second tensor implementation.
- Sheaf.AlgebraicGeometry.MarkedSplitModuleDeformations: `SplitModule.base`, `baseZero`,
  `baseMap`, `space`, `toBase`, `fibre`, `change`. These are geometric bases/products only;
  its unrelated Marked MODULE deformation notion is not copied or used as a space deformation.
- Sheaf.AlgebraicGeometry.MarkedCurveDeformations: `ProperCurveFamily.directionMap`;
  `directionBase` supplies the actual split ring. No curve condition is inherited.
- Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization:
  `space_square_zero_ringed_realization` is imported as a proof dependency, privately.
  The conormal-flatness and sheaf-algebra extension classification nodes presently lack
  Lean records, so their proof-only imports are omitted; their mathematical steps remain
  in the full main theorem docstring. They are not needed to TYPE the statement.

Edge cases checked against definitions and source:

M=0 gives Y_M=Spec K and only a trivial marked class and identity infinitesimal
  automorphism, matching zero Ext coefficients. Empty X gives the empty family and
  zero module category; no nonemptiness hypothesis excludes it. Infinite-dimensional M
  is permitted: tensor sheafification and all ModuleCat quantifiers have no finite bound.
  K can have characteristic two: summation is `fst + snd`, with no division. The zero
  scalar and zero coefficient map are included in the base-change and coefficient formulas.
  Identity maps and noninjective maps impose no extra conditions. Universes use the
  project's common ambient scheme/section universe u (enlarge u to contain K, X, M when
  necessary), while derived localization universe w remains independent.

Searches (all run before finalizing the new nodes):

- msearch leanfinder: flat algebraic-space deformations over split square-zero extensions
  classified by cotangent Ext, naturally in vector spaces. Eight hits on ring cotangent
  and formal smoothness, no algebraic-space theorem.
- msearch leansearch: marked flat algebraic-space deformations and isomorphism classes.
  Eight hits on ring derivations and square-zero primitives, no geometric class set.
- msearch leansearch: sheafification of presheaf tensor with a constant vector space.
  Found `PresheafOfModules.sheafify` and standard sheafification, used through the existing API.
- msearch leanfinder: regular functions tensor constant vector space on algebraic-space
  etale site. Found scheme Zariski `ModuleCat.tilde`, not the requested etale coefficient.
- msearch loogle `TrivSqZeroExt`: exact split ring exists and is reused. The first query
  `TrivSqZeroExt, CategoryTheory.Ext` reported an unknown second identifier; the corrected
  query succeeded with twelve hits. No duplicate ring was introduced.
- msearch grep in Mathlib AlgebraicGeometry: deformation/Deformation/cotangent and
  Deformation/TrivSqZeroExt. Only etale/formal-unramified ring-cotangent references, no theorem.
- rg in lean/WeilConjectures: no item id and no split algebraic-space deformation class
  or coefficient interface. Deformation-to-normal-cone constructions are unrelated.
- rg in lean/Sheaf: found MarkedCurveDeformations, MarkedSplitModuleDeformations and
  SplitModuleDeformationExt; the first restricts to proper curves, the latter two deform
  module sheaves. Reused their geometric bases and product maps. No declaration in the
  new SplitSpace namespace exists upstream or in Mathlib.
- blueprint_refs.py search split-coefficient / marked-split-deformations: zero matches.
  DAG search found the item itself and the separate curve/module nodes, not these notions.
  The new nodes retain successful msearch records verbatim as JSON results in mathlib_searches.

Validation: all THREE delivered modules compiled separately, in dependency order,
using the required scompile.py wrapper against the published live library; no errors
or non-sorry warnings. The source files are module-mode with explicit universes and
`autoImplicit false`, all declarations public/exposed, and all lines at most 100 characters.

## New nodes

`def-sfb-space-split-coefficient` owns SpaceSplitCoefficient.lean. It defines the genuine
sectionwise scalar extension, tensor restriction determined by its pure-tensor formula,
identity/composition laws, sheafification, and the coefficient-induced Ext maps using
exactly the recorded naive cotangent complex. The three postponed theorems are the
restriction universal property, presheaf laws, and coefficient-map naturality; their
statements are included explicitly in this node and each has a full proof docstring.
Source: Stacks 0D17 split conormal coefficient and Modules on Sites 03EK. Existing
sheafification/tensor primitives do not specify the K-action on this algebraic space
and its exact natural coefficient map. Search evidence is recorded on the node.

`def-sfb-space-marked-split-deformations` owns SpaceMarkedSplitDeformations.lean. It defines
actual marked flat algebraic-space families and their class set, triviality, geometric
base change and pushout gluing, infinitesimal automorphisms and their coefficient change.
It reuses the actual split bases/products from the separate MODULE-deformation node.
Source: Stacks 0D17 and artin.tex section-inf. A curve-family interface would add forbidden
properness/dimension hypotheses; a module deformation is a different object. These are
new definitions, with no postponed theorem or existence of a deformation baked into them.
The canonical right-action instances have explicit data and definitional proof fields.
Search evidence is recorded on the node.

## Second reading by O4

A separate final reading pass reopened the item JSON, all three Lean files, the source
Tag 0D17 and artin.tex section-inf, and the two new node statements. This was performed
in this worker session: the dispatcher explicitly forbids starting another agent, so
no claim of an independent second worker is made. Independent mathematical review is
left to the maintainer as specified in the dispatch brief.

The pass matched every item clause to the Lean rendering listed above. In particular it
checked that families are algebraic spaces rather than proper curves or module sheaves;
flatness is chartwise flatness of their projection; markings are cartesian and preserved;
the coefficient is a sheafified tensor, not tensor of arbitrary global sections; both
Ext degrees use the recorded cotangent object; and naturality includes noninjective maps.
It checked both projections in the gluing base and the SUM map, and that automorphisms
need not fix the projection to X. It also checked arbitrary derived morphism universe w.

Two elaboration issues were repaired during drafting: the terminal base map uses existing
`SplitModule.baseMap` rather than a nonexistent topology field, and `SplitModule.base`
receives explicit `(k := K)` where coefficient data otherwise leave a metavariable. These
repairs change no mathematical statement. The new node TeX was normalized to single
backslashes. All three final modules compiled cleanly after those corrections. No
hypothesis or conclusion mismatch remains; no node statement correction was needed.
