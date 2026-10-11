## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris` states
`AlgebraicGeometry.derivedBaseChange_mayerVietoris_naturality`, with its sole proof
`sorry`. It introduces no definitions. The item statement and its dependency lists
are unchanged. Source checked: [Stacks 0DJ9, induction step](https://stacks.math.columbia.edu/tag/0DJ9)
and [Stacks 08BV](https://stacks.math.columbia.edu/tag/08BV). The local copy of
`literature/stacks-project` is absent on this machine, so the published source was
read directly. The two proof steps supplied by the node are in the theorem docstring.

Hypotheses, individually:

- Four schemes and the four arrows: `{X S X' S' : Scheme.{u}}`, `f`, `f'`, `g`, `g'`.
- The square is cartesian: `hsq : IsPullback g' f' f g`. Its `hsq.w` is the
  commutativity used by the recorded base-change map. This allows any cartesian
  square, not just the chosen implementation of a fibre product.
- The morphism `f` is quasi-compact and quasi-separated: `[QuasiCompact f]`
  and `[QuasiSeparated f]`.
- Both bases are affine: `[IsAffine S]` and `[IsAffine S']`.
- The objects are in the quasi-coherent derived categories: `K`, `K'` are in the
  ambient `schemeDerivedCategory`, and `hK`, `hK'` assert
  `schemeDerivedQCohProperty`. This is equivalent to using the full subcategories.
- The given derived morphism is `ψ : (derivedPullback g').obj K ⟶ K'`.
- The two opens are `U V : X.Opens`; their quasi-compactness is `hU`, `hV`.
- The intersection is quasi-compact: `hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)`.
- They cover the source: `hcover : U ⊔ V = ⊤`.
- The common explicitly quantified universes `u w`, together with the family of
  `HasDerivedCategory.{w}` localization choices, follow the recorded base-change
  constructor's requirements. The localization family is categorical infrastructure,
  not a geometric restriction. No dimension, boundedness, perfectness, flatness,
  nonempty-open, or nonempty-scheme assumption is imposed.

Clauses of the conclusion:

1. The primed opens are literally `g' ⁻¹ᵁ U`, `g' ⁻¹ᵁ V`, and
   `g' ⁻¹ᵁ (U ⊓ V)`. These are the open-subscheme fibre products from the node.
   The intersection of the first two is the third. In the primed second arrow,
   `(Opens.map g'.base).map (homOfLE inf_le_left/right)` supplies precisely the
   two inclusions of the inverse-image intersection.
2. The six `adjU`, `adjV`, `adjUV` and primed adjunctions, and the two boundaries
   `δ`, `δ'`, are existential construction data, in the same format as the
   recorded `schemeDerived_mayerVietoris_triangle` theorem. The first arrow is
   `biprod.lift` of restriction units; the second is `biprod.desc` of the first
   restriction and the negative of the second. Both displayed triangles are
   required to belong to `distTriang` on their respective sources.
3. The source functor is exactly `schemeDerivedDirectImage f ⋙ derivedPullback g`;
   the target functor is exactly `schemeDerivedDirectImage f'`. The shift structures
   `csF`, `csG` are explicit existential infrastructure. `@Functor.mapTriangle`
   applies these functors to the two displayed Mayer--Vietoris triangles, and both
   resulting triangles are explicitly required to be distinguished in `D(O_S')`.
4. The component on `X` is fixed by the equation for `φ.hom₁`: the recorded
   `schemeDerivedBaseChangeMap f f' g g' hsq.w K`, followed by `Rf'_*` of `ψ`.
5. Each of `aU`, `aV`, `aUV` has its own defining equality. It first applies
   base change for `f` to `Rj_W* (K|W)`, then `Rf'_*` of base change for the open
   immersion `j_W`, then `Rf'_* Rj_W'*` of the restricted given morphism.
   The latter uses the inverse of the recorded
   `derivedPullback_openRestriction_iso`, followed by exact open restriction of `ψ`.
   These auxiliary existential maps are fixed by equations, not unconstrained maps.
   Under the canonical direct-image composition identifications specified by the
   node, pasting the two base-change maps is the single base-change map for
   `j_W ≫ f : W → S`. Thus these are precisely `α_U`, `α_V`, `α_(U∩V)` in
   the pre-identification coordinates, not an alternative comparison map.
6. The two equations for `φ.hom₂` composed with `Rf'_*` of `biprod.fst` and
   `biprod.snd` specify exactly `α_U ⊕ α_V` under the standard preservation
   of finite biproducts by the exact derived functors. They avoid introducing a
   separately chosen biproduct isomorphism.
7. `φ.hom₃ = aUV` fixes the intersection component. Crucially, `φ` is an actual
   morphism in the category of `Pretriangulated.Triangle`, not just three arrows.
   Its fields `comm₁`, `comm₂`, `comm₃` give all three squares. In particular,
   `comm₃` involves the shifted first component and hence includes the connecting
   square required by the node. `mapTriangle` includes each functor's shift
   comparison in its third arrow.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-pc-base-change`: its module `Sheaf.AlgebraicGeometry.BaseChangeConventions`
  explicitly delegates scheme fibre products to Mathlib; its main declaration
  `Scheme.Modules.moduleBaseChange` concerns module base change, not this square.
  This statement uses the delegated `CategoryTheory.IsPullback` and Mathlib's
  inverse-image open subschemes, rather than misusing `moduleBaseChange`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, and the full-subcategory interpretation
  `schemeDerivedQCohCategory`.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback` and its
  existence theorem's triangulated-functor specification.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle`:
  `schemeDerived_mayerVietoris_triangle`; the displayed source triangles reuse
  its exact statement shape, restriction maps, and existential adjunction format.
- `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`:
  `schemeDerivedBaseChangeMap`. This constructor works for any commutative square,
  including the square formed by an open immersion and its inverse image.
- Existing helper declarations (no replacement definitions):
  `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps` supplies
  `schemeOpenRestriction` and `schemeDerivedOpenDirectImageRestriction`;
  `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` supplies
  `derivedPullback_openRestriction_iso`;
  `Mathlib.AlgebraicGeometry.Restrict` supplies `Scheme.Hom.resLE` and
  `Scheme.Hom.resLE_comp_ι`; `Mathlib.CategoryTheory.Triangulated.Functor`
  supplies `Functor.mapTriangle`; `Mathlib.CategoryTheory.Triangulated.Basic`
  supplies `Triangle`, `TriangleMorphism`, and its three commuting-square fields.
  All helper signatures and docstrings were inspected.

Edge cases checked before finalizing: `K = 0`, `K' = 0`, and `ψ = 0` give the
expected zero comparison maps. Either open may be empty; then the overlap and its
component are zero, and there is no forbidden nonemptiness premise. The cover may
have `U = V = ⊤`: the second arrow retains the required difference sign. Disjoint
opens give zero overlap and zero connecting map. Identity base change recovers
naturality of Mayer--Vietoris in the object. No restriction on the characteristic
or on cohomological degree occurs. No counterexample or statement correction found.

Searches performed through `msearch.py` and direct source searches:

- LeanFinder: `naturality of derived base change morphisms with Mayer Vietoris
  distinguished triangles of schemes`. Eight hits, involving gluing-cover
  identities, sheaf Mayer--Vietoris-square gluing, and scheme morphism naturality;
  none is this derived O-module triangle statement.
- Loogle: `CategoryTheory.Triangle, CategoryTheory.TriangleMorphism`.
  Zero hits; the service reports unknown identifier `CategoryTheory.Triangle`
  (the declaration is under `Pretriangulated`, as direct source inspection shows).
- Mathlib grep: `MayerVietoris|baseChange.*Triangle` in `AlgebraicGeometry`.
  Zero hits.
- LeanSearch: `derived Mayer Vietoris triangle naturality base change`.
  Unavailable: Internal Server Error. The other searches and direct source
  inspection were used; this is not counted as a negative mathematical result.
- Direct `rg` of `WeilConjectures` for `MayerVietoris|mayerVietoris` finds pro-etale
  adic six-functor material, not unbounded derived O-modules; the item id has no hit.
- Direct `rg` of `lean/Sheaf` for `MayerVietoris|mayerVietoris|schemeOpenRestriction`
  identifies the shared dependency and helper modules listed above, and unrelated
  etale cohomology and Hom Mayer--Vietoris statements. Searching for
  `baseChange.*mayer|mayer.*baseChange|mayerVietoris_naturality` finds no existing
  statement. The upstream name index has no matching declaration.

Validation: server single-file compilation clean in 8.9 seconds, default heartbeats
and fixed 120-second file limit. An initial inference timeout in the primed
restriction inclusions was repaired by supplying the actual image of the open
inclusion under `Opens.map g'.base`; no larger heartbeat setting remains. All lines
are at most 100 characters, and `autoImplicit` is disabled. The only postponed
proof is the named theorem above. The second reading is left to the independent
reader, as required by the worker brief.

## Second reading by V1

I independently read the node statement, its source places (Stacks Tags 0DJ9 and 08BV),
all recorded statement dependencies, and the Lean declaration.

- Objects: the Lean binders `{X S X' S' : Scheme.{u}}`, arrows `f f' g g'`, and
  `hsq : IsPullback g' f' f g` render the cartesian square. The affine instances on
  `S,S'` and `[QuasiCompact f] [QuasiSeparated f]` render exactly the stated
  hypotheses. `K,K'`, their `schemeDerivedQCohProperty` hypotheses, and
  `ψ : (derivedPullback g').obj K ⟶ K'` render the derived objects and map.
- Cover data: `U,V : X.Opens`, compactness of `U,V,U ⊓ V`, and `hcover : U ⊔ V = ⊤`
  render the quasi-compact open cover and quasi-compact overlap. The primed opens
  are exactly inverse images `g' ⁻¹ᵁ U`, `g' ⁻¹ᵁ V`, and
  `g' ⁻¹ᵁ (U ⊓ V)`, with the latter used in every primed overlap term.
- Mayer--Vietoris data: the three adjunctions and boundary `δ`, and their primed
  counterparts `δ'`, produce the two triangles with first map `biprod.lift`, second
  map the restriction difference via `biprod.desc`, and explicit distinguishedness
  in the corresponding derived category. This is the dependency node's triangle
  shape, including the connecting morphism.
- Functorial conclusion: explicit `CommShift` structures `csF, csG` and
  `Functor.mapTriangle` render applying `Lg^* Rf_*` and `Rf'_*`; both mapped
  triangles are required distinguished in `D(O_{S'})`. The existential `φ` is a
  `Pretriangulated.Triangle` morphism, so its three commuting squares include the
  connecting square. `φ.hom₁` is exactly the stated base-change map followed by
  `Rf'_* ψ`.
- Components: the existential `aU`, `aV`, and `aUV` are fixed by the displayed
  composites: base change for `f`, then base change for the open immersion, then
  the inverse restriction comparison and restricted `ψ`. The two `φ.hom₂`
  projection equations give precisely `α_U ⊕ α_V`, and `φ.hom₃ = aUV` gives the
  overlap component. No unconstrained comparison map is introduced.

No mismatch was found and no source or node correction was needed. The source's
induction-step diagram permits the affine reduction used by the node; the Lean
statement includes those affine assumptions explicitly as the node does. Edge
cases checked are zero `K`, zero `K'`, zero `ψ`, empty opens, empty overlap,
`U = V = ⊤`, disjoint opens, identity base change, and arbitrary characteristic;
none is excluded by an added hypothesis. Universes are shared by all schemes and
by the derived-category instance family, so no independent index universe is
introduced.

Searches were repeated with `msearch.py` (LeanFinder and Loogle queries for
Mayer--Vietoris/base-change triangle naturality), `rg` over Mathlib,
`WeilConjectures`, and `lean/Sheaf`, and the upstream name index. No existing
statement or definition matching this node was found; the recorded dependencies
are the shared declarations. Lean compilation with `scompile.py` completed cleanly
(only the named theorem `sorry`).
