## Worker report

Item: `lem-sfb-derived-invariants-normal-subgroup-comparison` (Q04, stage 2).
The delivery states `Profinite.CondensedAction.normal_subgroup_comparison` in
`Sheaf.CategoryTheory.CondensedNormalSubgroupComparison`. Its conclusion is the
explicit proposition `NormalAssertion`. There is one postponed theorem, with the
complete fourteen-step natural-language proof from the DAG in its docstring.
All definitions, functorial arrows, comparison isomorphisms, and helper instances
have real bodies. No new axiom, arbitrary comparison morphism, hollow definition,
or separate model of internal action modules is introduced.

The existential packages in `NormalAssertion` are conclusions of the theorem.
In particular Grothendieck abelianness, the normalized invariant functors, their
adjunctions, and K-injective preservation are not additional hypotheses on A, G,
L, K, or a coefficient map. Inclusion and transpose equations determine the
invariant objects and their arrows by their usual universal properties.
`normalComparison`, `normalBeta`, and the derived coefficient transformations
are constructions from the ordinary normalized data and the existing total
right-derived-functor API; they are not existential choices of isomorphisms.

### Hypotheses and clauses, in the order of the node

1. **Any commutative condensed ring, on the small coherent profinite site.**
   `A : CategoryTheory.CondensedBar.Ring.{u}` is the existing
   `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1})`.
   Its existing `toMon` is used everywhere. This is the commutative version of
   the recorded `Profinite.CondensedRing`; it includes all commutative condensed
   rings, rather than only rings obtained by condensing topological rings.
   Test objects have universe u; module categories have object universe u+2
   and morphism universe u+1; derived localizations use universe u+2.
   `NormalComparisonCategories.derived` and `.moduleDerived` record choices of
   localization in precisely these universes. No site/coefficient universe
   equality or size restriction beyond the recorded convention is imposed.

2. **Internal A-linear condensed actions.** The category is the recorded
   `Profinite.CondensedAction.ActionModule A.toMon P`, with its existing
   equivariant hom subgroup, composition, and addition. `ActionAbelian` is the
   existing certificate that this fixed preadditive category is abelian;
   `NormalComparisonCategories.actionAbelian` and `.grothendieck` assert its
   abelian/Grothendieck properties. No arbitrary replacement abelian category
   or equivalence to an unspecified action category is used.

3. **G, L profinite; K open normal; Q finite discrete quotient.** The binders are
   `G L : ProfiniteGrp.{u}` and `K : OpenNormalSubgroup G`.
   `normalQuotient G K` is literally `ProfiniteGrp.of (G ⧸ K.toSubgroup)` with
   the quotient topology. This topology is discrete for an open subgroup,
   and the quotient is finite by compactness. These are consequences of the
   binder, not new assumptions. `normalKernel G K` uses the actual subgroup
   and its induced compact topology. `normalProduct` uses actual products.

4. **Exact inflation, normalized right adjoint T, fixed sections, residual
   action.** Inflation is the existing `inflate` applied to
   `normalProjection G K L`, the actual product of `QuotientGroup.mk'` and
   the identity of L. `NormalInvariantFamily.restrictExact` asserts its
   exactness (as well as arbitrary continuous action restriction).
   `NormalQuotient.functor` is T and `.adjunction` is inflation adjoint to T.
   `.inclusion`, `.injective`, and `.image` identify T with the submodule of
   `Fixed N (normalProjection G K L) S m`. The existing `Fixed` tests every
   profinite base change and every kernel-valued section, so this is internal
   K-invariance, not pointwise invariance by constant elements alone.
   `.residual` specifies the quotient action by lifting a map to G × L.
   `.transpose` and `.untranspose` specify restriction of codomain and
   composition with the invariant inclusion, respectively.

5. **Grothendieck abelian categories, exact forgetting and restriction, total
   unbounded right derived functors by K-injectives.** These are
   `NormalComparisonCategories.grothendieck`,
   `NormalInvariantFamily.forgetExact`, `.restrictExact`, and `.trivialExact`.
   `NormalExact` packages additivity and preservation of finite limits and
   finite colimits. Every complex is indexed by ℤ. The existing Grothendieck
   K-injective instance supplies resolutions; the existing
   `Functor.rightDerivedFunctor` is the K-injective construction used by all
   comparisons. No boundedness, acyclicity, or preservation of K-injectives
   by arbitrary action/scalar restriction is assumed.
   `NormalQuotient.preserves` and `NormalKernelPreserves.preserves` retain the
   specific preservation statements justified by exact left adjoints in the
   node's proof, including restriction k ↦ (k,1) when L is infinite.

6. **First derived comparison β.** `normalBeta A G L K d` has type
   `RT ⋙ D(forgetAction) ≅ D(inflate (normalKernelInclusion G K L)) ⋙ RΓK`.
   The inclusion homomorphism is literally k ↦ (k,1).
   `NormalDerivedComparison.kernel` gives the ordinary fixed-section identity;
   `.kernel_inclusion` pins it to the same map into the original module.
   `normalBeta` derives that identity using the exact postcomposition and
   exact K-injective-preserving precomposition comparison isomorphisms. Thus
   on a resolution its map is the specified fixed-section identity.

7. **Second comparison c, ordinary invariant identity, normalized adjunctions.**
   `normalComparison A G L K d` has type `RΓ(G×L) ≅ RT ⋙ RΓ(Q×L)`.
   `d.ordinary` and `.ordinary_inclusion` say exactly that full invariants
   are quotient invariants of kernel invariants, with the composite inclusion
   equal to the full invariant inclusion. `normalComparison` is constructed
   with `rightDerivedFunctorCompIso'` and that ordinary isomorphism.
   `NormalAdjunctionNormalized` additionally states its equality to the
   conjugate of `normalDerivedInflationIso` under the specified
   derived adjunctions. `d.leftInflation_identity` fixes the exact left
   inflation identification to the identity on the underlying module.

8. **Degree-zero η and its underlying K-invariant unit.**
   `normalResolutionUnit T X` is the canonical unit on a complex, transported
   through `quotientCompQhIso` and `mapHomotopyCategoryFactors` to have source
   `Q(TX)` and target `RT(QX)`. For X = N[0] this is exactly η_N.
   `NormalBetaUnit` explicitly states that under `normalBeta` this is the usual
   K-invariant resolution map, because
   `d.kernel_inclusion` is the identity of the underlying fixed submodules,
   and β is constructed with the canonical exact-square units. No arbitrary
   arrow from ordinary to derived invariants is selected.

9. **Actual inflation and the displayed equation.**
   `normalInflation A G L K d X` is `RΓQ.map (normalResolutionUnit T X)`
   followed by `normalComparison.inv`. `NormalInflationEquation` explicitly states that its composition with c is
   exactly `RΓQ(η)`, including for X = N[0].
   `NormalInflationResolution` states the independent resolution/inclusion
   description: for any K-injective resolution i : X → I, resolution
   a : TX → J, and b : J → TI with a ≫ b homotopic to T(i), inflation is the
   map induced by quotient invariants of b, followed by the actual ordinary
   invariant identification. The quantification over every homotopic lift
   keeps the original canonical inflation arrow, rather than merely defining
   an unrelated arrow to force the displayed equation.

10. **Naturality in equivariant module maps.** T, Γ, β and c are functors or
    natural isomorphisms. `NormalInflationNatural` is the explicit naturality
    equation for every map of complexes. Its specialization to degree zero
    gives the requested equation for every equivariant module map. Stating
    these standard constructions on complexes adds no boundedness condition
    and retains the requested degree-zero specialization.

11. **Naturality in every continuous L' → L.**
    `normalChange A B a G L L' h` composes the recorded scalar-restriction
    functor with the actual action restriction along `id_G × h`.
    Take a to be the identity ring map to obtain the continuous-homomorphism
    clause. `NormalChangeData` specifies the ordinary quotient, total,
    residual, and kernel maps, with section-inclusion equations, and the
    actual kernel restriction identification. Its `.derivedTotal`,
    `.derivedQuotient`, `.derivedOuter`, and `.derivedKernel` use `normalSquare`,
    the universal derived transformation of an ordinary square with exact
    vertical functors. They do not require action restriction to preserve
    K-injectives. `NormalChangeCompatible`, `NormalBetaCompatible`, and
    `NormalInflationCompatible` are the c square, β square, and actual
    inflation square, as equalities of derived arrows.

12. **Successive quotient projections and composition of actual inflations.**
    `J : OpenNormalSubgroup (normalQuotient G K)` is unrestricted.
    `normalTowerOrdinary` composes the two normalized invariant identities,
    representing the composite quotient by T1 ⋙ T2 with its composite
    inclusion. `normalTowerComparison` derives this composite identity;
    `normalTowerInflation` uses the resolution unit for that composite
    functor, transported by the canonical complex composition isomorphism.
    The first conjunct of `NormalTowerCompatible` equates the two derived
    comparison factorizations, including `rightDerivedFunctorCompIso T1 T2`.
    Its second conjunct says that this directly attached composite inflation
    equals inflation for the second quotient followed by inflation for the
    first. It is an equality of arrows, not merely an equality on cohomology
    or a statement about the comparison isomorphism alone.

13. **Every coefficient map, arbitrary equivariant coefficient morphism, and
    derivation of scalar-invariant identities.** In the file, `a : B ⟶ A`
    denotes restriction from A-modules to B-modules; rename B as the node's A
    and A as its A' to obtain exactly A → A'. `NormalScalars.action` uses the
    landed `ScalarAction`, whose underlying comparison is `Mod.comap` and
    whose action equation fixes scalar restriction. `modulesExact` fixes the
    exact nonequivariant `normalScalarRestriction A B a`, whose body is the
    existing `Mod.comap a.hom.hom`. The explicit source/target alias shares this
    scalar functor across all diagrams and avoids repeatedly elaborating it. All ordinary maps in
    `NormalChangeData` have inclusion equations, so their derived maps come
    from the equality of invariant submodules with scalar restriction.
    For h = id, the final conjunct of `NormalAssertion` asserts that the
    canonical total, quotient, residual, and kernel coefficient transformations
    are isomorphisms. No flatness hypothesis is imposed. The preceding
    conjunct gives the three compatibility squares, also simultaneously
    with arbitrary h. The chosen direction of the canonical scalar transformation is
    `RΓ(A') ⋙ D(Res_modules) → D(Res_actions) ⋙ RΓ(A)`; its invertibility supplies the
    node's direction by inversion. Its natural square, inverted, precomposes
    with `RΓ(v)` for every v : N → Res N'. Thus this includes arbitrary
    equivariant coefficient maps,
    rather than just scalar change on an identical underlying module.

14. **K = 1 and evident identity identifications.**
    `NormalTrivialKernel` assumes `Subsingleton K.toSubgroup` (exactly K = 1)
    and asserts invertibility of the actual invariant inclusion and the
    resolution unit. The fixed-section inclusions and the ordinary/kernel
    comparison equations then give the evident ordinary identifications;
    the canonical derived constructions and `NormalAdjunctionNormalized`
    give the identity comparisons under those identifications. There is no
    unspecified self-automorphism in the comparison data.

### Dependency declarations used

Public statement dependencies:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.CategoryTheory.CondensedActionModule`:
  `Profinite.CondensedAction.Modules`,
  `sectionModule`, `ActionModule`, `Fixed`, `Invariants`, `forgetAction`,
  `inflate`, and `trivial` (all in the recorded namespaces).
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`:
  `CategoryTheory.CondensedBar.Ring`, `Ring.toMon`, `ActionAbelian`,
  `actionAbelian`, and `ScalarAction`. The already landed owning node
  `def-sfb-condensed-equivariant-bar-data` is added to stmt_deps. These
  are reused; no second condensed-ring or scalar-action definition is made.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  the recorded resolution-based total-right-derived-functor interface.
  The underlying live `Functor.rightDerivedFunctor` and its unit are the
  existing K-injective construction, not a new local implementation.
- `Sheaf.CategoryTheory.CondensedNormalInvariantData`:
  `Profinite.CondensedAction.normalDerivedInflationIso`, constructed from
  `NormalDerivedComparison.leftInflation` using Mathlib's derived composition
  and natural-isomorphism descent. Its owning definition node is already in
  stmt_deps.
- Existing Mathlib `ProfiniteGrp`, `OpenNormalSubgroup`, quotient group and
  quotient topology; exact-functor derived-category machinery. Existing live
  `Functor.rightDerivedFunctorCompIso`, `rightDerivedFunctorCompIso'`,
  `rightDerivedFunctorNatIso`,
  `rightDerivedFunctorCompMapDerivedCategoryIso`,
  `mapDerivedCategoryCompRightDerivedFunctorIso`, and their units.

The recorded proof dependency modules are also imported privately: internal
ringed action-site presentation; ringed-site Grothendieck abelianness;
split-coset induction; Grothendieck K-injective resolutions; the exact-square
comparison; exact-left-adjoint K-injective preservation; ringed-topos morphisms,
derived pushforward composition and its cocycle. Their recorded declarations
were read. In particular, `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`
provides `CategoryTheory.Adjunction.derivedCompositionAdjunctionNormalization`
for the proof; its node remains in proof_deps only. The K-injective Hom comparison is Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective`. They are inputs to the detailed
postponed proof, not additional hypotheses in the main theorem.

### Edge cases checked

- K = 1: the image condition becomes the whole underlying module; normalized
  inclusions give the identity case, recorded by `NormalTrivialKernel`.
- K = G: allowed, since the top subgroup is open; Q is the trivial group and
  the same product/quotient functors still type.
- G = 1 or L = 1: actual product and quotient carriers are retained, with
  canonical identifications instead of definitional equality assumptions.
- Infinite L and non-surjective h, including the trivial homomorphism:
  `NormalKernelPreserves` singles out restriction to K; `normalSquare` never
  assumes arbitrary restriction preserves K-injectives.
- Zero coefficient ring and zero module: all assertions use submodules,
  adjunctions and unbounded resolutions; none uses nonzero coefficients or
  division by a finite group order.
- Nonflat coefficient maps: no tensor-exactness hypothesis or K-injective
  preservation by `Mod.comap` is present. The coefficient square is derived
  by its universal unit, and its invertibility is a theorem conclusion.
- Two successive nontrivial open normal kernels, and either kernel trivial:
  `NormalTowerCompatible` quantifies over all J and includes actual inflation
  composition, with the complex and derived composition isomorphisms visible.

### Searches

The prescribed search wrapper recorded the following successful searches in
`searches.jsonl` (2026-10-21 UTC):

- LeanFinder: “Unbounded derived invariants for internal condensed modules
  through an open normal subgroup with normalized inflation and coefficient
  compatibility”: eight results about CondensedMod, LightCondMod, solidness,
  abelianness and Grothendieck properties; no requested comparison theorem.
- Loogle: `"invariants", "DerivedCategory"`: no hits.
- Mathlib grep: `(quotientToInvariants|derived.*invariant|invariant.*derived)`:
  ordinary representation invariants and group (co)homology, without the
  internal condensed action or normalized unbounded comparison statement.
- LeanSearch: “Derived invariants of condensed modules under an open normal
  subgroup, with quotient inflation and scalar restriction”: eight hits,
  including `Rep.quotientToInvariants`, `Representation.quotientToInvariants`,
  `groupCohomology.H1InfRes` and `groupCohomology.infNatTrans`. These concern
  ordinary representations over an ordinary ring and do not state this node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for normal subgroup,
  quotient/invariant and derived-invariant names: existing discrete-module,
  continuous-cochain, group-theoretic and normalization machinery, but no
  declaration with this node's statement. Searching the exact node id in
  both source trees returned no matching declaration.

The source blueprint paragraph (3) was read. As the node itself records, the
condensed-action comparison is an agent-formulated formal input to that local
calculation, not a literal theorem in that paragraph. The delivery follows the
full node statement and its fourteen-step proof, without changing its statement,
source, proof, proof_deps, or maintained review fields. There is no statement dispute, source-based statement correction, or
repair of an existing dependency. The normalized invariant datum is delivered
as one new definition node and module to keep per-file compilation within the
required limit. The remaining helper diagrams belong to the item. Every
helper is listed in its owning node's lean.declarations and has that blueprint id.

### Validation

The prescribed `scompile.py` compiled both modules separately against the live
published build, including their final library names, without errors or
warnings (datum module 43.8 s, theorem module 54.5 s). A temporary signature
check printed `NormalAssertion : Prop` and
`normal_subgroup_comparison : NormalAssertion`: the theorem has no extra
categorical-instance hypothesis. Those diagnostic commands have been removed.
The final delivery is subjected to `deliver2.py --no-push` preflight and its
per-file server compilation before the real delivery.

## New nodes

`def-sfb-normal-invariant-comparison-data` defines the normalized fixed-section
quotient datum, its Grothendieck/derived categorical certificate, ordinary
invariant identities, and the canonical unbounded comparison, unit and
inflation constructions with their normalization predicates, and the canonical
derived left-inflation identity `normalDerivedInflationIso`. It is a definition
of the reusable datum, with no assertion that such a datum exists and no
postponed proof. Its module is
`Sheaf.CategoryTheory.CondensedNormalInvariantData`; the main declaration is
`Profinite.CondensedAction.NormalSystem`. It follows the same blueprint
paragraph (3), in the formal open-normal-kernel expansion recorded by the item.
The item's stmt_deps gains this id. Its own stmt_deps cite exactly the five
recorded definitions used for coefficients, size, internal actions and total
derived functors.

The LeanSearch, LeanFinder, Loogle and Mathlib grep searches reported above
also search for this datum and are recorded in its mathlib_searches. No result
gives this normalized internal-action quotient datum. The additional pattern
`normal.invariant.comparison.data|normalized quotient.*datum|normal subgroup.*datum`
was searched in Mathlib, both project source trees, and the DAG: the only
project-source hit was an unrelated semicontinuity module. The blueprint
search `normal invariant comparison` had no matching blueprint node.
`tools/blueprint_refs.py ancestor` reports null as this item's blueprint ancestor;
the new node records that result and prepends the item to its existing via path.
This adds a missing reusable definition, without changing the reviewed
mathematical statement or re-splitting its proof.

## Returned-delivery repair

The return on immutable head `adef578762a9` identified H2: stmt_deps cited
`lem-sfb-derived-composition-adjunction-normalization` solely to obtain its
plain helper definition, without using its theorem conclusion in the statement.
The retained packet was compared with the current read-only main node: only
lean and the previously added stmt_deps differed; the mathematical statement,
proof, proof_deps, and maintained fields agree.

The datum definition node now owns `normalDerivedInflationIso`, listed in
lean.declarations and used by `NormalAdjunctionNormalized`. Its body is exactly
`(mapDerivedCategoryCompIso La Lb).symm ≪≫ mapDerivedCategoryNatIso d.leftInflation`.
Unfolding gives the former `Adjunction.derivedCompositionLeftIso` by rfl; no
postponed proof or new mathematical condition is involved. The definition is
specialized to the datum, rather than duplicating the general composition API.
The theorem node was removed from stmt_deps and retained unchanged in
proof_deps; its module is now a plain proof import. Both the ordinary
left-inflation identity and all derived normalizations are preserved.

The new specialized declaration name was searched with rg in Mathlib and both
project source trees; no existing declaration uses that name. The saved packet's
searches and the source/API readings above supply its underlying construction.
The repair changes no hypothesis, clause, universe, coefficient arrow or edge
case from the independently reviewed delivery. In particular the trivial-kernel
case still uses the same canonical descent and normalized conjugation.

The first repaired compile found that changing the normalization module to a
proof import also hid the derived-adjunction API previously re-exported by it.
The statement module now explicitly publicly imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`,
whose `Adjunction.mapDerivedCategoryRightDerivedAdjunction` is used by the
normalization predicate. The specialized datum module already compiled cleanly.

The required first dry run of the retained packet passed as `a4730638be8`.
That preliminary success predates this repair's final checks; the repaired
packet is compiled and dry-run again before delivery.

Final repaired `scompile.py` validation passed for both modules with no errors
or warnings: datum library compilation 33.2 s; theorem library compilation
33.6 s. The intermediate sandbox checks also passed. JSON field comparison
confirms that the item differs from current main only in lean and the two
authorized definition-node additions to stmt_deps; proof_deps is unchanged.
Both modules have no lines over 100 characters and explicitly disable
autoImplicit. Only the main theorem contains sorry.

## Second reading by Q04

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
