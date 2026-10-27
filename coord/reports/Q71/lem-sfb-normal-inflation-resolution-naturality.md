## Worker report

The delivery states `lem-sfb-normal-inflation-resolution-naturality` in
`Sheaf.CategoryTheory.NormalInflationResolutionNaturality`. Every theorem has proof
`sorry`; every definition has actual data. There is no statement correction, new DAG
node, or dependency-record change. The primary declaration is
`Profinite.CondensedAction.normalInflation_resolution`; the other declarations in the
Lean record supply the remaining clauses and the canonical auxiliary comparisons.

Source read: the complete node statement and nine proof steps, all statement-dependency
records and their signatures/docstrings, and
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). As the node explicitly
records, that paragraph motivates the direct-image application; the detailed condensed
normal-subgroup lemma is agent-formulated infrastructure, not text asserted by the
blueprint itself. The theorem docstrings follow the node's nine-step argument and name
the relevant K-injective Hom, composition-adjunction, and restriction-mate inputs.

Hypotheses and objects:

- `A : CategoryTheory.CondensedBar.Ring.{u}` is the recorded bundled commutative
  internal condensed ring on `coherentTopology Profinite.{u}`. Its `toMon` is the
  underlying `Profinite.CondensedRing`. No topological presentation of A is required.
- `NormalComparisonCategories.{u}` supplies the fixed preadditive action categories'
  Grothendieck abelian certificates and localizations. `NormalInvariantFamily.{u}`
  supplies exactly the normalized fixed-section inclusions/adjunctions and exact
  restrictions/trivial inflations. `NormalSystem.{u}` supplies the quotient data and
  ordinary inclusion-normalized comparisons specified by the statement's dependency.
  These are the recorded categorical data of the setting, not replacement arbitrary
  maps or assumptions of the conclusions proved here.
- `G L : ProfiniteGrp.{u}` and `K : OpenNormalSubgroup G` give the actual quotient
  `G ⧸ K.toSubgroup`, `normalQuotient G K`, the actual kernel `normalKernel G K`,
  `normalProjection G K L`, and `normalKernelInclusion G K L` (k maps to (k,1)).
- The category is always `ActionModule A.toMon P`, the dependency's internal action
  category, not abstract representations or a category of constant-ring modules.
  Derived categories are the ordinary unbounded `DerivedCategory.{u + 2}` of the
  recorded action/module categories. No boundedness or additional size equality is
  imposed. A module N in degree zero is the existing `(CochainComplex.single₀ _).obj N`.
  Resolution identities are written for complexes, as in the dependency's existing
  canonical resolution predicates and the node's proof; their module specializations
  give each asserted N[0] formula without choosing a bounded resolution.

Clause-by-clause rendering:

1. Normalized invariant inclusions, quotient adjunction and K-injective preservation
   are the existing `NormalQuotient`, `NormalDerivedComparison`, and the models
   theorem's exported `openNormalKernelPreserves`. The specified beta is the existing
   `normalBeta`. Its resolution normalization is the imported
   `openNormalActionInjectiveModels`, including its equality on all unbounded models.
2. The canonical c is the existing `normalComparison`. The theorem
   `normalComparison_conjugate` identifies precisely this c with
   `conjugateIsoEquiv` of the descended exact left-inflation identity
   `normalDerivedInflationIso`, under the canonical full and composite adjunctions.
   This fixes the unit and counit exactly, via Mathlib's `unit_conjugateEquiv` and
   `conjugateEquiv_counit`, with `Adjunction.comp` (whose `comp_unit_app` and
   `comp_counit_app` are the required composite formulas). It is not mere existence
   of an unspecified isomorphism. `normalComparison_onKInjective` is its actual
   representative equality using ObjQIso, the ordinary inclusion-normalized identity,
   and the composition identification for complexes.
3. `normalResolutionUnit_onResolution` states that the canonical `normalResolutionUnit`
   followed by the resolution identification equals `Q.map T(i)`. The existing
   `NormalBetaUnit` in `normalInflation_resolution` gives the full underlying
   `(ri)^K` unit equality with every exact-functor and complex-composition map shown.
4. `normalInflation_uniqueLift` gives `∃! b` in the homotopy category with
   `[a] ≫ b = [T(i)]`, exactly existence and uniqueness of the homotopy class.
   `I.IsKInjective`, `J.IsKInjective`, `QuasiIso i`, and `QuasiIso a` are explicit.
5. `normalInflation_transpose` states degreewise that the inverse transpose's
   underlying map is `(b.f n).val ≫ T.inclusion.app (I.X n)`.
   `normalInflation_transposeLift` states the homotopy relating its composite with
   inflated a to the original invariant inclusion followed by i. Thus this is a
   resolution representative of the specified original coefficient morphism.
6. `normalInclusionInflation` independently constructs inflation from the existing
   quotient restriction transformation and the counit inclusion. The last conjunct
   of `normalInflation_resolution` equates this arrow with the dependency's canonical
   `normalInflation`. The other conjuncts assert `NormalInflationEquation`,
   `NormalBetaUnit`, and `NormalInflationResolution`. In particular the last existing
   predicate is the explicit localized equality whose chain map is
   `Gamma_(Q×L).map b`, for EVERY resolution and EVERY homotopy lift. This supplies
   both the representative and its independence of resolutions and lifts, and the
   first predicate is exactly `inf ≫ c = RGamma_(Q×L).map eta`.
7. `normalInflation_natural` is the equivariant-map naturality equation (including
   module maps in degree zero). The unit comes from the canonical derived computation
   unit, whose naturality also supplies naturality of the resolution description.
   Beta and c retain their existing `NatIso` types on the ENTIRE unbounded categories;
   their naturality is not weakened to statements about cohomology.
8. For arbitrary `L' : ProfiniteGrp.{u}` and `h : L' →ₜ* L`,
   `normalAuxiliaryRestriction` is the actual inflate/restriction functor along
   `ContinuousMonoidHom.prodMap (ContinuousMonoidHom.id P) h`, for P=G or Q.
   `normalAuxiliaryQuotient_existsUnique` specifies the ordinary identity by equality
   of invariant inclusions, and `normalAuxiliaryQuotient` selects only that UNIQUE
   isomorphism. `normalAuxiliaryTau` derives this identity by the already recorded
   `normalSquare`, so it is the canonical comparison, not an extra hypothesis.
9. The b^G and b^Q in the c square are `normalDerivedRestriction` for the two product
   maps. It uses the dependency's existing `invariantRestriction` and exactly its
   universal `Functor.rightDerivedPullback` construction. The recorded API's
   `invariantRestriction` unnecessarily retains three small derived-category instances
   even though its conclusion is underived. `normalInvariantRestriction` supplies
   these via `HasDerivedCategory.ofIsGrothendieckAbelian` INTERNALLY, then returns the
   very same underived map. Applying `rightDerivedPullback` outside that definition
   uses the already specified larger localizations. No object universe is identified,
   no smaller derived instance escapes into the statement, and no restriction
   transformation is replaced by an arbitrary map.
10. `normalAuxiliaryComparison_square` is the displayed c-square, in Lean's
    left-to-right composition order, at EVERY `N : DerivedCategory.{u+2} ...`.
11. `normalAuxiliaryBeta_square` says that `D(U') tau`, after the canonical forgetful
    and kernel-restriction identifications, equals beta itself. The exact
    identifications are `normalAuxiliaryForgetDerived` and
    `normalAuxiliaryKernelDerived`. The kernel identity is chosen from a UNIQUE
    isomorphism with underlying map `𝟙 N.module`, not an unspecified isomorphism.
    Thus the common RGamma_K D(r) transformation is exactly the identity.
12. `normalAuxiliaryUnit_square` and `normalAuxiliaryInflation_square` give the
    actual unit and inflation squares, with every exact-descent identification
    and the ordinary quotient identity on complexes included explicitly. Combined
    with `NormalBetaUnit` and the beta square they give the underlying K-unit square.
13. `normalDerivedRestriction_onResolution` gives the invariant-inclusion-followed-
    by-invariants-of-a formula for both b transformations on fresh resolutions.
    `normalAuxiliaryTau_onResolution` gives precisely T'(a) for an arbitrary
    K-injective I and ANY quasi-isomorphic K-injective resolution a:r_hI→J.
    The normalized ordinary quotient complex map is displayed. The c square makes
    the composite b^Q,tau representative the invariant map of this same T'(a), and
    the beta square together with `openNormalActionInjectiveModels` gives the same
    map on the unchanged K-invariants. No theorem assumes r_hI K-injective or assumes
    any K-injective-preservation property for r_h.

Dependency declarations used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, underlying ring
  convention, reexported by the normal-data dependency.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`,
  `inflate`, `forgetAction`, `trivial`, `Invariants`, its normalized transpose fields.
- `Sheaf.CategoryTheory.CondensedNormalInvariantData`: `NormalComparisonCategories`,
  `NormalInvariantFamily`, `NormalSystem`, `NormalQuotient`, `NormalDerivedComparison`,
  `normalProduct`, `normalQuotient`, `normalKernel`, `normalProjection`,
  `normalKernelInclusion`, `normalComparison`, `normalDerivedInflationIso`,
  `normalBeta`, `normalResolutionUnit`, `normalInflation`, `normalSquare`, and all
  three existing resolution predicates. No private copies of these notions are used.
- `Sheaf.CategoryTheory.OpenNormalActionInjectiveModels`:
  `openNormalActionInjectiveModels`, `openNormalKernelPreserves`, and the quotient/
  invariant K-injective model interfaces.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`, and its exported
  `Sheaf.CategoryTheory.CondensedDerivedInvariants`: `invariantRestriction`,
  `groupMap`, the canonical derived restriction calculus. Only the underived
  inclusion is used directly, for the universe reason explained above.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: the recorded
  total-derived convention; on these Grothendieck categories the existing
  `Functor.rightDerivedFunctor`, computation units and ObjQIso are the normal-data
  dependency's chosen K-injective model, so no second derivation is chosen.
- Proof imports: `Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization`
  (`derivedCompositionAdjunctionNormalization`);
  `Sheaf.CategoryTheory.CondensedRestrictionMateNormalization` (`groupMap_mate` and
  its resolution formula); Mathlib `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Adjunction.comp`, `conjugateIsoEquiv`; upstream `Functor.rightDerivedPullback`,
  `Adjunction.mapHomologicalComplex`, `mapDerivedCategoryRightDerivedAdjunction`.
  `HasDerivedCategory.ofIsGrothendieckAbelian` supplies the unused underived helper
  certificates. All signatures and relevant docstrings were opened.

Edge cases checked before/during writing: K=G (trivial quotient), K the trivial open
normal subgroup when G is finite/discrete, G or L trivial, h the identity, h from a
trivial group, h with kernel or nondense image, zero module, empty profinite test
object, arbitrary negative complex degrees, and resolutions with different models.
All product maps and quotients are actual ones. No condition of injectivity,
surjectivity, openness or finiteness on h is used. Homotopy-class uniqueness uses only
the target's K-injectivity; exact restriction is never claimed to preserve it.
The empty test object is already admitted by `Invariants`/`FixedAll`; no nonempty
section hypothesis appears. Nontrivial arbitrary condensed rings remain allowed.

Searches actually run:

- msearch.py leanfinder: "normalized inflation derived invariants normal subgroup
  resolution auxiliary group naturality" — 8 hits on abstract group cohomology and
  group homology, including `groupCohomology.infNatTrans(_app)` and H1InfRes. None
  states internal condensed unbounded resolution/auxiliary-group compatibility.
- msearch.py loogle: "groupCohomology.infNatTrans, CategoryTheory.conjugateIsoEquiv"
  — 0 hits for the joint query.
- msearch.py grep: "infNatTrans|normalComparison|normalInflation" in
  Mathlib/RepresentationTheory — 3 group-(co)homology hits, no matching theorem.
- msearch.py leansearch: "derived inflation normal subgroup K-injective resolution
  invariant naturality" — 8 hits on ordinary injective-resolution naturality,
  none on this internal-action assertion.
- rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  the normalized comparison/inflation and proposed auxiliary names; also searched
  the exact node id in `lean/WeilConjectures`. Found the recorded normal-data module
  and downstream `CondensedNormalSubgroupComparison` predicates. That downstream
  theorem uses this item in its proof and is not imported (which would close a
  proof-import cycle); its scalar-change predicates need a NormalScalars family,
  so they are not the pure auxiliary-group maps constructed here. No existing
  theorem states the current resolution/naturality item.

Validation: the final complete module passed scompile.py in both sandbox and canonical
library contexts, without errors or warnings, in 35.3 s and 29.6 s respectively.
A transient 60-second timeout was investigated with Lean profiling: the final
private-module interface linter dominated runtime. Direct public imports of the
actual adjunction/mate/restriction definitions used in public statements were added;
proof-only imports remain private. The temporary profiler option was removed.
The initial 101-character style warning was fixed. deliver2.py preflight is run
before delivery. No theorem is proved in
this stage. No STATEMENT-DISPUTED issue or source correction was found.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
