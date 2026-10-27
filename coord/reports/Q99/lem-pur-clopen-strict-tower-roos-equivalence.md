## Worker report

Module: `Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence`.
Namespace: `AlgebraicGeometry.Scheme.ProEt.ClopenRoos`.
The node is stated jointly by `strict_tower_equivalence`, `strict_roos_comparison`,
`derived_products`, `derived_triangle_descent`, and `empty_partition`. All postponed
proofs are `sorry`, with source and stepwise proof docstrings. Definitions contain
real constructions and no postponed data. The original node is unchanged except
for its `lean` record. No new or dependency nodes are necessary.

Hypotheses, objects, and clauses:

- `X : Scheme.{t}`, `I : Type w`, `[Finite I]`, `Y : I → Scheme.{t}` and
  `j : ∀ i, Y i ⟶ X` give exactly the scheme and finite family. The two immersion
  instances, `hdisjoint : Pairwise ...` on image ranges, and `hcover : ∀ x, ∃ i, ...`
  give the open/closed, disjoint and covering assumptions. No component is assumed
  nonempty. The ring is `R : Sheaf (topology X) RingCat.{u}` with sectionwise
  commutativity `hcomm`, following the module-gluing dependency's exact interface.
- `Modules` is only the recorded `ringedSiteModules` abbreviation; `restrictedRing`
  is the recorded `clopenRingRestriction`. The small site keeps object universe
  t+1 and morphism universe t. Section-module universe `max v (t+1)` contains the
  site, with independent ring and finite-index universes. `modulesAbelian` uses
  the existing Mathlib structure with the published small-site sheafification
  transports explicitly, avoiding any new choice of an abelian structure.
- `Towers` is `CochainComplex (ℕᵒᵖ ⥤ Modules X R) ℤ`, the dependency's strict
  Roos encoding. Equivalently its evaluated complexes form a strict tower of
  complexes: `asFunctor` supplies each level, transition and strict-map square.
  Positive natural levels are indexed by n+1, including the first level n=0.
- `strict_tower_equivalence` gives G, the unit iso η, the counit iso ε and both
  triangle identities. The forward functor is exactly `Functor.pi'` of degreewise
  `towerRestriction`, not an arbitrary equivalent functor.
- Its additive section isomorphism σ is the displayed product over component
  base changes `clopenTestPiece`. Its seven conjuncts specify scalar actions,
  section restrictions, every tower morphism (hence transitions), differentials,
  strict maps, the unit as section restriction, and the counit as component
  projection using the actual diagonal base-change identification. Thus the
  inverse's data are fixed to the module-gluing formula, including all actions.
- `roosP`, `roosU`, `roosF`, `roosχ`, `roosProj` and `roosEval` are the recorded
  strict Roos declarations, imported without replacement. Their definitions use
  the actual termwise product, towerTransitionEndomorphism, and Cone(v)[-1].
- `productComparison` is the canonical Mathlib `piComparison`, with its target
  explicitly exposed as `roosP` of the restricted tower. The first clauses of
  `strict_roos_comparison` give its invertibility, every projection equation,
  and its conjugacy with `roosU`. Being morphisms of cochain complexes, these
  comparisons commute with differentials. `gluingProductReindex` is exactly
  `Equiv.piComm`: ((a[n,i])_i)_n maps to ((a[n,i])_n)_i, fixing every coordinate.
- The natural isomorphism β compares the actual Roos functors. Its `roosχ`
  equation states the same product comparison on both biproduct summands,
  after the canonical additive biproduct comparison. This uses precisely the
  dependency's signed differential (-dy-vx,dx); naturality for every strict
  tower map is part of the natural-isomorphism type, and the recorded roosF
  maps are diagonal products of strict-map components.
- The next clauses retain `roosProj` and every `roosEval`. `boundary` is the real
  negative mapping-cone inclusion followed by shift cancellation, so in the
  specified coordinates it is z ↦ (-z,0). The final chain equation uses the
  canonical restriction/shift comparison and the shifted β. It retains this sign.
- The last conjunct of `strict_roos_comparison` universally quantifies over a
  chosen component derived localization. It applies that exact Q to β, the
  projection, every level evaluation, and the signed boundary equation. The
  resulting isomorphism is `Q.mapIso (β.app C)`, with all map identities retained.
  Shifts are transported by Q's canonical shift comparison when reading these
  identities in the derived category. There is no choice of an abstract cone.
- `restriction_exact` supplies the canonical open-restriction exactness needed
  by `Functor.mapDerivedCategory`. Its two instance projections contain real
  data extracted from that named theorem; no extra exactness assumption is
  imposed on users. `derivedRestriction` is Mathlib's exact-functor construction.
- `derived_products` states that the image of the actual termwise product cone
  under Q is a limit cone on X and on each component. This keeps every actual
  projection and does not assume products in D in order to assert existence.
- `derived_triangle_descent` compares the canonical derived products by α with
  α.hom equal to `piComparison`. It states the iff for every specified first
  arrow c and connecting arrow δ, using the recorded `IsDerivedLimitTriangle`.
  On components c is restriction(c) followed by α; δ is α inverse, then
  restriction(δ), then the canonical shift comparison. The middle map is the
  recorded transition endomorphism. Neither the first nor the last arrow is
  discarded in an object-only derived-limit assertion.
- `empty_partition` includes `IsEmpty X`, equivalences of modules, strict towers
  and derived categories with `Discrete PUnit`, and distinguishedness of every
  triangle. Empty components, zero coefficients, singleton covers, two-component
  covers, identity/zero transitions, arbitrary cochain degrees and zero complexes
  are admitted throughout; no nonzero, Mittag-Leffler, boundedness or resolution
  assumption is present. The chosen `HasDerivedCategory.{d}` instances express
  only the node's chosen-localization universe convention.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms.
- Mathlib.AlgebraicGeometry.OpenImmersion: `AlgebraicGeometry.IsOpenImmersion`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.Sites.Proetale: `Scheme.ProEt`, `ProEt.topology`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`.
- Mathlib.CategoryTheory.Functor.OfSequence: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`; strict towers use the same functor category ℕᵒᵖ ⥤ A.
- WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism:
  `towerTransitionEndomorphism`, reached by `roosU`.
- Sheaf.CategoryTheory.StrictRoosModel: `roosF`, `roosP`, `roosU`, `roosχ`,
  `roosPmap`, `roosProj`, `roosEval` (their full signatures and source were read).
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit:
  `IsDerivedLimitTriangle`, including its specified first/last arrows.
- Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing:
  `clopenRingRestriction`, `clopenModuleRestriction`, additivity,
  `clopenTestPiece`, `clopenTestInclusion`, `clopenDiagonal`, and the theorem
  `clopen_ringed_module_gluing` supplying the section normalizations.
- Proof imports: Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
  (`countableProducts_exact`),
  WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
  (`derivedCategory_termwiseProduct_isLimit`), and Mathlib's exact-functor,
  product, and pretriangulated APIs (including finite distinguished products).
  `lem-pur-clopen-unbounded-derived-localization` has no published Lean record;
  its proof import is therefore unavailable. This item uses the canonical
  `mapDerivedCategory` directly, and records the needed triangle detection
  assertion itself as its node requires; it needs no new notion from that proof
  dependency to type its own statement.

Sources read: Stacks derived.tex, definition-derived-limit (08TC), lemma-products
(07KC), and the dependency source modules; the current blueprint's
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md was also read
for the ultimate source assertion. Cone and shift conventions were checked in
Mathlib MappingCone, MappingCocone, and StrictRoosModel, including the negative sign.

Searches (raw results retained in searches.jsonl): LeanFinder query "Restriction
to a finite clopen partition gives an equivalence of strict towers of module
complexes preserving products and the Roos mapping fibre with its projection and
signed connecting map" returned eight unrelated results. Loogle query
`"mappingCone", "mapHomologicalComplex"` found the generic mapping-cone transport
API but no finite-clopen/tower result. Mathlib grep
`(clopen|disjoint).*(roos|tower)|roos.*(restrict|equivalence)` found four unrelated
linear-disjointness files. LeanSearch "strict towers Roos mapping cone restriction
finite clopen cover" found open-cover and clopen-set constructions, no exact match.
Direct rg of WeilConjectures and Sheaf found OpenExchangeRoosRestriction and
ClopenRoosIntegralDescent (constant/completed integral coefficient specializations,
not arbitrary ring sheaves or this whole statement), and cofinal/arithmetic tower
comparisons. The exact blueprint-id grep in WeilConjectures found no declaration.
The generic StrictRoosAdditiveComparison is only a proof ingredient, not an exact
existing declaration of the finite-clopen statement; no notion is copied here.

## Second reading by Q99

The dispatcher explicitly forbids starting other agents and assigns this worker
self-delivery, so this section records a separate self-review pass, not an
independent agent review. The maintainer's independent review remains required.
I reopened the complete node and the module. Matched the finite cover binders,
all seven gluing coordinate equations, both unit/counit equations, product
projections and conjugacy, the two-summand formula, strict-map naturality,
projection/evaluation/boundary identities and their actual localized images,
termwise-derived product limit cones, the specified-triangle iff with unchanged
first/connecting maps, and the empty partition. Fixed missing explicit localization
clauses and a malformed universe expression during development. Replaced an
unavailable product-type instance in an unnecessary additional G-product clause
with the actual sectionwise coordinate interchange already required by the node.
The module/sheaf universe adapters are transparent and preserve the native site's
unequal object and morphism universes. No statement correction or disputed claim.
