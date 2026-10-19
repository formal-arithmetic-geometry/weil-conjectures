## Worker report

The module `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction` states
`CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestriction`, with its proof
`sorry`. There are no other postponed theorems. All construction data are explicit.
The only changed node field is `lean`; no statement correction or dependency repair is needed.

Sources read: Stacks `more-algebra.tex`, lemma-pro-isomorphism-iso-Rlim (0H9K),
including its distinct maps φ′ and φ″, and lemma-pro-isomorphism-Rlim (0H9L), whose
triangulated completion is explicitly noncanonical; `sites-cohomology.tex`,
lemma-derived-limit-is-ok (0941), including its simultaneous K-injective representatives,
injective terms, and derived-product justification. The item's entire ten-step proof
is carried in the theorem docstring.

Hypothesis and clause correspondence:

- The small site is `{C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)`.
  Module sections and coefficients live in `max uC vC r`, so this includes unequal
  object and arrow universes, as required for small pro-etale sites. The two
  sheafification instances are the existing dependency's canonical abelian-sheaf
  infrastructure for a site small relative to the section universe.
- The coefficient is `R : Sheaf J RingCat.{max uC vC r}` with `_hcomm` expressing
  sectionwise commutativity. The module category is the recorded `ringedSiteModules R`,
  definitionally Mathlib `SheafOfModules R`, with its inherited abelian structure.
- The strict tower category is exactly `ℕᵒᵖ ⥤ ringedSiteModules R`. Zero-based index
  `n` means the source's positive index `n+1`. Its ordinary unbounded derived category
  is `DerivedCategory.{w}` with the two explicit `HasDerivedCategory` instances.
- `RF`, `η`, `_hRF`, `_hη` name an arbitrary realization of the total right derived
  inverse-limit functor with its K-injective computation, precisely the first outputs
  of `ringedStrictTowerHomotopyLimitOfUniverses`. These identify the functor already
  stipulated by the node, rather than assume any new exactness of module products.
  `limitComplex` abbreviates the existing `lim.mapHomologicalComplex`.
- `index e` sends `op n` to `op (e*(n+1)-1)`. `restriction A e` is Mathlib whiskering
  by this functor, and `complexRestriction` and `derivedRestriction` are its existing
  exact-complex and exact-derived extensions. Exactness is inferred from pointwise
  limits and colimits, rather than imposed as an extra hypothesis. Its transitions
  are exactly the strict composite transitions of the original functor.
- The main conclusion supplies `ρ e he : RF ≅ derivedRestriction _ e ⋙ RF` for all
  natural numbers `e` with `he : 1 ≤ e`. Being a natural isomorphism includes both
  invertibility on every derived object and naturality for every derived morphism,
  hence also every strict square and its induced total-limit square.
- The first conjunct fixes `ρ` against the original derived-limit unit: its composite
  with `η` is localization of the ordinary `limitMap`. `limitMap` uses the actual
  degreewise `limit.pre`, so it selects exactly the indicated compatible coordinates.
  This is the canonical total derived comparison, not an existential choice of a
  morphism between triangulated vertices.
- The second conjunct writes the strict-cone unit equation for every complex `K` and
  map `a : K ⟶ (limitComplex _).obj X`. Such a map is exactly a strict cone of complexes
  into `X`, by the termwise limit universal property. The two displayed maps are
  `Q(a) ≫ η_X` and `Q(a ≫ limitMap e X) ≫ η_(r_e X)`, with only the canonical derived
  restriction factorization used to match their targets. Thus it includes cones into
  unresolved complexes and arbitrary strict cones, not just identities or zero maps.
- The third conjunct explicitly handles `e=1`: `ζ` is the cochain restriction identity,
  with its components specified by transport along the index equality; `ι` is its
  localized identity, fixed by `mapDerivedCategoryFactors`. The equation
  `ρ_1,Z ≫ RF.map (ι_Z) = 𝟙` is identity under this canonical identification. Neither
  identity is an arbitrary isomorphism: every component on complexes is prescribed.
- The fourth conjunct supplies simultaneous resolutions for every `X` and positive `e`:
  `j` is a quasi-isomorphism, `I` is K-injective with injective tower objects in every
  degree, and its exact restriction is K-injective and still resolves the restriction.
- The final conjunct applies to EVERY such `I`, so there is no dependence on one
  arbitrary representative. It records evaluated K-injectivity and explicitly asserts
  that each localized ordinary product cone is an `IsLimit` in the derived category.
  These are the source's derived products computed on simultaneous resolutions.
- `selection e I.asFunctor` is `Pi.lift` of the projections at `e*(n+1)-1`.
  `block e I.asFunctor` is `Pi.lift` of the finite sums over `k ∈ Finset.range e`,
  with summand the projection at `e*(n+1)-1+k` followed by the original functor's
  transition to `e*(n+1)-1`. These are exactly the two source product formulas,
  including the identity transition in the first summand. The square involving
  `boundary` states their telescoping identity for `1-s`.
- `boundary` transparently abbreviates existing `towerTransitionEndomorphism`;
  `model` transparently abbreviates Mathlib's actual `mappingCocone`, i.e. Cone[-1].
  The existential maps `κ`, `κe` have zero shifted coordinates and the actual limit
  projections as their source coordinates. They are quasi-isomorphisms. `c` has its
  source coordinate fixed by `selection` and its shifted coordinate fixed by `block`
  in every cochain degree. Together these two coordinates determine the entire chain
  map, including zero mixed terms, rather than merely a triangulated completion.
- `κ ≫ c = limitMap e I ≫ κe` is the strict comparison of the kernels and cone maps.
  `σ`, `σe` are fixed by `η ≫ σ.hom = Q(κ)` and its restriction, so they are the
  canonical representative identifications. The next equation identifies `ρ` with
  `Q(c)` using exactly those identifications.
- The displayed `∀ n` equation is `p_n ρ = p_(e(n+1))`, explicitly using the actual
  cocone source projections after the canonical identifications. As the statement
  gives resolutions of every complex and holds for every such resolved representative,
  and `ρ` is natural on the whole derived category, this represents the projection
  identity for all derived objects, not a bounded or strict-map special case.
- The final equation writes the Roos cone-unit identity for every `K` and every strict
  cone `a` into the resolved tower: `Q(aκ) Q(c) = Q(a α κe)`.
  No product-exactness hypothesis appears anywhere.

Dependency declarations and imports:

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules` (publicly
  imported by the recorded tower theorem): the exact general ringed-site module category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.Q` (transitive public import): ordinary unbounded localization.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitOfUniverses`: the stipulated total right
  derived functor and its K-injective computation, used as the input `RF,η`.
- Proof imports follow the recorded proof dependencies: Mathlib injective objects,
  Mathlib `CochainComplex.IsKInjective.Qh_map_bijective`, Mathlib functor-category
  abelianness; `Sheaf.Algebra.Homology.KInjectiveProductsTermwise` and
  `CochainComplex.termwise_product_isKInjective_and_isLimit`;
  `WeilConjectures.Algebra.Homology.KernelShiftedMappingCone` and
  `CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi`;
  `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective` and
  `CategoryTheory.tower_evaluation_isKInjective`;
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` and
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes`;
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` and
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
  Missing local recorded files were read through `scompile.py --source`, as instructed.
- Product constructions are exactly Mathlib `Pi.π`, `Pi.lift`, `limit.cone`, and
  `HasCountableProducts`; the existing transition differential is imported from
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`.

Edge cases checked before writing: `e=1` selects every level and each block has a single
identity-transition summand; `e=2` selects source levels 2,4,6 and its first block is
levels 2,3, so the initial omitted level is handled by ordinary cofinal limit restriction.
On a constant tower, the target map is multiplication by `e` while the source map is
selection, which is why the two cone coordinates cannot be replaced by the same map.
On towers with zero transitions only the first summand survives; on the zero tower all
constructions remain defined. Unbounded negative cochain degrees, nonexact sheaf products,
and unequal site universes are retained. `e=0` is not asserted, exactly as in the node.

Searches actually run for this item:

- `msearch.py ... leanfinder`: "Restriction of a strict inverse tower to an arithmetic
  subsequence gives a natural isomorphism on total right derived inverse limits with
  the finite block Roos cone map" returned eight hits, including complex-shape
  restrictions, `LightProfinite.isoMapCone`, and `InverseSystem.globalEquiv_naturality`;
  none states the present derived ringed-site restriction and cone-unit normalization.
- `msearch.py ... loogle`: `CategoryTheory.Functor.Initial, CategoryTheory.Limits.limit`
  returned `Functor.Initial.limitIso`, `limit_pre_isIso`, and the two projection lemmas.
  These concern ordinary limits; they do not state the derived Roos comparison.
- `msearch.py ... leansearch`: "The homotopy inverse limit is invariant under restriction
  to a cofinal arithmetic subsequence" returned eight inverse-system equivalence hits,
  with no exact derived ringed-site match.
- `msearch.py ... grep`: `(arithmetic.*(tower|Tower)|[Rr]oos|homotopyLimit)` in Mathlib
  `CategoryTheory` returned zero hits.
- `rg` of the named upstream source directories and `lean/Sheaf/CategoryTheory` for
  arithmetic towers, Roos, and homotopy limits found existing transition, mapping-cocone,
  product, and noncanonical triangulated homotopy-limit infrastructure, all reused.
  The full-tree upstream/project search for the node id and arithmetic tower names
  found no exact declaration. `dag/lean_names_upstream.json` has no matching node binding.
  The generic existing integral-operations Roos definition was inspected; its underlying
  construction is Mathlib `mappingCocone`, which `model` abbreviates transparently rather
  than constructing a second complex.

Validation: prescribed `scompile.py NE lem-sp-strict-tower-arithmetic-restriction <file>`
compiled both the sandbox copy and its intended library module cleanly (8.1 s and 9.1 s
on the final full-import version). Initial elaboration issues were repaired: restriction
is a transparent abbreviation so its exactness instances resolve, the correct ordinary
limit lemma is `limit.map_pre`, the family of natural isomorphisms is parenthesized,
and K-injectivity of inferred complex types uses its fully qualified predicate.
No warnings remain. The only `sorry` is the main theorem.

## Second reading by NE

I reread the node, source passages, and final module clause by clause after compilation.
This is a second pass by the dispatched worker; the independent reading is the maintainer's
delivery review, and no other agent was started, in accordance with the dispatch brief.

The index shift was rechecked: the code's `e*(n+1)-1+k`, `k<e`, is exactly source level
`e*(n+1)+k`, with the final level `e*(n+2)-1`. The first block starts at level `e`, and
`e=1` retains the entire tower. I specifically checked that `block` uses the composite
transition from that summand back to the selected level, not just an adjacent transition.
Both products have the same selected family, so the telescoping square has matching types.

I checked that the theorem binds the ring, commutativity, small-site structure, module
universe, and both derived localizations; it does not restrict object and morphism
universes to be equal. `RF,η` use exactly the recorded dependency's interface. The
natural isomorphism is on the whole derived tower category, and the proof's representative
argument is stated for every K-injective tower with injective terms. Both localized
product cones are asserted to be derived products. The unshifted and shifted coordinate
equations for `c` prescribe the full cone map; specifying only its unshifted projection
would have lost information, and that was avoided. The kernel-to-cone maps have the
zero shifted coordinate, so the supplied strict-cone units retain their normalization.

The identity case has its own canonical cochain and derived identifications, with each
cochain component explicitly specified; the equation is not an assertion that differently
typed objects are definitionally equal. The two unit clauses cover both arbitrary strict
cones before resolution and the resolved Roos representatives. No hypothesis of countable
product exactness, boundedness, or a chosen trivial cone was introduced. No mathematical
statement change was found necessary. The initial compiler issues listed above were
elaboration/interface repairs only. No new nodes or dependency modules are delivered.
