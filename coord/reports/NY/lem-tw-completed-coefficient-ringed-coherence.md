## Worker report

The module `Sheaf.Paper.CompletedCoefficientRingedCoherence` states the entire node in
four named theorems, with `sorry` proofs: `completedRingMap_existsUnique`,
`completedRingMap_comp`, `completedRingMap_equal_composites`, and
`completedRingMap_slice`, all in namespace `WeilConjectures`. The other declarations
supply the canonical constructions and their normalizations. The node is changed
only in `lean`; no new node, dependency-record repair, or statement correction is needed.

The previous dispatch result confused the Q13 stage-1 merge with a stage-2 statement.
The live node has a reviewed split from Q13 but has no `lean` record. Its stage-2
sandbox was empty. This delivery supplies its first Lean statement, preserving the
reviewed statement and proof plan. There is no repair note or return entry for this item.

Hypotheses and objects:

* The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The recorded
  `Padic.coefficientExtensionRing l E (n + 1)` uses the valuation ring and the
  uniformizer already chosen by `def-weil-l-adic-coefficient-extension`.
* Schemes have universe `t`, independently of `u`. Their sites are the existing
  `Scheme.ProEt` and `ProEt.topology`, with objects in `Type (t+1)` and morphisms
  in `Type t`. Coefficient rings are canonically lifted to `max u (t+1)`.
  `HasColimitsOfSize` is obtained by Mathlib's universe-shrink theorem, inside
  the inverse-image abbreviation; it is not a hypothesis on the statement.
* `integralCoefficientCommRingSheaf l E W n` is C_(n+1), and
  `completedIntegralCommRingSheafUnrestricted l E W` is B_W. Its recorded
  `completedIntegralCommRingProjectionUnrestricted` is pi_(n+1). These are
  the existing constructions, with no new completion or coefficient tower.
  The unrestricted version is necessary: this node assumes no global finite-field
  datum or condition l != p, unlike the ambient convention of the completion node.
* `completedRingPull` and `completedRingAdj` abbreviate the same Mathlib
  Kan-extension/sheafification constructions used by `proEtaleSheafInverseImage`
  and `proEtaleSheafAdjunction`, at the universe containing both inputs. The recorded
  abbreviations have value-category Hom universe t+1, so they cannot themselves
  take `CommRingCat.{max u (t+1)}` for independent u. No alternative inverse-image
  construction or extra universe equality is introduced.
* `completedRingConstantMap` is the adjunct, through that very adjunction, of the
  published `coefficientProEtaleDirectRingMap`. That existing map extends the map
  sending a coefficient to the same constant section. This reuses the independent
  coefficient-universe interface of the inverse-image node rather than copying rho.

Clause-by-clause correspondence:

1. The structural map c_g and its characterization are
   `completedRingMap_existsUnique`: it quantifies over precisely a ring-sheaf map
   g^-1 B_W -> B_T and asserts every displayed finite-projection equation.
   `completedRingMap` chooses its unique witness. Its data are determined by all
   projections, not selected from an unconstrained existence statement.
2. `completedRingComp h k` is alpha_(h,k). Its definition is the adjunction mate of
   `MorphismProperty.Over.pullbackComp` through
   `Functor.sheafPushforwardContinuousComp'`, hence uses the geometric compositor.
   The first conjunct of `completedRingMap_comp` is exactly c_(kh) =
   alpha_B ; h^-1(c_k) ; c_h in Lean's left-to-right composition convention.
   The second conjunct is the node's equation at every positive finite level.
3. `completedRingMap_equal_composites h k h' k' e` permits different intermediate
   schemes and an arbitrary equality `e : h ≫ k = h' ≫ k'`. It compares the two
   iterated coefficient maps by alpha_(h,k)^-1, transport across e, and alpha_(h',k').
   Each compositor is the geometric mate, so this is the specified comparison.
   Applying a projection to this equality gives equality at that finite level;
   repeated use of the composition assertion covers any finite iterated composite.
4. The slice is not a separately invented restriction. `completedRingRestriction U`
   is Mathlib `(ProEt.topology W).overPullback _ U`, transported to U.left.ProEt
   along the existing `ProEt.sliceFrom W U`. `ProEt.sliceDense W U` supplies the
   required continuity. Thus it is precisely the restriction of
   `def-pur-localized-ringed-site` under the dependency's canonical slice equivalence.
5. In `completedRingMap_slice`, `aU n` and `aV n` identify the restricted finite
   coefficients with the coefficients on U and V. The two `toSheafify` equations
   require their components to send every constant section to itself. Thus these
   are the identity-on-constants comparisons, not arbitrary ring isomorphisms.
   `eU` and `eV` identify the completed rings, and their two equations with pi_n
   explicitly make those identifications compatible with every finite projection.
6. `((proEtaleBaseChange g).obj U)` is V, and `completedRingSliceArrow g U` is v.
   As in the inverse-image dependency, the chosen product is U x_W T rather than
   T x_W U; the canonical symmetry identifies them. The arrow v is the actual first
   projection to U. `completedRingSlicePointIso g U H` is the actual pasting
   isomorphism H x_U (U x_W T) -> H x_W T, over T, from Mathlib's
   `pullbackRightPullbackFstIso`, with its structural-map equality checked.
7. The quantified `beta` is fixed on EVERY ring sheaf F and EVERY test object H:
   its component is F applied contravariantly to that geometric pasting isomorphism.
   Consequently it compares the actual localized site functor for g with that for v.
   The quantified `lambda` has type j_U^-1 ; v^-1 ≅ g^-1 ; j_V^-1, and its next
   equation specifies every component by the unit of g, beta, and the counit of v.
   This fixes the canonical inverse-image mate, not a mere existence of an iso.
8. The next equation is exactly the equality of localized structural maps after the
   completed identifications: lambda_B ; j_V^-1(c_g) ; eV = v^-1(eU) ; c_v.
   The final quantified equation is this localized structural map at every finite
   projection, with the actual finite constant coefficient map for v.
9. There is no flatness or invertibility hypothesis on c_g, no Noetherian hypothesis,
   no dimension bound, no finite-type hypothesis, and no mono/open hypothesis on U.
   Weak etaleness of U -> W is exactly its membership in W.ProEt.

Declarations read and reused:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the existing coefficient
  integers, chosen uniformizer, quotient rings, and reduction maps.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, reexporting
  `Sheaf.Paper.CompletedIntegralCoefficients`: `integralCoefficientCommRingSheaf`,
  `completedIntegralCommRingSheafUnrestricted`,
  `completedIntegralCommRingProjectionUnrestricted`. The commutative sheaf retains
  the recorded ring sheaf's data; forgetting commutativity recovers it.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`,
  `proEtaleConstantDirectImageMap`, `proEtaleConstantInverseImageMap`.
* `Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses`:
  `coefficientProEtaleDirectRingMap`, the existing constant-section map with
  independent coefficient and site universes, belonging to the same inverse-image node.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, reexporting
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.overPullback` and
  `Sheaf.over`, the recorded restriction to a slice.
* `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `ProEt.sliceFrom`, `ProEt.sliceEquiv`, `ProEt.sliceDense`,
  `ProEt.weaklyEtale_localization`. These identify the exact sites and constants.
* `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π` (already used by
  the recorded completion), and `hasColimitsOfSizeShrink` for the coefficient-sized
  inverse image.
* Proof imports: `Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`,
  `Scheme.proEtaleCoefficientInverseImageMap_comp`; and
  `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`,
  `SheafOfModules.localize_ringed_site_morphism_general`. Their signatures and
  proof docstrings were read. They express the finite coefficient calculation and
  generic ringed localization used in the node's proof plan. A proof at independent
  universes can transport the latter through the existing small-site models.

Edge cases checked against the signatures and construction:

* Empty T, W, U, or V are admitted. The actual constant sheafification is used,
  including its terminal ring of sections over an empty object; no nonempty
  constant-presheaf shortcut occurs.
* n=0 denotes exponent one, so every and only positive quotient level occurs.
  The zero-exponent quotient is not inadvertently included.
* Identity maps and either identity factor are admitted in composition and in the
  equal-composites assertion; the comparison still comes from the actual geometric
  adjunction, including the chosen pullbacks along identity maps.
* U is any pro-etale site object, including non-monomorphisms. No open-immersion
  restriction has been substituted for weakly-etale slice localization.
* The structural map is not postulated to be invertible or flat. Isomorphisms in
  the slice theorem are geometric/restriction identifications, not assumptions on c_g.
* Arbitrarily large finite coefficient extensions relative to the scheme universe
  are covered by independent t and u and the canonical ULift. No equality of site
  object and morphism universes is imposed.

Searches actually run:

* `msearch.py ... leanfinder`, query "Completed pro-etale coefficient ring maps
  compose and restrict to slice sites compatibly with finite projections": eight
  hits, including RingHom.Etale.stableUnderComposition,
  StandardEtalePair.HasMap.map, and AdicCompletion.transitionMap_comp_eval.
  These concern algebraic etale maps or module adic completions, not the node.
* `msearch.py ... loogle`, query
  `CategoryTheory.Sheaf.over, CategoryTheory.Limits.limit.post`: zero hits.
* `msearch.py ... grep`, query `overPullback|limit.post` in CategoryTheory/Sites:
  fourteen hits, including the slice restriction in Over.lean and uses in SheafHom.
  These give the existing restriction construction, not this coherence statement.
* `msearch.py ... leansearch`, query "Inverse limit of constant ring sheaves:
  structural inverse image maps respect composition and slice restriction": eight
  hits, including constantCommuteCompose, PresheafOfModules.limitPresheafOfModules,
  and SheafOfModules.conjugateEquiv_pullbackComp_inv. None states the completed-ring
  composition plus normalized weakly-etale slice assertion.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, by the item id: no existing
  declaration carrying this node. Searches for completed coefficient comparison and
  completed ringed coherence found `ProfiniteCoefficientInverseImage` and
  `OrdinaryCompletedIntegralPullback`. Their source declarations were read.
  The former has a general finite-tower composition clause but no slice clause and
  uses a separately formed CommRingCat limit. The latter has the direct-image
  adjunct of a completed coefficient map, but no composition/slice assertion and is
  downstream of this item through the stratified-model route. It cannot be imported
  here. Neither is an exact existing match for this node.
* `rg` for the new full declaration names in the project and DAG found no collision.
  Unrelated completed matching-ring maps occur in a different namespace and concern
  punctured-completion gluing, not pro-etale coefficient sheaves.

Validation: `scompile.py NY lem-tw-completed-coefficient-ringed-coherence` compiled
both the sandbox module and its library-path placement cleanly with the required
60-second per-file limit. The final module uses module mode, public statement
imports, explicit universes, and `autoImplicit false`; no diagnostic commands,
local notations, or private definitions remain. Definitions have real construction
data. The only postponed proofs are the four named theorems of this node, each
with its source and proof plan in its docstring. No statement dispute was found.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
