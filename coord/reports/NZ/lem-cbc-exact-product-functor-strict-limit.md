## Worker report

Repair of the returned immutable delivery c6f8b824006a. The retained packet passed
`deliver2.py NZ lem-cbc-exact-product-functor-strict-limit --no-push` first (dry-run
commit 0f419d27d1), but its unconstrained `FT` and arbitrary-arrow equations still
had the returned semantic defects. Those clauses have been replaced, rather than
re-pushed unchanged. The current base node has the same non-`lean` fields as the
retained node. Its now-repaired `StrictRoosComparison` dependency was read in full.

`Sheaf.Paper.ExactProductFunctorStrictLimit` states
`CategoryTheory.exactProductFunctorStrictLimit`, with one `sorry` and no other
declarations. There are no new definitions, new nodes, dependency-record changes,
or changes to the mathematical node statement.

The following matches every hypothesis and clause. In the descriptions below,
`T` abbreviates, in this report only, the actual Lean term
`(Functor.whiskeringRight ℕᵒᵖ _ _).obj F`, `TC` its
`mapHomologicalComplex (ComplexShape.up ℤ)`, and `FD` means
`F.mapDerivedCategory`. These are not additional parameters or local notation.

| Node text | Lean rendering |
| --- | --- |
| Small ringed sites and commutative ring sheaves | `C, J, R` and `D, K, S`, with sectionwise commutativity `_hR`, `_hS`; `ringedSiteModules R` and `ringedSiteModules S` are the recorded module categories. |
| Small relative to the module universe | Module and ring universes are `max uC vC r` and `max uD vD s`; sheafification and locally-bijective instances give the recorded abelian structures. Site object and arrow universes, coefficient universes, and the two derived-localization universes remain independent. |
| Countable products exact in both categories | Both `[HasExactLimitsOfShape (Discrete ℕ) ...]` binders. |
| `F` additive and exact | `[F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]`. |
| Canonical product comparison is invertible for every family | `_hphi : ∀ M, IsIso (piComparison F M)`. Mathlib defines `piComparison` as `Pi.lift (fun n ↦ F.map (Pi.π M n))`; its `piComparison_comp_π` is exactly the node's characterization. No arbitrary comparison map is assumed. |
| Termwise derived functor and termwise action on strict towers | `FD` and the actual `T.mapDerivedCategory`. All factors use `T.mapDerivedCategoryFactors`, with canonical finite-(co)limit preservation data constructed from Mathlib's `whiskeringRight_preservesLimitsOfShape` and its colimit counterpart. There is no free `FT`. |
| Total right derived inverse limits | `LA`, `LB`, their units `etaA`, `etaB`, and `_hLA`, `_hLB : IsRightDerivedFunctor ... quasiIso`. The unit uses transpose followed by the ordinary limit in complexes, as in the current Roos dependency; limits in complexes are termwise. |
| Natural isomorphism on the derived category of strict towers | `lambda : LA ⋙ FD ≅ T.mapDerivedCategory ⋙ LB`. Its domain includes every derived tower object and every derived morphism; all its components are isomorphisms by the type `≅`. |
| Termwise product and signed Roos complex | `HA`, `HB` have objects exactly `mappingCone (towerTransitionEndomorphism ...)⟦-1⟧`, through `hAobj`, `hBobj`. The equality clauses for `chiA`, `chiB` fix the shift/cone coordinates followed by `biprod.map (𝟙 _) (-𝟙 _)`. Thus they are `(x,y)=(u,-v)` in Mathlib's coordinates, with `H^(p+1)=P^(p+1) ⊞ P^p` and differential `(dx,(1-s)x-dy)`. |
| Roos functoriality and descent | The equations for `HA.map` and `HB.map` fix the product map on both signed coordinates. `thetaA : Q ⋙ LA ≅ HA ⋙ Q` and `thetaB` are natural on complexes. They identify the localized Roos functors with `LA`, `LB`; hence the same comparison descends to the derived category. |
| Normalized `theta`, including K-injective inclusion `(iota,0)` | For every K-injective tower complex with injective tower terms, `iota` is a quasi-isomorphism; its two coordinates are the compatible product inclusion and zero. `etaA.app I ≫ thetaA.hom.app I = Q.map iota`, and the analogous target equation, fix the very same `thetaA`, `thetaB` used everywhere else. Naturality supplies the normalization after every resolution `X → I`. |
| `kappa` is `phi` on both summands | `psi` is the product-complex isomorphism characterized by every projection. The two equations for `kappa X` specify its composite with each first-coordinate and second-coordinate product projection as `F.map` of that source projection. Product and biproduct uniqueness force the block-diagonal canonical map; no off-diagonal maps or arbitrary isomorphisms remain. |
| `lambda = theta_(FM)^(-1) kappa F(theta_M)` | The clause headed “This square is lambda” is that formula after the explicit exact-functor localization factors. Both routes end in `Q(HB(TC X))`. Cancelling the displayed invertible factors gives exactly the node's formula. |
| Preservation of the ordinary inverse limit | `beta I : FC(lim I) ≅ lim(TC I)` and its equations against every `limit.π` characterize the canonical limit comparison. This is a conclusion, not an added preservation hypothesis. |
| Equality with the resolution comparison | For every `q : X → I` and `r : TC I → Jt`, with `q,r` quasi-isomorphisms and `I,Jt` K-injective, `dI` and `dJ` are pinned by the two derived-limit unit equations. The equality then identifies `FD(dI)` followed by `lambda` and the derived image of `Fq` with `Q(beta I)` followed by `Q(lim r)` and `dJ`. Cancelling the image of `Fq` gives precisely the resolution formula with its inverse. `FI` is not assumed K-injective, and this clause does not assume injective terms. |
| Independence of resolutions | The preceding assertion quantifies over every pair of resolutions and identifies every resulting composite with one fixed natural `lambda`. The two unit equations uniquely determine `dI,dJ`, since the derived images of `q,r` are invertible. Thus it states independence of all choices rather than selecting a pair of resolutions. |
| First maps of the specified Roos triangles | Existential `p,p'` are chain maps fixed in every degree by the first signed-coordinate projection. Their localized maps are transported through `thetaA`, `thetaB`. The first triangle equality is exactly `p' lambda = phi FD(p)`, including localization factors. |
| Connecting maps and shift comparison | `delta,delta'` are fixed by `delta.f i ≫ shiftFunctorObjXIso.hom ≫ chi.hom = -biprod.inr`. The sign follows Mathlib's mapping-cone triangle, whose third map is induced by `-mappingCone.fst`. The connecting equality uses the actual `Q.commShiftIso` and `FD.commShiftIso`; there is no free `xi`. After transport by `theta`, it is `lambda[1] xi FD(delta) = delta' phi`. |
| Every complex and strict augmentation | `Q` is an arbitrary cochain complex; `gamma` is any family of chain maps satisfying `_hgamma` for every successor transition. This is precisely a strict map from the constant tower. |
| Canonical augmented derived maps are carried to each other | `b,b'` have signed coordinates `(gamma,0)` and `(F gamma,0)`. The final equality uses exactly `Q.map b ≫ thetaA.inv` and `Q.map b' ≫ thetaB.inv`, the canonical maps of the recorded normalized Roos comparison, with the exact-functor localization factor. It quantifies over no arbitrary induced arrows. |

Dependencies and sources read:

- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: transparent `SheafOfModules` specialization,
  including its category and abelian-instance requirements.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and
  the `CommShift` and triangulated instances: full signatures and docstrings.
- `Mathlib.CategoryTheory.Functor.OfSequence`,
  `Functor.ofOpSequence`, `NatTrans.ofOpSequence`: `ℕᵒᵖ` is the paper's positive
  indexing after the bijection `n ↦ n+1`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`,
  `CategoryTheory.Abelian.functorCategoryAbelian`; the recorded evaluation,
  levelwise mono and epi declarations in `Limits.FunctorCategory.Basic` and
  `Limits.FunctorCategory.EpiMono` were also read.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`,
  `CategoryTheory.ringedStrictTowerHomotopyLimitOfUniverses`: full generalized
  signature and proof docstring, retaining independent site and module universes.
- `Sheaf.CategoryTheory.StrictRoosComparison`,
  `CategoryTheory.strictRoosComparison`: full current signature and all eight
  proof steps, especially the fixed natural descent, unit normalization,
  every-resolution formula, augmentation and resolution-transport clauses.
- Proof imports are the recorded
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`,
  `Mathlib.Algebra.Homology.DerivedCategory.KInjective`, and
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
  The first source was obtained through `scompile.py --source`; its theorem is
  `CategoryTheory.derivedCategory_countableProducts_core`.
- Local source: Stacks `sites-cohomology.tex`, `section-derived-limits` and
  `lemma-derived-limit-is-ok` (Tags 0940/0941), including the K-injective
  representative, injective tower terms, termwise limit and short exact sequence.
  The blueprint's final paragraph and Mathlib's shifted-cone/triangle conventions
  were opened alongside the node's complete nine-step proof.

Edge cases checked: zero complexes, zero transitions, constant identity towers,
zero augmentation and arbitrary negative cochain degrees. In the zero-augmentation
case the coordinate conditions force both augmentation maps to be zero. For the
identity functor the projection characterizations force identity comparisons
(up to the stated localization factors). The false former claim with arbitrary
`p'` is excluded: `p'` now must be the first-coordinate projection, so it cannot
be independently changed to zero on a nonzero example. All degree conditions are
at `p+1` with `p : ℤ`, which covers every integer. No boundedness, preservation of
all infinite limits, injective terms in the arbitrary-resolution clause, or
K-injectivity of the image `FI` has been added.

Searches retained and refreshed with actual calls:

- `msearch.py ... leanfinder "canonical normalized Roos comparison for an exact
  product preserving functor on strict towers"`: eight hits, including
  `Limits.instIsIsoPiComparison`, `Limits.map_lift_piComparison`, exact-functor
  whiskering, and product-preservation infrastructure; no complete comparison.
- `msearch.py ... loogle "CategoryTheory.Functor.mapDerivedCategory,
  CategoryTheory.Limits.piComparison"`: zero hits.
- `msearch.py ... grep "exactProductFunctorStrictLimit|normalizedRoos|strictRoos"
  Mathlib/CategoryTheory`: zero hits.
- Direct `rg` for the declaration and node id in `WeilConjectures` and `lean/Sheaf`:
  no existing declaration of the item on the current base. Direct Mathlib source
  searches found the canonical product projection identity, mapping-cone sign,
  and postcomposition preservation declarations used above.
- The prior three logged searches in `searches.jsonl` were retained; the repair
  added the actual refreshed searches to that same log.

Validation: `scompile.py` compiled the final module as a sandbox file and at its
library path with no errors or warnings. The only postponed proof is
`CategoryTheory.exactProductFunctorStrictLimit`. The declaration docstring now
contains the complete nine-step natural-language proof, with the DAG dependencies
and the computations for signs, limits, arbitrary resolutions and augmentations.
The node's `lean.statement` is extracted directly from the final source, from the
`theorem` keyword to the terminating `:=`, preserving the signature verbatim.

## Second reading by NZ

This is a separate clause-by-clause self-check in the dispatcher session; no
independent worker is claimed. The brief prohibits starting other agents, and the
maintainer supplies the independent reading of the delivery.

I reread the unchanged node statement against the rewritten file, with the current
Roos dependency and the Mathlib cone triangle open. The original failure was
substantive: setting an arbitrary triangle map to zero already contradicted the
universal equations, and an unrelated `FT` could change the entire target functor.
The new conclusion contains the actual localized postcomposition functor and
projection-specified maps. I checked both triangle composites' domains and
codomains, including `Q.commShiftIso`, `FD.commShiftIso`, and the target tower's
localization factor. The `-biprod.inr` connecting coordinate agrees with the
inverse rotation of Mathlib's cone triangle and the change `y=-v`.

I checked the two normalization clauses against the fixed `thetaA,thetaB`: each
unit followed by theta is the localized `(iota,0)` inclusion, not a new comparison
chosen per equation. In the resolution clause, `r` starts at `FI`, both `dI,dJ`
are tied to the unit, and the image of `q` occurs on the correct side. Cancelling
its invertible derived image recovers the node's formula; universal quantification
over `q,r` makes it independent of those choices. In the last clause the first
coordinates are exactly `gamma` and `F gamma`, and both second coordinates are
zero. Consequently these are the dependency's canonical augmentation maps.

Return audit: H3 is repaired by removing free `FT`, fixing triangle and
augmentation arrows, and adding the normalized signed Roos and every-resolution
clauses. H8 is repaired by the nine-step proof docstring. H1/H11 is repaired by
this substantive self-check, with the independent maintainer review still to
follow. H2 is repaired by mechanical extraction of the final verbatim signature.
No TeX statement correction was required; only the Lean rendering was defective.
