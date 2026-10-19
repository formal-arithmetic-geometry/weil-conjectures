## Worker report

This delivery states `lem-cbc-strict-tower-proper-open-calculus` in
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`. No target statement or natural-language
item statement is changed. The complete interface is recorded in the item and new nodes' `lean.declarations`:
the principal theorem contains the three proper/open coherence equations; the accompanying
constructions and theorems give the other clauses. All newly stated theorem proofs are `sorry`.
Definitions contain actual functor, mate, localization, coefficient-map and fibre-product data.

The item is matched clause by clause as follows. Names in this table are in
`AlgebraicGeometry.ProEtale.StrictTower` unless qualified otherwise.

| Natural-language hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary commutative B, including infinite B | `B : Type (u + 1)` and `[CommRing B]`; no `Finite B` on the tower operations, beta, alpha, gamma, or coherence laws. |
| Every scheme and its actual small pro-etale site | `X : Scheme.{u}`, `Scheme.ProEt.topology X`; object universe u+1 and arrow universe u are retained. |
| Constant ring sheaf, module sheaves | `coefficients B X` uses `constantSheaf ... CommRingCat`; `Modules B X` is `Scheme.proEtaleRingModules` over that sheaf. |
| Strict inverse systems indexed by positive integers | `Towers B X := ℕᵒᵖ ⥤ Modules B X`; index n represents level n+1. This reindexes the recorded inverse-system convention, without losing level 1. |
| Ordinary unbounded derived category of towers | `Derived B X := DerivedCategory (Towers B X)` and `HasDerivedCategory.standard`; this is not a functor category of separate derived objects. |
| Diagram-site interpretation | Import `Sheaf.CategoryTheory.DiagramSiteRealization`, declaration `CategoryTheory.exists_diagramSite_realization`; the module-sheaf skeleton can be enlarged without equating the site's two universes. |
| Canonical constant-ring identification | `constantRingIso`, formed by inverting `Scheme.proEtaleConstantInverseImageMap`; `constantRing_isIso` and `constantRingIso_comp` state its properties for arbitrary B. |
| Termwise exact inverse image and total right derived termwise direct image | `modulePullback`, `moduleDirectImage`, `towerPullback`, `towerDirectImage`, `G`, `R`; `towers_hasKInjectiveResolutions`, `towerPullback_exact`. |
| Normalized adjunction and compositors | `adj` derives the recorded tensor-unit-normalized module adjunction; `moduleRComp_existsUnique` and `moduleRId_existsUnique` fix ordinary direct images on sections. `gComp`, `rComp`, `gId`, `rId` descend these or take their conjugates. |
| Exact termwise open extension with adjunction | `moduleJ`, `moduleJAdj`, `towerJ`, `J`, `jAdj`; `openPullback_isRightAdjoint` uses localization and `moduleJ_exact`, `towerJ_exact` assert exactness. The selected left adjoint is determined up to its unit-preserving adjoint isomorphism, not by unnormalized existence of a comparison map. |
| Cartesian open square | Four explicit morphisms, `[IsOpenImmersion j]`, `[IsOpenImmersion j']`, commutativity `h`, and `hsq : IsPullback ...`. These are the fields of the recorded `OpenImmersionSquare`, with its chosen pullback isomorphism recovered by the pullback universal property. There is no condition on g. |
| Canonical beta and prescribed inverse transpose | `betaInvApp` is exactly `(jAdj ...).homEquiv.symm` of the pulled-back open unit and `squareG.inv`; `betaInv` supplies naturality; `betaInv_isIso` and `beta` give the stated orientation. |
| Beta naturality, identity, successive base changes, composition of opens | Naturality is built into `betaInv`; `beta_id`, `beta_comp`, `beta_open_comp` give equalities in the derived tower categories, with their actual compositors. |
| Finite constant evaluation | `beta_evaluation [Finite B]` compares evaluation of beta to `singleBeta`, using `evalG` and `evalJ`. |
| Arbitrary commutative proper/open square | `k,r,p,i,h`, `[IsProper r]`, `[IsProper p]`, `[IsOpenImmersion k]`, `[IsOpenImmersion i]`, `[QuasiCompact k]`, `[QuasiCompact i]`. Alpha and gamma have no cartesian or factorization premise. |
| Canonical fibre-product lift and its clopen image | `squareLift := pullback.lift k r h`; `squareLift_clopen` asserts both `IsOpenImmersion` and `IsClosedImmersion`. The projection identities are those of `pullback.lift`. |
| Projection identity on the image and zero off it | `pi` is the direct-image unit followed by the inverse canonical `openToR` comparison; `pi_components` states its restriction to s and every complementary open c. The complement is expressed by `Set.range c = (Set.range s)ᶜ`. |
| Intrinsic alpha | `alpha` is beta on the canonical fibre product, then the whiskered `pi` of `squareLift`, then the open-extension and inverse-image compositors along `pullback.lift_fst` and `pullback.lift_snd`. |
| Cartesian and refinement normalizations | `alpha_cartesian` identifies alpha with beta. In the refinement V=S and r=identity, the same definition uses exactly the section `pullback.lift k (𝟙 S) h`; `pi_components` fixes it as identity on this clopen section and zero on its complement. No additional factorization is chosen. |
| Gamma is precisely the proper-adjunction mate | `gamma := mateEquiv (adj B r) (adj B p) (alpha ...)`; Mathlib's `mateEquiv` expands to the unit-alpha-counit formula in the node. |
| A finite bounded-below etale origin at each level, with ring map B to Λ_n | `ScalarEtaleOrigin B V ((ev B V n).obj M)` records finite commutative Λ, its discrete topology, `φ : B →+* Λ`, a finite pro-etale object, the existing `EtaleOriginWitness`, and its scalar-restriction isomorphism. |
| No uniform lower bound | `gamma_isIso` assumes `∀ n, Nonempty (ScalarEtaleOrigin ...)`; each witness has its own bounded-below object. There is no common integer or bound. |
| Gamma invertible on these origins | `gamma_isIso` concludes `IsIso ((gamma ...).app M)`. |
| Evaluation is the specified normalized finite comparison, including refinements | `finiteGamma` selects the dependency's gamma together with its section/derived-unit normalizations; `finiteSource` and `finiteTarget` retain all evaluation, site, scalar and origin isomorphisms; `gamma_evaluation` equates the two specified arrows. The dependency includes the identity-left refinement case. |
| Vertical and horizontal alpha pasting | `alpha_vertical`, `alpha_horizontal` identify the intrinsically constructed outer alpha with the pasted maps before evaluation, for every proper/open square. |
| Alpha under base change | `alpha_baseChange` is the pullback cube equation with beta and `squareG`. |
| Vertical gamma law | First conjunct of `normalizedProperOpenCalculus`, with `rComp` on both sides. |
| Horizontal gamma law | Second conjunct of `normalizedProperOpenCalculus`, with `jComp`. |
| Arbitrary base-change gamma law | Third conjunct of `normalizedProperOpenCalculus`; `exchange` is the actual pullback-square mate. The four `IsPullback` premises specify the base-change cube and impose no cartesian condition on the original proper/open square. |
| Parenthesization independence | The binary laws identify each pasted comparison with the single intrinsic comparison for its outer square, using the normalized composition adjunctions. Repeated application covers all parenthesizations. |
| Identity vertical and horizontal maps | The two conjuncts of `gamma_identities`, using `rId` and `jId`. |
| Equalities before evaluation; evaluation need not be faithful | Every alpha/beta/coherence equality is a morphism equality in `Derived B X`. Evaluation is used only by `beta_evaluation`, `gamma_evaluation` and the isomorphism-detection proof plan, never as a faithfulness hypothesis. |

Dependencies read and used: the sites and ring/module definitions of
`Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`, `CategoryTheory.constantSheaf`,
`CategoryTheory.ringedSiteModules`, and `DerivedCategory`; the arbitrary identified-ring
operations and tensor-unit-normalized adjunction of
`Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
(`Scheme.proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
`proEtaleRingModuleAdjunction`, reexported by the recorded operations chain);
`Scheme.proEtaleRingCompositeCoefficients` in
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`;
`CategoryTheory.exists_diagramSite_realization` in
`Sheaf.CategoryTheory.DiagramSiteRealization`; the localized extension/restriction interfaces
`SheafOfModules.localizedModuleExactIndependent` and
`localizedModuleAdjunctionIndependent` in `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`;
`AlgebraicGeometry.OpenImmersionSquare`; Mathlib `pullback`/`pullback.lift`,
`IsProper`, `IsOpenImmersion`, `IsClosedImmersion`, `QuasiCompact`, `LocallyOfFiniteType`;
`SheafOfModules.restrictScalars`; `CategoryTheory.mateEquiv`, `mateEquiv_hcomp`,
`mateEquiv_vcomp`, composition adjunctions and conjugate comparisons.

Finite normalization uses `ProEtale.EtaleOriginWitness` in `Sheaf.Paper.EtaleOriginWitness`,
`finiteCoefficientRealization` and `finiteCoefficientComparison` in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, the recorded
`Scheme.proEtaleSiteComparisonModules`, and `Etale.properOpenInterchangeCoherence` in
`Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`. The source signatures of
`ProEtale.isIso_comparisonDirectImagePlus` and
`ProEtale.openImmersionLowerShriekComparison_coherence` were read: the scalar/site transports
retain their same section, unit and open-adjunction normalization rather than importing
conflicting legacy pro-etale modules. The recorded `completedDirectImageRlimIso` concerns
completed coefficients; the present G/R/evaluation specializations use arbitrary constant
B and do not claim to instantiate that completed-coefficient theorem directly.

Edge cases checked: B infinite (e.g. integers); the zero ring and zero module; empty schemes
and empty opens; n=0 representing positive level 1; identity base changes; identity proper
or open arrows; a non-cartesian refinement whose canonical fibre-product lift is a proper
clopen section with nonempty complement; separate bounded-below origins whose lower bounds
tend to minus infinity; a non-flat scalar map B to a finite quotient. No finiteness of B,
flatness of the coefficient map, uniform lower bound, chosen factorization, cartesian
proper/open square, or faithfulness of derived evaluation is assumed.

Searches made (also retained verbatim in the new nodes' `mathlib_searches`): LeanFinder on
strict inverse systems of pro-etale sheaves with coherent proper/open comparisons returned
light-profinite transition maps, condensed realization and ordinary scheme-module pullback
APIs, none the requested statement. LeanSearch on strict inverse systems with exact open
extension and derived direct image returned `Scheme.Modules.restrictAdjunction` and generic
sheaf-module limits/pushforward comparisons; it does not give the tower calculus. The earlier
LeanSearch request failed with a service error; the repeated request succeeded. Loogle
`"mateEquiv"` returned the exact Mathlib mate and pasting APIs, which are reused. Grep queries
`properOpen|proper_open|strictTower|tower.*shriek` and
`strictTower|towerPullback|finiteScalarMap|ScalarEtaleOrigin` found no full Mathlib or upstream
match. Project rg found the finite etale proper/open theorem and generic ringed tower/limit
APIs, which are not the arbitrary-constant-ring normalized operations. DAG grep and
`tools/blueprint_refs.py search 'strict tower'` / `'termwise'` found the adic tower and
finite/coefficient-specific nodes, but no existing node for these normalized packages.
The upstream blueprint-id search found no full statement.

Sources checked directly: Stacks Tags [0F7B](https://stacks.math.columbia.edu/tag/0F7B),
[0F7C](https://stacks.math.columbia.edu/tag/0F7C),
[0F7D](https://stacks.math.columbia.edu/tag/0F7D),
[0F7F](https://stacks.math.columbia.edu/tag/0F7F), and
[09AE](https://stacks.math.columbia.edu/tag/09AE). The tower/pro-etale assertions are the node's
explicit refinement, as its source record says, rather than attributed verbatim to those tags.
No statement dispute or source correction was identified.

## New nodes

`def-cbc-strict-constant-tower-operations` owns
`Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: aliases of the existing constant
ring/module/tower/derived notions and actual normalized termwise G/R operations, their
adjunctions and compositors, and evaluation comparisons. The source is the first and
seventh proof steps of this item (blueprint ancestor `thm-cbc-complete-proetale`), Stacks
07A7, 0F7B and the diagram-site realization. Existing adic/completed tower interfaces
assume coefficient data absent here; this package instead keeps arbitrary constant B.
The three kinds of searches above found component APIs, all reused, but no such package.

`def-cbc-strict-tower-open-extension` owns
`Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: the localized-site left adjoint, exact
termwise extension, derived adjunction, open compositors and evaluation comparison over
arbitrary constant B. Its source is item proof steps 1--2 and Stacks 03DI, 03DJ, 09AE.
Finite fixed-ring open extension exists and is reused in finite transport, but supplies
neither an arbitrary-B functor nor the strict-tower operations. Searches found no package
with these objects and normalization.

`def-cbc-finite-constant-coefficient-transport` owns
`Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`: actual restriction along the
constant-section map B to the finite continuous-function coefficient sheaf, finite sheaf
realization, and the normalized site/scalar G/J/R comparisons. `ScalarEtaleOrigin` combines
the existing explicit etale-origin witness with this actual restriction of scalars; it
retains the witness's isomorphism. Source: item proof steps 7--8, Stacks 03DA, 099R, 09AF.
The existing finite-coefficient and etale-origin definitions are used, not copied. The
missing notion is their specified scalar/site transport to arbitrary B. Searches found
only the component constructions.

### def-cbc-strict-tower-proper-open-arrows

`Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` contains the actual unit-normalized
cartesian beta, fibre-product lift, canonical clopen projection, intrinsic alpha,
proper-adjunction mate gamma and pullback/direct-image exchange arrow. This definition node owns the missing normalized arrow constructions independently
of the main item's coherence assertions;
their normalization and finite beta evaluation are its characterizing properties.
Its sources and hypotheses are exactly those already mapped in the worker table.
The same Mathlib/upstream/DAG searches apply: grep for `squareLift|betaInvApp|openToR|
StrictTower.*gamma` in Mathlib returned no hit, and blueprint search `clopen comparison`
returned no node. The finite etale comparison remains reused, without redefining it.
No mathematical statement was changed by the split.

## Dependency modules

`lem-cbc-proetale-extension-zero-base-change` is repaired in
`Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`, with `singleBeta` as its principal
declaration. Its previously recorded upstream module imports the legacy pro-etale API,
which conflicts with the finite-coefficient framework needed here. Its current server
source was read using `scompile.py --source`: it defines the inverse open-base-change
comparison by conjugation and then descends it degreewise. The repair states exactly the
same unbounded finite constant-ring comparison in the intrinsic module coordinates, by
its inverse open-unit transpose. These are the node's constant-coefficient categories;
no complex or cartesian case is excluded.

The current `lem-weil-pbc-comparison-pullback` interface is reused from
`Sheaf.Paper.CompactSupportComparisonPullbackCoherence`. The finite transport uses
`cbcEtaleComparisonAdjunction`, `cbcProEtaleComparisonAdjunction`, and
`cbcComparisonCoefficientPullbackIso`, whose definitions are the canonical Kan-extension
adjunctions and the mate of the sectionwise fibre-product restriction comparison.
This is the published Q24 repair of the legacy import conflict. The stale sandbox copy
of `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` and its dependency node override
were removed. The original node is cited in the item's added statement dependencies;
its current Lean record is preserved.

Repairs made while completing the earlier sandbox: supplied the Grothendieck-abelian
module instance from the recorded independent-universe resolution theorem, specializing
its site-object, site-arrow and coefficient universes explicitly to u+1, u, u+1. This
supplies enough injectives without adding a hypothesis to any comparison. Imported the
existing filtered-colimit preservation of `CommRingCat` to `RingCat`; a remaining generic
instance search timed out. The unit-preserving sheafification-compatibility property is
therefore stated explicitly as `constantRingForget_preservesSheafification`, with its
plus-construction proof plan and a matching clause in its owning definition node. The
coefficient map still uses the canonical `constantCommuteCompose` construction. Corrected the open transport's direction: `hOpenInv` is
the specified inverse mate and `hOpen` is its inverse, with invertibility stated separately.
Qualified the functor-whiskering API. Removed the earlier boilerplate imports and kept
proof-only imports private where possible. Corrected the node signature records to start
at their declaration keywords and made every new node's dependency citation explicit.

Completion review of the existing attempt (2026-10-16): re-read the current item,
its statement dependencies, the finite-origin and finite-interchange interfaces, and
the current comparison-pullback replacement. Repeated LeanFinder with query
“strict inverse systems of pro-etale module sheaves normalized proper open base change
comparisons” (only affine transition-limit/normalization results), Loogle `"mateEquiv"`
(the existing mate and pasting APIs), and Mathlib grep
`properOpen|proper_open|strictTower|tower.*shriek` (no hits). Repeated upstream/project
rg and DAG blueprint search; there is no exact full calculus statement. The current
comparison-pullback definitions are reused rather than restated. Directly checked the
source of the old upstream finite open-base-change declaration with `scompile.py --source`:
it is the inverse adjunction conjugate and its degreewise derived descent, as matched
by the normalized `singleBeta` repair. Stacks 0F7B, 0F7C, 0F7D, 0F7F and 09AE were
read from their published tag pages because the local literature checkout lacks the
TeX files. The main statement and target statements remain unchanged.

Compiler repair: profiling isolated a kernel timeout in the nested existential
selection defining `finiteGamma`; all other main-file declarations elaborated
within the reduced diagnostic heartbeat limit. `secondWitness` shares that generic
selection behind a small typed definition. Its body is the identical
`h.choose_spec.choose`, so it selects exactly the same globally normalized finite
comparison and adds no premise, theorem or arbitrary unnormalized map. The
principal theorem and every mathematical signature are unchanged.

## Second reading by N4

I read the node statement clause by clause against
`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` and its five sibling modules.
The object and hypothesis checks are:

- An arbitrary commutative ring is `B : Type (u + 1)` with `[CommRing B]`; no finiteness,
  flatness, characteristic, or uniform bound is added.
- For each `Scheme.{u}`, `coefficients`, `Modules`, `Towers`, and `Derived` in
  `StrictConstantTowerOperations` render the constant small pro-etale ring sheaf, module
  category, strict inverse towers, and ordinary unbounded derived category. `n : ℕ` is
  explicitly the positive level `n+1`.
- `G`, `R`, `J`, and their adjunctions/compositors in the operations and open-extension
  modules render termwise inverse image, total right-derived direct image, exact open
  extension, and the stated normalized units and compositors.
- `beta`, `beta_id`, `beta_comp`, and `beta_open_comp` render the cartesian open-square
  comparison, its unit transpose, identity and successive-base-change laws, and open
  composition. Their hypotheses are the two open immersions and the displayed pullback
  equalities/pullback structures.
- `squareLift`, `squareLift_clopen`, `pi`, and `alpha` render the fibre-product lift, its
  open-and-closed image, the identity/zero clopen projection, and the intrinsic alpha for
  an arbitrary commutative proper/open square. The square has proper verticals and
  quasi-compact open horizontals; no cartesian or identity-left premise is introduced.
- `gamma` is exactly the proper-adjunction mate of `alpha`; `alpha_cartesian` identifies it
  with `beta` in the cartesian case. `gamma_identities` supplies the two identity
  normalizations.
- `ScalarEtaleOrigin`, `finiteSource`, `finiteTarget`, `finiteGamma`, and
  `gamma_evaluation` render finite coefficient maps, independent bounded-below etale
  origins, and the specified normalized finite evaluation comparison. `gamma_isIso` has
  precisely the pointwise `Nonempty` origin hypothesis and no common lower bound.
- `alpha_vertical`, `alpha_horizontal`, `alpha_baseChange`, and
  `normalizedProperOpenCalculus` render the intrinsic alpha pasting/base-change equations
  and the vertical, horizontal, and arbitrary base-change gamma equalities. The latter are
  equalities in the derived tower categories before evaluation, so no evaluation
  faithfulness hypothesis is present.

I checked edge cases: `n = 0` denotes level one; empty schemes and empty opens are admitted;
zero rings/modules make the projection and comparison maps zero where appropriate; identity
vertical and horizontal maps are covered by `gamma_identities`; infinite `B` is allowed while
finite origins use separate finite `Lambda_n`; and no characteristic restriction or universe
collapse is imposed. The clopen complement is explicit through `pi_components`, including an
empty complement.

Searches were repeated with `rg` over the project and upstream Lean sources for strict towers,
proper/open comparisons, clopen projections, and the item identifier, plus the required
semantic/Mathlib searches recorded by the worker. They found no exact existing declaration;
only generic mate, derived-category, scheme-module, and finite etale comparison APIs, all of
which are reused. I read the recorded dependency statements, including the repaired finite
open-base-change interface, and found each supplied notion matches its node. No new definition
node or dependency repair is needed, and no source-based statement correction is warranted.

No mismatch was found, so no Lean or node repair was made. The only change in this reading is
this report section.
